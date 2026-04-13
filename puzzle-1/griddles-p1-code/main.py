"""
Chromatic Rotations Verifier
Tests all claims for the 101×101 grid problem on small grids (n = 2 … 11).

Parallelisation strategy
  Each valid first-row configuration (3·2^(n-1) of them) becomes one job.
  Jobs are distributed across all CPU cores via multiprocessing.Pool.
  Each worker runs independent iterative backtracking from its prefix.

Memory strategy
  n ≤ 7  (≤ 12 288 colorings) — COLLECT mode:
      workers return all proper colorings; full set/orbit verification follows.
  n ≥ 8  (≥ 49 152 colorings) — STREAM mode:
      workers return only aggregated counts; no large list ever lives in memory.

All output is written to both stdout and verification_output.log.
"""

import itertools
import multiprocessing as mp
import os
import sys
from pathlib import Path
from tqdm import tqdm

NUM_WORKERS = os.cpu_count()   # 8 on M1 Pro
COLLECT_MAX_N = 7              # use collect mode for n ≤ this value


# ── output tee ───────────────────────────────────────────────────────────────


class _Tee:
    def __init__(self, *streams):
        self._streams = streams

    def write(self, text):
        for st in self._streams:
            st.write(text)

    def flush(self):
        for st in self._streams:
            st.flush()

    def __getattr__(self, name):
        return getattr(self._streams[0], name)


# ── helpers (module-level so workers can import them) ────────────────────────


def is_proper(g, n):
    """Check adjacency and every-2×2-has-all-3-colors constraints."""
    for r in range(n):
        for c in range(n):
            v = g[r * n + c]
            if c + 1 < n and v == g[r * n + c + 1]:
                return False
            if r + 1 < n and v == g[(r + 1) * n + c]:
                return False
    for r in range(n - 1):
        for c in range(n - 1):
            sq = {
                g[r * n + c],
                g[r * n + c + 1],
                g[(r + 1) * n + c],
                g[(r + 1) * n + c + 1],
            }
            if len(sq) < 3:
                return False
    return True


def rotate90(g, n):
    """90° clockwise: (r, c) → (c, n-1-r)."""
    out = [0] * (n * n)
    for r in range(n):
        for c in range(n):
            out[c * n + (n - 1 - r)] = g[r * n + c]
    return tuple(out)


def is_separable(g, n):
    """Check g(r,c) = base + R[c] + D[r]  (mod 3)."""
    base = g[0]
    R = [(g[c] - base) % 3 for c in range(n)]
    D = [(g[r * n] - base) % 3 for r in range(n)]
    for r in range(n):
        for c in range(n):
            if g[r * n + c] != (base + R[c] + D[r]) % 3:
                return False
    return True


def generate_separable(n):
    """Enumerate all separable colorings directly."""
    out = []
    for base in range(3):
        for hs in itertools.product((1, 2), repeat=n - 1):
            R = [0] * n
            for c in range(1, n):
                R[c] = (R[c - 1] + hs[c - 1]) % 3
            for vs in itertools.product((1, 2), repeat=n - 1):
                D = [0] * n
                for r in range(1, n):
                    D[r] = (D[r - 1] + vs[r - 1]) % 3
                g = tuple(
                    (base + R[c] + D[r]) % 3
                    for r in range(n)
                    for c in range(n)
                )
                out.append(g)
    return out


def burnside_groups(proper, n):
    """Count orbits via Burnside's lemma (uses a seen-set; only for small n)."""
    fix = [0, 0, 0, 0]
    seen = set()
    groups = 0
    for g in proper:
        fix[0] += 1
        g1 = rotate90(g, n)
        g2 = rotate90(g1, n)
        g3 = rotate90(g2, n)
        if g == g1:
            fix[1] += 1
        if g == g2:
            fix[2] += 1
        if g == g3:
            fix[3] += 1
        if g not in seen:
            groups += 1
            seen |= {g, g1, g2, g3}
    assert (sum(fix) // 4) == groups, "Burnside count mismatch!"
    return groups, fix


# ── formula for odd n ─────────────────────────────────────────────────────────


def formula_groups_odd(n):
    k = n - 1
    return (3 * (2 ** (2 * k) + 2 ** (k // 2 + 1) + 2**k)) // 4


def formula_fix_odd(n):
    k = n - 1
    fe    = 3 * 2 ** (2 * k)
    fr90  = 3 * 2 ** (k // 2)
    fr180 = 3 * 2**k
    return fe, fr90, fr180, fr90   # fix_r270 == fix_r90


# ── parallel worker (module-level for pickling) ───────────────────────────────


def _worker(args):
    """
    Iterative backtracking from a fixed first-row prefix.

    collect_mode=True  → return list of proper colorings (small n only)
    collect_mode=False → return (total, sep_ok, fix_r90, fix_r180, fix_r270)
    """
    prefix, n, collect_mode = args
    nn      = n * n
    grid    = list(prefix) + [0] * (nn - len(prefix))
    start   = len(prefix)
    nv      = [0] * (nn + 1)   # next color to try at each position

    proper = [] if collect_mode else None
    total = sep = fix_r90 = fix_r180 = fix_r270 = 0

    pos = start
    while pos >= start:
        if pos == nn:
            # ── leaf: record or aggregate ────────────────────────────────────
            if collect_mode:
                proper.append(tuple(grid))
            else:
                g = tuple(grid)
                total += 1
                if is_separable(g, n):
                    sep += 1
                r1 = rotate90(g, n)
                if g == r1:
                    fix_r90 += 1
                r2 = rotate90(r1, n)
                if g == r2:
                    fix_r180 += 1
                if g == rotate90(r2, n):
                    fix_r270 += 1
            pos -= 1

        else:
            # ── interior node: try next valid color ──────────────────────────
            r, c = divmod(pos, n)
            v     = nv[pos]
            found = False
            while v < 3:
                ok = True
                if c > 0 and v == grid[pos - 1]:
                    ok = False
                if ok and r > 0 and v == grid[pos - n]:
                    ok = False
                if ok and r > 0 and c > 0:
                    sq = {
                        grid[(r - 1) * n + (c - 1)],
                        grid[(r - 1) * n + c],
                        grid[r * n + (c - 1)],
                        v,
                    }
                    if len(sq) < 3:
                        ok = False
                if ok:
                    found = True
                    break
                v += 1

            if found:
                grid[pos]     = v
                nv[pos]       = v + 1   # resume here from v+1 on backtrack
                nv[pos + 1]   = 0       # fresh start for next position
                pos += 1
            else:
                nv[pos] = 0             # reset for future visits
                pos -= 1

    if collect_mode:
        return proper
    return total, sep, fix_r90, fix_r180, fix_r270


# ── job generation ────────────────────────────────────────────────────────────


def _first_row_jobs(n, collect_mode):
    """
    Generate one job per valid first-row prefix.
    A valid first row has no two horizontally adjacent cells equal.
    Count: 3 · 2^(n-1).
    """
    jobs = []
    stack = [(v,) for v in range(3)]
    while stack:
        row = stack.pop()
        if len(row) == n:
            jobs.append((row, n, collect_mode))
        else:
            last = row[-1]
            for v in range(3):
                if v != last:
                    stack.append(row + (v,))
    return jobs


# ── parallel dispatcher ───────────────────────────────────────────────────────


def run_parallel(n, collect_mode):
    jobs = _first_row_jobs(n, collect_mode)
    mode_label = "collect" if collect_mode else "stream"
    desc = f"  parallel ({NUM_WORKERS} cores, {mode_label})"

    with mp.Pool(processes=NUM_WORKERS) as pool:
        chunks = list(
            tqdm(
                pool.imap_unordered(_worker, jobs),
                total=len(jobs),
                desc=desc,
                leave=False,
            )
        )

    if collect_mode:
        return [g for chunk in chunks for g in chunk]
    else:
        total = sep = r90 = r180 = r270 = 0
        for t, s, a, b, c in chunks:
            total += t
            sep   += s
            r90   += a
            r180  += b
            r270  += c
        return total, sep, r90, r180, r270


# ── main ─────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    log_path  = Path(__file__).parent / "verification_output.log"
    _log_file = open(log_path, "w", buffering=1)
    sys.stdout = _Tee(sys.__stdout__, _log_file)

    print("=" * 65)
    print("CHROMATIC ROTATIONS — verification  n = 2 … 11")
    print(f"  Workers : {NUM_WORKERS}   Log : {log_path.name}")
    print("=" * 65)

    for n in range(2, 12):
        print(f"\n{'─' * 65}")
        print(f"  n = {n}   ({n}×{n} grid, {3 ** (n*n):,} candidates)")
        print(f"{'─' * 65}")

        collect = (n <= COLLECT_MAX_N)

        # ── 1. Find all proper colorings ──────────────────────────────────────
        if n <= 3:
            # Flat sequential enumeration (tiny search space)
            proper = []
            for g in tqdm(
                itertools.product(range(3), repeat=n * n),
                total=3 ** (n * n),
                desc="  sequential",
                leave=False,
            ):
                if is_proper(g, n):
                    proper.append(g)
            num_proper = len(proper)
            non_sep    = [g for g in proper if not is_separable(g, n)]
            sep_ok     = not non_sep
            sep_label  = "✓  ALL separable" if sep_ok else f"✗  {len(non_sep)} not separable"
        elif collect:
            # Parallel backtracking → collect all colorings
            proper     = run_parallel(n, collect_mode=True)
            num_proper = len(proper)
            non_sep    = [g for g in proper if not is_separable(g, n)]
            sep_ok     = not non_sep
            sep_label  = "✓  ALL separable" if sep_ok else f"✗  {len(non_sep)} not separable"
        else:
            # Parallel backtracking → stream counts (large n, no big list)
            num_proper, sep_count, fix_r90, fix_r180, fix_r270 = run_parallel(
                n, collect_mode=False
            )
            sep_ok    = (sep_count == num_proper)
            sep_label = (
                "✓  ALL separable (streamed)"
                if sep_ok
                else f"✗  {num_proper - sep_count} NOT separable"
            )
            proper = None  # not stored

        formula_total = 3 * 2 ** (2 * (n - 1))
        count_ok      = "✓" if num_proper == formula_total else "✗"
        print(
            f"  Proper colorings : {num_proper:>10,}  "
            f"(formula 3·2^{2*(n-1)} = {formula_total:,})  {count_ok}"
        )
        print(f"  Separability     : {sep_label}")

        # ── 2. Separable generation comparison ────────────────────────────────
        if n <= 3 or collect:
            sep_set   = set(generate_separable(n))
            gen_match = "✓  sets equal" if sep_set == set(proper) else "✗  sets DIFFER"
            print(f"  Separable gen    : {gen_match}  ({len(sep_set):,} generated)")
        else:
            # For large n, generating 3·2^(2(n-1)) full tuples is expensive;
            # count equality follows from: all found are separable + counts match.
            gen_count = formula_total   # 3·2^(2(n-1))
            gen_match = "✓  count matches" if gen_count == num_proper else "✗  count mismatch"
            print(
                f"  Separable gen    : {gen_match}  "
                f"({gen_count:,}, set equality inferred)"
            )

        # ── 3. Burnside rotation groups ───────────────────────────────────────
        if n <= 3 or collect:
            groups, fix = burnside_groups(proper, n)
            print(
                f"  Fix(e,90,180,270): {fix}  "
                f"→  {sum(fix):,} / 4 = {groups:,} groups"
            )
        else:
            fix       = [num_proper, fix_r90, fix_r180, fix_r270]
            groups    = sum(fix) // 4
            groups_ok = (sum(fix) % 4 == 0)
            print(
                f"  Fix(e,90,180,270): {fix}  "
                f"→  {sum(fix):,} / 4 = {groups:,} groups"
                + ("" if groups_ok else "  ✗ NOT DIVISIBLE BY 4")
            )

        # ── 4. Formula check (odd n only) ─────────────────────────────────────
        if n % 2 == 1:
            fe, fr90, fr180, fr270 = formula_fix_odd(n)
            f_groups  = formula_groups_odd(n)
            fix_ok    = fix == [fe, fr90, fr180, fr270]
            grp_ok    = groups == f_groups
            print(
                f"  Formula fixes    : [{fe}, {fr90}, {fr180}, {fr270}]  "
                f"{'✓' if fix_ok else '✗'}"
            )
            print(
                f"  Formula groups   : {f_groups:,}  {'✓' if grp_ok else '✗'}"
            )
        else:
            print(
                f"  (n={n} even — no closed-form formula; brute-force is ground truth)"
            )

    # ── Extrapolation to n = 101 ──────────────────────────────────────────────
    print(f"\n{'=' * 65}")
    print("  EXTRAPOLATION TO n = 101")
    print(f"{'=' * 65}")
    print("  Fix(e)    = 3 · 2^200")
    print("  Fix(r90)  = Fix(r270) = 3 · 2^50")
    print("  Fix(r180) = 3 · 2^100")
    print()
    print("  Groups = (3·2^200 + 3·2^50 + 3·2^100 + 3·2^50) / 4")
    print("         = (3/4)(2^200 + 2^100 + 2·2^50)")
    print("         = (3/4)(2^200 + 2^100 + 2^51)")
    print("         = 3(2^198 + 2^98 + 2^49)")
    val = 3 * (2**198 + 2**98 + 2**49)
    print(f"\n  Numerical value  : {val}")
    print("  Compact form     : 3(2^198 + 2^98 + 2^49)")

    _log_file.close()
    sys.stdout = sys.__stdout__
    print(f"\n[Log saved → {log_path}]")
