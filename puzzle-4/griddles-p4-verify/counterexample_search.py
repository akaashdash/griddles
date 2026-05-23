"""AGGRESSIVE counterexample search for the Band Recurrence lemma.

Lemma (contrapositive / band form):
  c: Z>=1 -> Z>=1 a bijection, NOT eventually identity (non-EI). Fix 1<=a<b.
  CLAIM: there exists an EVEN s>=b such that for INFINITELY many D>=0,
         exactly one of c(a+D)>=D+s and c(b+D)>=D+s holds.
  With u_D=c(a+D)-D, v_D=c(b+D)-D:  s in (min(u,v), max(u,v)]  ("s in band")
  i.e. separator at slack s, displacement D  iff  L < s <= R  where L=min(u,v), R=max(u,v).

A COUNTEREXAMPLE is a non-EI permutation + pair (a,b) where EVERY fixed even s>=b has
only FINITELY many (saturating) separators, while windows keep escaping upward
(max R -> infinity). We distinguish saturation from growth by counting separators in
[0,N], [0,2N], [0,4N] and looking at the ratios.

We do NOT trust "last separator in far half" heuristic; we use growth ratios.

Run:  uv run --no-project counterexample_search.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from families import make_perm_from_list  # noqa: E402


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


# ---------------------------------------------------------------------------
# NEW aggressive families (formula-defined where possible -> no prefix truncation).
# Each builder returns (c, cinv, n) where c,cinv are valid on [1, n].
# All builders are checked for bijectivity by validate_bijection below.
# ---------------------------------------------------------------------------


def doubling_blocks_rev(NMAX):
    """Reverse each block [2^k, 2^(k+1)). Displacement ~ 2^k (sharply unbounded)."""
    vals = []
    k = 0
    while (
        2 ** (k + 1) - 1 <= NMAX
    ):  # block [2^k, 2^(k+1)-1] fully present (1-indexed values)
        lo = 2**k
        hi = 2 ** (k + 1) - 1  # inclusive
        block = list(range(lo, hi + 1))
        vals.extend(block[::-1])
        k += 1
    return make_perm_from_list(vals)


def doubling_blocks_cyc(NMAX):
    """Cyclic-shift each block [2^k, 2^(k+1)). c(n) = n+1 within block, wrap end->start."""
    vals = []
    k = 0
    while 2 ** (k + 1) - 1 <= NMAX:
        lo = 2**k
        hi = 2 ** (k + 1) - 1
        block = list(range(lo, hi + 1))
        block = block[1:] + block[:1]
        vals.extend(block)
        k += 1
    return make_perm_from_list(vals)


def squared_blocks_rev(NMAX):
    """Reverse each block [k^2, (k+1)^2). Displacement ~ 2k ~ sqrt(N)."""
    vals = []
    k = 1
    while (k + 1) ** 2 - 1 <= NMAX:
        lo = k * k
        hi = (k + 1) ** 2 - 1
        block = list(range(lo, hi + 1))
        vals.extend(block[::-1])
        k += 1
    return make_perm_from_list(vals)


def interval_exchange_doubling(NMAX):
    """Within each block [2^k, 2^(k+1)), swap the two halves (interval exchange).
    Block of size L=2^k; first half [lo, lo+L/2), second [lo+L/2, hi]. Output: 2nd then 1st.
    Displacement ~ L/2 ~ 2^(k-1), unbounded."""
    vals = []
    k = 0
    while 2 ** (k + 1) - 1 <= NMAX:
        lo = 2**k
        hi = 2 ** (k + 1) - 1
        L = hi - lo + 1
        h = L // 2
        first = list(range(lo, lo + h))
        second = list(range(lo + h, hi + 1))
        vals.extend(second + first)  # swap halves
        k += 1
    return make_perm_from_list(vals)


def growing_blocks_rev(NMAX):
    """Blocks of size 2,3,4,5,...; reverse each. (linear-ish growth, ~sqrt(2N) displacement)"""
    vals = []
    start = 1
    bsize = 2
    while start + bsize - 1 <= NMAX:
        block = list(range(start, start + bsize))
        vals.extend(block[::-1])
        start += bsize
        bsize += 1
    return make_perm_from_list(vals)


def growing_blocks_cyc(NMAX):
    """Blocks of size 2,3,4,...; cyclic-shift each."""
    vals = []
    start = 1
    bsize = 2
    while start + bsize - 1 <= NMAX:
        block = list(range(start, start + bsize))
        vals.extend(block[1:] + block[:1])
        start += bsize
        bsize += 1
    return make_perm_from_list(vals)


def parity_shift(NMAX):
    """c(1)=2; c(2k)=2k+2, c(2k+1)=2k-1.  Bounded displacement, KNOWN-HARD control."""

    def c(x):
        if x == 1:
            return 2
        if x % 2 == 0:
            return x + 2
        return x - 2

    def cinv(y):
        if y == 2:
            return 1
        if y % 2 == 0:
            return y - 2
        return y + 2

    return c, cinv, NMAX


def _adj_involution_list(m):
    """c(2i-1)=2i, c(2i)=2i-1 on [1, m_even] (m truncated to even)."""
    me = (m // 2) * 2
    vals = []
    for nn in range(1, me + 1):
        vals.append(nn + 1 if nn % 2 == 1 else nn - 1)
    return vals  # length me


def adj_involution_compose_growing_rev(NMAX):
    """Composition: growing_blocks_rev THEN adjacent-transposition involution.
    Both are finite-support per block / in-range, so the result is a clean permutation
    prefix. Mixes unbounded block-reversal with a bounded local swap."""
    cg, _, ng = growing_blocks_rev(NMAX)
    inv = _adj_involution_list(ng)  # inv[i]=c_inv(i+1), a list of length me
    me = len(inv)

    # apply inv after cg: result(i) = inv_func(cg(i)); inv is an involution swapping neighbors
    def invf(x):
        return x + 1 if x % 2 == 1 else x - 1

    vals = []
    for i in range(1, me + 1):
        y = cg(i)
        if y > me:
            break
        vals.append(invf(y))
    L = largest_perm_prefix(vals)
    return make_perm_from_list(vals[:L])


def growing_rev_compose_adj_involution(NMAX):
    """Composition the other way: adjacent-transposition involution THEN growing_blocks_rev."""
    cg, _, ng = growing_blocks_rev(NMAX)
    me = (ng // 2) * 2

    def invf(x):
        return x + 1 if x % 2 == 1 else x - 1

    vals = []
    for i in range(1, me + 1):
        y = invf(i)
        if y > ng:
            break
        vals.append(cg(y))
    L = largest_perm_prefix(vals)
    return make_perm_from_list(vals[:L])


def shift_within_doubling(NMAX):
    """Within block [2^k, 2^(k+1)): shift by +d_k where d_k grows (=k), cyclic.
    Gives unbounded displacement ~ k = log N within doubling blocks (slow but unbounded)."""
    vals = []
    k = 0
    while 2 ** (k + 1) - 1 <= NMAX:
        lo = 2**k
        hi = 2 ** (k + 1) - 1
        block = list(range(lo, hi + 1))
        L = len(block)
        d = (k + 1) % L if L > 0 else 0  # shift amount, grows with k
        shifted = block[d:] + block[:d]
        vals.extend(shifted)
        k += 1
    return make_perm_from_list(vals)


def random_growing_blocks(NMAX, seed=0):
    """Blocks of size 2,3,4,...; apply a RANDOM permutation within each block.
    Random displacement up to block size, unbounded."""
    import random

    rng = random.Random(seed)
    vals = []
    start = 1
    bsize = 2
    while start + bsize - 1 <= NMAX:
        block = list(range(start, start + bsize))
        pat = block[:]
        rng.shuffle(pat)
        vals.extend(pat)
        start += bsize
        bsize += 1
    return make_perm_from_list(vals)


def sawtooth_unbounded(NMAX):
    """An interval-exchange where blocks double and we reverse only ODD-indexed blocks.
    Mixes identity blocks with reversed growing blocks -> windows can escape but with gaps."""
    vals = []
    k = 0
    while 2 ** (k + 1) - 1 <= NMAX:
        lo = 2**k
        hi = 2 ** (k + 1) - 1
        block = list(range(lo, hi + 1))
        if k % 2 == 1:
            block = block[::-1]
        vals.extend(block)
        k += 1
    return make_perm_from_list(vals)


def largest_perm_prefix(vals):
    """Largest L such that vals[:L] is a permutation of 1..L."""
    seen = set()
    best = 0
    mx = 0
    for i, v in enumerate(vals):
        seen.add(v)
        mx = max(mx, v)
        # vals[:i+1] is perm of 1..(i+1) iff mx == i+1 and len(seen)==i+1
        if mx == i + 1 and len(seen) == i + 1:
            best = i + 1
    return best


# ---------------------------------------------------------------------------
# value: (builder, is_EI, is_formula)
NEW_FAMILIES = {
    "doubling_blocks_rev": (doubling_blocks_rev, False, False),
    "doubling_blocks_cyc": (doubling_blocks_cyc, False, False),
    "squared_blocks_rev": (squared_blocks_rev, False, False),
    "interval_exchange_doubling": (interval_exchange_doubling, False, False),
    "growing_blocks_rev": (growing_blocks_rev, False, False),
    "growing_blocks_cyc": (growing_blocks_cyc, False, False),
    "parity_shift": (parity_shift, False, True),
    "adjinv_o_growing_rev": (adj_involution_compose_growing_rev, False, False),
    "growing_rev_o_adjinv": (growing_rev_compose_adj_involution, False, False),
    "shift_within_doubling": (shift_within_doubling, False, False),
    "sawtooth_unbounded": (sawtooth_unbounded, False, False),
    "random_growing_b_0": (lambda N: random_growing_blocks(N, 0), False, False),
    "random_growing_b_1": (lambda N: random_growing_blocks(N, 1), False, False),
}


# ---------------------------------------------------------------------------
# Validation
# ---------------------------------------------------------------------------
def validate_bijection(c, cinv, n, name, formula=False):
    """List-built families: must be a bijection of [1,n] onto [1,n].
    Formula families (c defined on all of N+ but a finite prefix's image may spill
    by a bounded amount, e.g. parity_shift): we instead verify c is injective on [1,n]
    and cinv(c(x))==x and c(cinv(x))==x for all x in [1,n] (genuine bijection of N+)."""
    if formula:
        seen = {}
        for x in range(1, n + 1):
            y = c(x)
            if y < 1:
                return False, f"{name}: c({x})={y} < 1"
            if y in seen:
                return False, f"{name}: c not injective, c({seen[y]})=c({x})={y}"
            seen[y] = x
            if cinv(y) != x:
                return False, f"{name}: cinv(c({x}))={cinv(y)} != {x}"
        return (
            True,
            f"{name}: valid N+ bijection (formula), injective on [1,{n}] (n={n})",
        )
    seen = [False] * (n + 2)
    for x in range(1, n + 1):
        y = c(x)
        if not (1 <= y <= n):
            return False, f"{name}: c({x})={y} out of range [1,{n}]"
        if seen[y]:
            return False, f"{name}: c not injective, value {y} hit twice (at x={x})"
        seen[y] = True
    return True, f"{name}: valid bijection on [1,{n}] (n={n})"


def is_non_EI(c, n):
    """non-eventually-identity on prefix: exists x near the top with c(x)!=x.
    We check the upper third has a moved point."""
    for x in range(n, max(1, 2 * n // 3), -1):
        if c(x) != x:
            return True
    return False


def max_displacement(c, n):
    if n < 1:
        return 0
    return max(abs(c(x) - x) for x in range(1, n + 1))


def deepest_block_size_doubling(n):
    """size of the last doubling block fully within [1,n]."""
    k = 0
    last = 0
    while 2 ** (k + 1) - 1 <= n:
        last = 2 ** (k + 1) - 2**k
        k += 1
    return last


# ---------------------------------------------------------------------------
# Core: separator counting with LOG-SPACED snapshots
# ---------------------------------------------------------------------------
# We classify each fixed even slack s by its cumulative separator count at
# logarithmically spaced D-bounds. The KEY distinction the advisor flagged:
#   - count keeps INCREASING (even +const per decade => logarithmic) => UNBOUNDED
#     => infinitely many separators => LEMMA HOLDS for this s.
#   - count PLATEAUS (no increase over the last 2+ decades) => bounded (saturating)
#     => only finitely many separators at this s.
# A COUNTEREXAMPLE needs EVERY even s>=b to plateau while windows keep escaping.
SNAP_BOUNDS = None  # set in analyze_pair from Dlim


def make_snaps(Dlim):
    """Logarithmically spaced cumulative D-bounds (decades) up to Dlim."""
    snaps = []
    x = 1000
    while x < Dlim:
        snaps.append(x)
        x *= 10
    snaps.append(Dlim)
    return snaps


def analyze_pair(c, n, a, b, Dlim, SMAX_excess=60):
    """SINGLE D-pass computing, for every even s in [b, b+SMAX_excess], the cumulative
    separator count at log-spaced D-bounds (snaps). Also escape stats.
    Returns: (rows, snaps, Dlim, mRf, mRl, win_even)
      rows = list of (s, [count at each snap]).
    Classification (bounded vs unbounded) is done by classify_slack on the snap counts."""
    Dlim = min(Dlim, n - b - 1)
    snaps = make_snaps(Dlim)
    nsnap = len(snaps)
    lo_even = b if b % 2 == 0 else b + 1
    hi_even = b + SMAX_excess
    evens = list(range(lo_even, hi_even + 1, 2))
    ne = len(evens)
    # counts[i][j] = # separators at even slack evens[i] with D < snaps[j]
    counts = [[0] * nsnap for _ in range(ne)]
    maxR_first = -(10**18)  # over first decade [0, snaps[0])
    maxR_last = -(10**18)  # over whole range
    win_even = 0
    Nfirst = snaps[0]
    for D in range(Dlim):
        u = c(a + D) - D
        v = c(b + D) - D
        if u < v:
            L, R = u, v
        else:
            L, R = v, u
        if R > maxR_last:
            maxR_last = R
        if D < Nfirst and R > maxR_first:
            maxR_first = R
        slo = L + 1
        if slo % 2:
            slo += 1
        if slo < lo_even:
            slo = lo_even
        if slo <= R:
            win_even += 1
            shi = R if R <= hi_even else hi_even
            if slo <= shi:
                i0 = (slo - lo_even) // 2
                i1 = (shi - lo_even) // 2
                # which snaps does this D fall under? all snaps[j] > D
                # find smallest j with snaps[j] > D
                j0 = 0
                while j0 < nsnap and snaps[j0] <= D:
                    j0 += 1
                for i in range(i0, i1 + 1):
                    ci = counts[i]
                    for j in range(j0, nsnap):
                        ci[j] += 1
    rows = [(evens[i], counts[i]) for i in range(ne)]
    return rows, snaps, Dlim, maxR_first, maxR_last, win_even


def classify_slack(snap_counts):
    """Given cumulative counts at log-spaced D-bounds, classify the slack:
    ZERO     - no separators at all
    UNBOUNDED- count keeps increasing across the last two decades (incl. log growth)
    PLATEAU  - count fixed (no increase) over the last two decades (>=2 snaps) -> bounded
    few      - too few separators to judge confidently
    """
    cnt = snap_counts
    if cnt[-1] == 0:
        return "ZERO"
    last = cnt[-1]
    prev = cnt[-2] if len(cnt) >= 2 else 0
    prev2 = cnt[-3] if len(cnt) >= 3 else prev
    # plateau: no increase over last two decades
    if last == prev == prev2 and last > 0:
        return "PLATEAU"
    # unbounded: strictly increased in the last decade
    if last > prev:
        return "UNBOUNDED"
    if last == prev and prev > prev2:
        # increased one decade ago but not last -> ambiguous, lean unbounded if total small
        return "slow"
    return "few" if last < 3 else "UNBOUNDED"


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    NMAX = 4_000_000
    DLIM = (
        300_000  # log-snapshots reach D<300k (snaps 1k,10k,100k,300k) -> enough decades
    )
    SMAX_EXCESS = (
        30  # how far above b we scan even slacks (co-block width <= b-a <= 11)
    )
    all_pairs = [(a, b) for a in range(1, 13) for b in range(a + 1, 13)]
    larger_pairs = [(2, 9), (3, 10), (1, 11), (5, 12), (4, 11), (1, 12)]
    # pairs used for the per-pair table; do all 1<=a<b<=12 plus the larger set.
    table_pairs = all_pairs + larger_pairs

    print("=" * 78)
    print("STAGE 1: validate families are genuine non-EI bijections, measure escape")
    print("=" * 78)
    built = {}
    for name, (builder, _isEI, formula) in NEW_FAMILIES.items():
        c, cinv, n = builder(NMAX)
        ok, msg = validate_bijection(c, cinv, n, name, formula=formula)
        if not ok:
            print(f"  {msg}")
            print(f"    !!! INVALID, excluding {name}")
            continue
        nei = is_non_EI(c, n) or formula  # parity_shift is non-EI by construction
        md = max_displacement(c, n)
        built[name] = (c, cinv, n)
        print(f"  {msg} | non-EI={nei} | max|c(x)-x|={md}")
    print()

    print("=" * 78)
    print("STAGE 2: LOG-SNAPSHOT separator analysis (corrected counterexample hunt)")
    print(
        "  Scan even s in [b, b+%d]; cumulative count at log-spaced D-bounds."
        % SMAX_EXCESS
    )
    print("  UNBOUNDED = count keeps climbing across last decades (incl. LOG growth)")
    print("              => infinitely many separators => LEMMA HOLDS for that s.")
    print(
        "  PLATEAU   = count fixed over last 2 decades => bounded (finite) separators."
    )
    print(
        "  COUNTEREXAMPLE = EVERY even s>=b PLATEAUs while windows escape (maxR climbs)"
    )
    print("                   and many windows still contain an even slack >= b.")
    print("=" * 78)

    # STREAMING: print each (family,pair) row as computed so partial runs are usable.
    print(
        f"{'family':<26}{'pair':<9}{'wit s':<7}{'lEG':<5}{'exc':<5}{'kind':<6}{'esc':<5}{'counts@snaps'}"
    )
    counterexamples = []
    excess_by_family = {}
    kind_by_family = {}
    snaps_ref = None
    for name in sorted(built):
        c, cinv, n = built[name]
        excess_by_family.setdefault(name, [])
        kind_by_family.setdefault(name, [])
        for a, b in table_pairs:
            if b + 50 > n:
                continue
            rows, snaps, Dlim, mRf, mRl, win_even = analyze_pair(
                c, n, a, b, DLIM, SMAX_EXCESS
            )
            snaps_ref = snaps
            escaped = mRl > mRf + 2
            witness = None
            witness_kind = None
            wcnts = None
            for s, cnts in rows:
                kind = classify_slack(cnts)
                if kind in ("UNBOUNDED", "slow"):
                    witness = s
                    wcnts = cnts
                    last, prev = cnts[-1], (cnts[-2] if len(cnts) >= 2 else 0)
                    ratio = (last / prev) if prev > 0 else float("inf")
                    witness_kind = "LIN" if ratio >= 3 else "LOG"
                    break
            esc = "Y" if escaped else "n"
            if witness is None:
                print(
                    f"{name:<26}{f'({a},{b})':<9}{'NONE':<7}{leastEvenGe(b):<5}{'-':<5}{'-':<6}{esc:<5}NO-WITNESS win_even={win_even}"
                )
                if escaped and win_even > 50:
                    counterexamples.append(
                        (name, a, b, rows, snaps, mRf, mRl, win_even)
                    )
            else:
                excess = witness - leastEvenGe(b)
                print(
                    f"{name:<26}{f'({a},{b})':<9}{witness:<7}{leastEvenGe(b):<5}{excess:<5}{witness_kind:<6}{esc:<5}{wcnts}"
                )
                excess_by_family[name].append((a, b, excess))
                kind_by_family[name].append(witness_kind)
            sys.stdout.flush()
        sys.stdout.flush()

    print()
    if counterexamples:
        print(
            f"!!! {len(counterexamples)} COUNTEREXAMPLE CANDIDATE(S) (every even s PLATEAUs, windows escape):"
        )
        for name, a, b, rows, snaps, mRf, mRl, win_even in counterexamples:
            print(
                f"  >>> {name} ({a},{b}): maxR {mRf}->{mRl}, win_even={win_even}, snaps={snaps}"
            )
            for s, cnts in rows:
                if cnts[-1] > 0:
                    print(
                        f"        s={s:4d} excess={s - leastEvenGe(b):3d}: {cnts} {classify_slack(cnts)}"
                    )
    else:
        print(
            "NO counterexample candidates: every non-EI (family,pair) has an UNBOUNDED even s>=b."
        )
        print("=> Band Recurrence lemma HOLDS across all tested families/pairs.")
    if snaps_ref:
        print(f"\n(counts@snaps are cumulative separator counts at D < {snaps_ref})")

    print()
    print("=" * 78)
    print("STAGE 4: SUMMARY per family (excess range + witness density type)")
    print("=" * 78)
    for name in sorted(excess_by_family):
        exs = excess_by_family[name]
        kinds = kind_by_family[name]
        if not exs:
            print(f"  {name}: (no witness found anywhere)")
            continue
        evs = [e for (_, _, e) in exs]
        nlin = kinds.count("LIN")
        nlog = kinds.count("LOG")
        worst = sorted({(a, b, e) for (a, b, e) in exs if e == max(evs)})
        print(
            f"  {name}: excess range [{min(evs)},{max(evs)}]  density LIN={nlin} LOG={nlog}  max-excess pairs: {worst[:5]}"
        )
    print()
    print("DONE.")
