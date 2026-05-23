"""REFUTATION test: try to BREAK "S infinite" / "S finite => EI".

The honest question (advisor): is there a clean contradiction from S finite?

Reframe using the GAP=2-VARIANT that is symmetric and uses the engine cofinitely_bad_impossible.

Actually let's reconsider the WHOLE reduction. We need:
  "S infinite" where S = {D : c(b+D) > b+D AND |c(a+D)-c(b+D)| >= 2}.

A MUCH cleaner sufficient set might be available. Let me search for the SIMPLEST
infinite subset of the separating set, robust to log-sparsity.

OBSERVATION from data: for swap_at_powers, EVERY strict ascent of b has gap>=2.
For block_cycle, MANY strict ascents have gap=1 (when a,b in same block residue).

Let me test alternative cleaner sufficient sets T_i and whether each is infinite for
ALL bounded non-EI families. We want a set that:
  (i) is provably contained in the separating set (=> some even s>=M separator), AND
  (ii) is provably infinite for bounded non-EI c.

Candidates:
  T1 = {D : c(b+D) > b+D AND c(a+D) <= a+D}   (strict asc at b, weak desc at a)
       -- window lo = min-D, with c(a+D)-D <= a < b+1 <= hi; gap = ca-cb...
  T2 = {D : c(b+D) >= D+M AND c(a+D) < D+M}  (b-signal above threshold, a-signal below)
       = direct slack-M separator with s=M when M even! (this IS separatorAtSlack at s=M)
  T3 = {D : c(b+D) > b+D AND c(a+D) < b+D}  (b strict asc, a-value below b+D)

For each candidate, check: (a) is it subset of separating-set for some even s in [M,M+B]?
(b) is it infinite on all bounded non-EI families?
"""

from families import FAMILIES


def make_c(fam_fn, NMAX):
    return fam_fn(NMAX)


def even_in_window_ge_M(lo, hi, M):
    for s in (hi, hi - 1):
        if s % 2 == 0 and s > lo and s >= M:
            return s
    return None


def candidate_sets(c, a, b, D):
    """Return dict candidate-> (in_set, separating_witness_s_or_None)."""
    M = b  # a<b so max=b
    ca = c(a + D)
    cb = c(b + D)
    lo = min(ca, cb) - D
    hi = max(ca, cb) - D
    out = {}
    # T1: strict asc b, weak desc a
    t1 = (cb > b + D) and (ca <= a + D)
    out["T1_ascb_desca"] = t1
    # T2: direct slack-M separator: exactly one of ca,cb < D+M
    t2 = (ca < D + b) != (cb < D + b)
    out["T2_slackM_sep"] = t2
    # T3: strict asc b, a-value strictly below b+D
    t3 = (cb > b + D) and (ca < b + D)
    out["T3"] = t3
    # original S
    s_orig = (cb > b + D) and (abs(ca - cb) >= 2)
    out["S_orig"] = s_orig
    # for each in-set, can we find even s in (lo,hi], s>=M?
    sw = even_in_window_ge_M(lo, hi, M)
    return out, sw, lo, hi, M


def analyze(c, a, b, n):
    Dmax = n - b - 1
    counts = {}
    last = {}
    contain_fail = {}
    for D in range(Dmax):
        out, sw, lo, hi, M = candidate_sets(c, a, b, D)
        for k, v in out.items():
            if v:
                counts[k] = counts.get(k, 0) + 1
                last[k] = D
                # containment: this D should be a separator for SOME even s>=M
                # (sw is even s in (lo,hi]; need sw>=M too)
                ok = (sw is not None) and (sw >= M)
                if not ok:
                    contain_fail[k] = contain_fail.get(k, 0) + 1
    return counts, last, contain_fail, Dmax


def main():
    NMAX = 50000
    pairs = [(1, 2), (2, 3), (1, 3), (1, 4), (3, 5), (2, 7)]
    keys = ["T1_ascb_desca", "T2_slackM_sep", "T3", "S_orig"]
    # track: for each candidate, the MIN count across all (family,pair) (to find which never empties)
    min_count = {k: 10**9 for k in keys}
    total_contain_fail = {k: 0 for k in keys}
    empties = {k: [] for k in keys}
    for name, (fn, is_ei) in FAMILIES.items():
        if is_ei or name.startswith("growing"):
            continue
        for a, b in pairs:
            c, cinv, n = make_c(fn, NMAX)
            counts, last, cf, Dmax = analyze(c, a, b, n)
            for k in keys:
                cnt = counts.get(k, 0)
                min_count[k] = min(min_count[k], cnt)
                total_contain_fail[k] += cf.get(k, 0)
                if cnt == 0:
                    empties[k].append((name, a, b))
    print(
        "candidate          min|set| across all (fam,pair)   containment-fails   #empty"
    )
    for k in keys:
        print(
            f"  {k:18s} min={min_count[k]:8d}            cf={total_contain_fail[k]:6d}    empty={len(empties[k])}"
        )
        if empties[k]:
            print(f"      empties: {empties[k][:8]}")


if __name__ == "__main__":
    main()
