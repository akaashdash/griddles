"""Verify the CLEANER reduction for the bounded-displacement band recurrence.

S := { D : c(b+D) > b+D  AND  |c(a+D) - c(b+D)| >= 2 }

Claims to verify on bounded non-EI families:
  (1) S is infinite (every D in S is a slack-s separator for some even s >= M=b).
  (2) The "interval-even arithmetic" lemma: a half-open interval (lo, hi] with
      hi >= M+1 and hi - lo >= 2 contains an even number >= M, indeed in (lo,hi].
  (3) S finite => EI (the contrapositive contradiction we must reproduce in Lean),
      decomposed into delta=1 and delta>=2 sub-cases.
"""

from families import FAMILIES


def make_c(fam_fn, NMAX):
    return fam_fn(NMAX)


def disp(c, n):
    return c(n) - n


def in_S(c, a, b, D):
    """D in S iff c(b+D) > b+D and |c(a+D) - c(b+D)| >= 2."""
    cb = c(b + D)
    ca = c(a + D)
    return (cb > b + D) and (abs(ca - cb) >= 2)


def separating_slacks_at_D(c, a, b, D):
    """The set of slacks s (integers) such that a slack-s separator holds at D.
    A slack-s separator at D: [c(a+D) < D+s] != [c(b+D) < D+s].
    Equivalently D+s in (min(ca,cb), max(ca,cb)], i.e. s in (min-D, max-D].
    Returns the open-low/closed-high window (lo, hi] in slack coords (lo,hi exclusive/inclusive)."""
    ca = c(a + D)
    cb = c(b + D)
    lo = min(ca, cb) - D  # exclusive
    hi = max(ca, cb) - D  # inclusive
    return lo, hi


def even_in_window_ge_M(lo, hi, M):
    """Return an even integer s in (lo, hi] with s >= M, if one exists; else None.
    The KEY arithmetic lemma asserts: if hi >= M+1 and hi-lo >= 2, one exists."""
    # candidates: hi or hi-1, whichever even; must be > lo and >= M.
    for s in (hi, hi - 1):
        if s % 2 == 0 and s > lo and s >= M:
            return s
    return None


def verify_key_arithmetic():
    """Exhaustively check: hi>=M+1 and hi-lo>=2 => exists even s in (lo,hi], s>=M."""
    fails = 0
    for M in range(0, 40):
        for hi in range(M + 1, M + 60):
            for lo in range(-5, hi - 1):  # hi - lo >= 2
                if hi - lo < 2:
                    continue
                s = even_in_window_ge_M(lo, hi, M)
                if s is None:
                    fails += 1
                    if fails <= 5:
                        print(f"  ARITH FAIL M={M} lo={lo} hi={hi}")
    print(f"key arithmetic lemma: {fails} failures")
    return fails == 0


def s_infinite_check(fam_name, fam_fn, NMAX, pairs):
    """For each pair (a,b) with a<b, count |S| up to NMAX displacement, and check
    every D in S yields an even separator s with M=b <= s (i.e. the containment)."""
    results = []
    for a, b in pairs:
        c, cinv, n = make_c(fam_fn, NMAX)
        Dmax = n - b - 1
        if Dmax < 10:
            continue
        S_count = 0
        last_D = -1
        containment_ok = True
        for D in range(0, Dmax):
            if in_S(c, a, b, D):
                S_count += 1
                last_D = D
                lo, hi = separating_slacks_at_D(c, a, b, D)
                # M = b (since a<b, max(a,b)=b)
                M = b
                # hi = max(ca,cb)-D; cb>b+D => cb-D>b => hi>=cb-D>=b+1 => hi>=M+1
                # gap>=2 => hi-lo>=2
                s = even_in_window_ge_M(lo, hi, M)
                if s is None or s < M or not (lo < s <= hi):
                    containment_ok = False
        results.append((a, b, S_count, last_D, Dmax, containment_ok))
    return results


def is_EI_prefix(c, n, tail=200):
    """Heuristic: is c identity on the top `tail` of [1,n]?"""
    return all(c(x) == x for x in range(max(1, n - tail), n + 1))


def main():
    print("=== KEY ARITHMETIC LEMMA ===")
    verify_key_arithmetic()

    print("\n=== S INFINITE on bounded non-EI families ===")
    NMAX = 60000
    pairs = [(1, 2), (1, 3), (2, 3), (1, 4), (3, 5), (2, 7)]
    bounded_fams = []
    for name, (fn, is_ei) in FAMILIES.items():
        if is_ei:
            continue
        # restrict to bounded-displacement families
        if name.startswith("growing"):
            continue  # unbounded
        bounded_fams.append((name, fn))

    grand_fail = 0
    for name, fn in bounded_fams:
        res = s_infinite_check(name, fn, NMAX, pairs)
        for a, b, cnt, lastD, Dmax, cok in res:
            tag = "OK" if cok else "CONTAIN-FAIL"
            sparse = " (SPARSE)" if 0 < cnt < 50 else ""
            if not cok:
                grand_fail += 1
            # flag S empty (would break "S infinite")
            empty = " *** S EMPTY ***" if cnt == 0 else ""
            print(
                f"  {name:22s} (a={a},b={b}): |S|={cnt:6d} lastD={lastD:6d}/{Dmax} {tag}{sparse}{empty}"
            )
    print(f"\ncontainment failures: {grand_fail}")


if __name__ == "__main__":
    main()
