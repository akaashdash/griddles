"""Understand WHY S is infinite for bounded non-EI c, by analyzing the S-finite case.

Suppose S finite. Then COFINITELY-many strict-ascent-b D (i.e. c(b+D) > b+D) have
gap = 1: c(a+D) = c(b+D) +- 1.

We want to derive EI (contradiction with non-EI).

Two sub-cases by delta = b - a:

  delta = 1 (b = a+1): along strict-ascent positions n = b+D = a+1+D,
      c(n-1) = c(n) +- 1  (cofinitely on strict-ascent-n).
      With bounded displacement, this should force EI.

  delta >= 2: along n = b+D, c(n-delta) = c(n) +- 1 (cofinitely strict-ascent-n).
      In bounded disp, phi(n-delta) - phi(n) = (c(n-delta)-c(n)) + delta in {delta-1, delta+1}
      both >= 1, so phi(n-delta) >= phi(n)+1. Chain forces phi unbounded => contradiction
      with bounded displacement.

This script empirically confirms:
  - For bounded non-EI c, there is NO D0 beyond which all strict-ascent-b have gap 1
    (i.e. S is genuinely infinite); equivalently the "gap=1 cofinitely on strict ascents"
    hypothesis already fails. We instead test the IMPLICATION directly:
    IF a perm has 'gap=1 on all strict-ascent-b for D >= D0' on a prefix, THEN it looks EI-like.
"""

from families import FAMILIES


def make_c(fam_fn, NMAX):
    return fam_fn(NMAX)


def analyze_strict_ascents_b(c, a, b, NMAX):
    """Among strict-ascent-b displacements (c(b+D) > b+D), how many have gap >= 2 (in S)
    vs gap == 1?  Return counts and the largest D with gap>=2."""
    Dmax = NMAX - b - 1
    asc = 0
    gap_ge2 = 0
    gap1 = 0
    last_gap2 = -1
    for D in range(Dmax):
        cb = c(b + D)
        if cb > b + D:
            asc += 1
            ca = c(a + D)
            if abs(ca - cb) >= 2:
                gap_ge2 += 1
                last_gap2 = D
            elif abs(ca - cb) == 1:
                gap1 += 1
    return asc, gap_ge2, gap1, last_gap2, Dmax


def phi(c, n):
    return c(n) - n


def delta1_mechanism(c, a, NMAX):
    """delta=1 sub-case: look at consecutive cells. On strict ascent of n=a+1+D,
    gap1 means c(n-1) = c(n) +- 1.  If this holds cofinitely, show bounded => EI.
    Empirically: how often does c(n-1) = c(n)-1 vs c(n)+1 on strict ascents? Bounded
    bijection with consecutive values on a tail must be eventually n->n+const => const=0 => EI."""
    b = a + 1
    Dmax = NMAX - b - 1
    plus = 0
    minus = 0
    for D in range(Dmax):
        cb = c(b + D)
        if cb > b + D:  # strict ascent at n=b+D
            ca = c(a + D)  # = c(n-1)
            if ca == cb - 1:
                minus += 1  # c(n-1) = c(n)-1  -> consecutive ascending
            elif ca == cb + 1:
                plus += 1
    return plus, minus, Dmax


def main():
    NMAX = 40000
    pairs = [(1, 2), (2, 3), (1, 3), (1, 4), (3, 5)]
    print("=== strict-ascent-b decomposition: gap>=2 (in S) vs gap==1 ===")
    for name, (fn, is_ei) in FAMILIES.items():
        if is_ei or name.startswith("growing"):
            continue
        for a, b in pairs:
            c, cinv, n = make_c(fn, NMAX)
            asc, g2, g1, lastD2, Dmax = analyze_strict_ascents_b(c, a, b, NMAX)
            # KEY: if S were finite, g1 would dominate cofinitely and g2 would stop.
            # We expect g2 to keep growing (lastD2 near Dmax) for non-sparse,
            # or genuinely recur (swap_at_powers) for sparse.
            sparse = " SPARSE" if 0 < g2 < 100 else ""
            print(
                f"  {name:20s}(a={a},b={b}): strict-asc={asc:6d} gap>=2(S)={g2:6d} "
                f"gap==1={g1:6d} lastD(S)={lastD2:6d}/{Dmax}{sparse}"
            )

    print("\n=== delta=1 mechanism: consecutive-value direction on strict ascents ===")
    print("(minus = c(n-1)=c(n)-1 ascending; plus = c(n-1)=c(n)+1)")
    for name, (fn, is_ei) in FAMILIES.items():
        if is_ei or name.startswith("growing"):
            continue
        for a in [1, 2, 3]:
            c, cinv, n = make_c(fn, NMAX)
            plus, minus, Dmax = delta1_mechanism(c, a, NMAX)
            print(f"  {name:20s}(a={a},b={a + 1}): plus={plus:6d} minus={minus:6d}")


if __name__ == "__main__":
    main()
