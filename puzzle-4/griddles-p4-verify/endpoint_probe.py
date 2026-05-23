import sys

import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from families import FAMILIES

# For each D, window endpoints (in slack units):
#   lo = c(a+D)-D, hi = c(b+D)-D  (NOT sorted; here we want signed roles)
#   L = min(lo,hi), R = max(lo,hi)
# A slack-s separator at D iff L < s <= R.
# Recurring slack s exists iff some fixed s is in (L,R] for infinitely many D.
# Check (3): does the UPPER endpoint R attain a fixed value v >= leastEvenGe(b) inf often?
#   More precisely, for fixed even s, count D with L < s <= R (true separator at slack s).
# We directly tabulate, for each even s in [b, b+SMAX], the count and max D.


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


def probe(fname, a, b, NMAX=800000, Dmax=600000, SMAX=20):
    builder, isEI = FAMILIES[fname]
    c, cinv, n = builder(NMAX)
    Nlim = n
    Dlim = min(Dmax, Nlim - b - 1)
    # for each even s in [b, b+SMAX], count separators and record last D (proxy unbounded)
    counts = {}
    lastD = {}
    evens = [s for s in range(b, b + SMAX + 1) if s % 2 == 0]
    for s in evens:
        counts[s] = 0
        lastD[s] = -1
    for D in range(Dlim):
        lo = c(a + D) - D
        hi = c(b + D) - D
        L = min(lo, hi)
        R = max(lo, hi)
        for s in evens:
            if L < s <= R:
                counts[s] += 1
                lastD[s] = D
    return Dlim, counts, lastD


if __name__ == "__main__":
    fams_pairs = [
        ("growing_blocks_rev", 2, 4),
        ("growing_blocks_rev", 1, 3),
        ("growing_blocks_rev", 3, 5),
        ("parity_shift", 2, 4),
        ("parity_shift", 3, 5),
        ("swap_at_powers", 2, 4),
        ("block_cycle_5", 1, 3),
        ("rev_block_5", 2, 4),
    ]
    for fname, a, b in fams_pairs:
        Dlim, counts, lastD = probe(fname, a, b)
        s0 = leastEvenGe(b)
        print(f"{fname} ({a},{b}) Dlim={Dlim} leastEvenGe(b)={s0}")
        for s in sorted(counts):
            recurs = lastD[s] > Dlim * 0.7
            print(
                f"    s={s:3d}: count={counts[s]:8d} lastD={lastD[s]:8d} recurs={recurs}"
            )
        print()
