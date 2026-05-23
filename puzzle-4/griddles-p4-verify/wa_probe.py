import sys

import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from families import FAMILIES

# At WEAK ASCENTS of b (g_b(D)=c(b+D)-(b+D) >= 0), examine:
#  - g_a(D) range
#  - window (min(lo,hi), max(lo,hi)] where lo=c(a+D)-D, hi=c(b+D)-D
#  - smallest even s>=b in window
# Test: is g_a bounded along this subseq? does an even s>=b always (or recurringly) appear?


def probe(fname, a, b, NMAX=400000, Dmax=300000):
    builder, isEI = FAMILIES[fname]
    c, cinv, n = builder(NMAX)
    Nlim = n
    Dlim = min(Dmax, Nlim - b - 1)
    n_wa = 0
    ga_min = 10**9
    ga_max = -(10**9)
    has = 0
    no = 0
    hist = {}
    for D in range(Dlim):
        gb = c(b + D) - (b + D)
        if gb < 0:
            continue
        n_wa += 1
        ga = c(a + D) - (a + D)
        ga_min = min(ga_min, ga)
        ga_max = max(ga_max, ga)
        lo = c(a + D) - D
        hi = c(b + D) - D
        L = min(lo, hi)
        R = max(lo, hi)
        start = max(L + 1, b)
        if start % 2:
            start += 1
        if start <= R:
            has += 1
            hist[start] = hist.get(start, 0) + 1
        else:
            no += 1
    return n_wa, ga_min, ga_max, has, no, dict(sorted(hist.items()))


if __name__ == "__main__":
    pairs = [(1, 2), (2, 3), (1, 3), (2, 4), (1, 4), (3, 5)]
    fams = [
        "parity_shift",
        "adjacent_involution",
        "growing_blocks_rev",
        "growing_blocks_cyc",
        "block_cycle_5",
        "rev_block_5",
        "swap_at_powers",
        "random_per_6_0",
        "random_per_6_4",
    ]
    for fname in fams:
        for a, b in pairs:
            n_wa, gmin, gmax, has, no, hist = probe(fname, a, b)
            print(
                f"{fname:22s} ({a},{b}): n_wa={n_wa:7d} ga@wa in [{gmin},{gmax}] has_s={has:7d} no_s={no:6d} hist={hist}"
            )
        print()
