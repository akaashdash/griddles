import sys

import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from families import FAMILIES

# At weak descents of a (g_a(D)=c(a+D)-(a+D) <= 0), examine:
#  - g_b(D)
#  - window endpoints: lo = a+g_a(D) (= c(a+D)-D) <= a,  hi via b+g_b(D) = c(b+D)-D
#    window W_D = (min(lo,hi), max(lo,hi)] of slacks; sep at slack s iff s in W_D.
#  - smallest even s >= b in W_D (if any).
# Test advisor's claim: along weak-descent subseq of a, is g_b bounded? is there always
#   some even s>=b in the window (or recurring)?


def probe(fname, a, b, NMAX=400000, Dmax=300000, verbose_n=8):
    builder, isEI = FAMILIES[fname]
    c, cinv, n = builder(NMAX)
    Nlim = n
    Dlim = min(Dmax, Nlim - b - 1)
    wd = []  # weak descent D's
    gb_at_wd = []
    has_even_s = 0
    no_even_s = 0
    even_s_values = {}  # smallest even s>=b in window -> count
    examples = []
    for D in range(Dlim):
        ga = c(a + D) - (a + D)
        if ga > 0:
            continue
        # weak descent of a
        wd.append(D)
        gbv = c(b + D) - (b + D)
        gb_at_wd.append(gbv)
        lo = c(a + D) - D
        hi = c(b + D) - D
        L = min(lo, hi)
        R = max(lo, hi)
        # window (L, R].  even s>=b in (L,R]: smallest even integer > L that is >= b and <= R
        start = max(L + 1, b)
        # smallest even >= start
        if start % 2 != 0:
            start += 1
        if start <= R:
            has_even_s += 1
            even_s_values[start] = even_s_values.get(start, 0) + 1
            if len(examples) < verbose_n:
                examples.append((D, ga, gbv, L, R, start))
        else:
            no_even_s += 1
            if len(examples) < verbose_n:
                examples.append((D, ga, gbv, L, R, None))
    res = {
        "n_wd": len(wd),
        "gb_min": min(gb_at_wd) if gb_at_wd else None,
        "gb_max": max(gb_at_wd) if gb_at_wd else None,
        "has_even_s": has_even_s,
        "no_even_s": no_even_s,
        "even_s_hist": dict(sorted(even_s_values.items())),
        "examples": examples,
    }
    return res


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
            r = probe(fname, a, b)
            print(
                f"{fname:22s} ({a},{b}): n_wd={r['n_wd']:7d} gb@wd in [{r['gb_min']},{r['gb_max']}] "
                f"has_even_s={r['has_even_s']:7d} no_even_s={r['no_even_s']:6d}"
            )
            print(
                f"      even_s_hist (smallest even s>=b in window -> count): {r['even_s_hist']}"
            )
        print()
