import random
import sys

import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


def recurs(c, a, b, s, Dlim, Nlim, tail=0.6):
    last = -1
    cnt = 0
    for D in range(Dlim):
        if b + D > Nlim:
            break
        if (c(a + D) < D + s) != (c(b + D) < D + s):
            last = D
            cnt += 1
    return cnt > 0 and last > Dlim * tail, cnt, last


def which_recurs(c, a, b, Dlim, Nlim, smax=20):
    out = []
    s0 = leastEvenGe(b)
    for s in range(b, b + smax + 1):
        if s % 2:
            continue
        r, cnt, last = recurs(c, a, b, s, Dlim, Nlim)
        if r:
            out.append(s)
    return out, s0


def random_bijection(NMAX, seed, blocksize_max=12):
    # build a genuine non-EI bijection by random blocks of varying size, each a random non-id perm
    rng = random.Random(seed)
    vals = []
    start = 1
    while start <= NMAX:
        B = rng.randint(2, blocksize_max)
        block = list(range(start, start + B))
        perm = block[:]
        rng.shuffle(perm)
        if perm == block:
            perm = perm[1:] + perm[:1]
        vals.extend(perm)
        start += B
    vals = vals[: (len(vals))]
    # ensure permutation prefix: truncate to a block boundary already satisfied
    cmap = {i + 1: vals[i] for i in range(len(vals))}
    # truncate to largest M with image set {1..M}: blocks are self-contained so any block end works
    inv = {v: k for k, v in cmap.items()}
    M = len(vals)

    def c(x):
        return cmap[x]

    def cinv(y):
        return inv[y]

    return c, cinv, M


if __name__ == "__main__":
    NMAX = 120000
    Dlim = 80000
    print(
        "=== Recurring slacks: is it always in {leastEvenGe(b), +2}? (random bijections) ==="
    )
    excess_hist = {}
    fails = 0
    total = 0
    for seed in range(40):
        c, cinv, M = random_bijection(NMAX, seed)
        Nlim = M
        for a, b in [
            (1, 2),
            (2, 3),
            (1, 3),
            (2, 4),
            (1, 4),
            (3, 5),
            (2, 5),
            (4, 6),
            (5, 7),
            (3, 7),
        ]:
            if b + 200 > Nlim:
                continue
            total += 1
            recs, s0 = which_recurs(c, a, b, Dlim, Nlim)
            if not recs:
                fails += 1
                print(f"  NO RECURRING SLACK seed={seed} ({a},{b})")
                continue
            smin = min(recs)
            ex = smin - s0
            excess_hist[ex] = excess_hist.get(ex, 0) + 1
    print(f"total={total} no-recurring-slack-fails={fails}")
    print(
        f"min-recurring-slack EXCESS over leastEvenGe(b) histogram: {dict(sorted(excess_hist.items()))}"
    )
