"""Direct debug of swap_at_powers separators - find the sparse recurring separating value."""

from families import FAMILIES

NMAX = 300000
c, cinv, n = FAMILIES["swap_at_powers"][0](NMAX)

for a, b in [(2, 3), (1, 3), (1, 5)]:
    M = b
    print(f"\n=== swap_at_powers a={a} b={b} M={M} ===")
    # find ALL D where a separator at SOME even s>=M exists, and record (phi pair, window, s)
    seps = []  # (D, phi_pair, window, s)
    Dlim = n - b - 1
    for D in range(Dlim):
        ca, cb = c(a + D), c(b + D)
        lo, hi = min(ca, cb) - D, max(ca, cb) - D
        # smallest even s>=M in (lo,hi]
        start = max(lo + 1, M)
        if start % 2:
            start += 1
        if start <= hi:
            pa, pb = ca - (a + D), cb - (b + D)
            seps.append((D, (pa, pb), (lo, hi), start))
    print(f"  total separating D up to {Dlim}: {len(seps)}")
    if seps:
        print(f"  first 6: {seps[:6]}")
        print(f"  last 3:  {seps[-3:]}")
        # which phi-pairs appear among separators, and their last occurrence
        from collections import Counter

        pc = Counter(p for (_, p, _, _) in seps)
        last = {}
        for D, p, w, s in seps:
            last[p] = (D, w, s)
        print(f"  separating phi-pairs: {dict(pc)}")
        print(f"  their last occurrence: {last}")
    else:
        print("  NO separators at even s>=M found! (would be a real counterexample)")
