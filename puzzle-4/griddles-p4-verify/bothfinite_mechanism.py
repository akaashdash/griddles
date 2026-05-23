"""GOAL 2 investigation: in the BOTH-finite (bounded + pointwise-comonotone) residue,
what mechanism forces a fixed even slack s >= M to separate at unbounded D?

We focus on the both-finite cases and ask:
  - Does the smallest even slack >= M ( = leastEvenGe(M) ) recur as a separator?
  - What is the actual recurring separating slack? (range)
  - For the constant-fiber pigeonhole: enumerate the recurring values (x = phi(a+D), y = phi(b+D))
    on the tail.  band fails for fiber value (x,y) iff va=a+x, vb=b+y are CONSECUTIVE
    (|va - vb| = 1)  =>  no even threshold strictly between them => no even-slack separator there.
  - Claim under test: NOT every recurring comonotone fiber value is consecutive
    (so some recurring value gives an even-slack separator) -- i.e. band always holds.
  - Mechanism: which recurring (x,y) is NON-consecutive (gives the separator)?
"""

from collections import Counter

from families import FAMILIES


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


def in_J(c, a, b, D, p):
    return (c(a + D) <= a + D) and (c(b + D) >= b + D + p)


def in_Jdd(c, a, b, D, q):
    return (c(a + D) >= a + D + q) and (c(b + D) <= b + D)


def sep_at_slack(c, a, b, s, D):
    return (c(a + D) < D + s) != (c(b + D) < D + s)


def main():
    NMAX = 100000
    pairs = [
        (1, 2),
        (1, 3),
        (2, 3),
        (1, 4),
        (3, 5),
        (2, 7),
        (4, 5),
        (1, 5),
        (2, 4),
        (3, 4),
    ]

    print(
        f"{'family':22s} {'(a,b)':7s} {'M':>3s} {'lEGe(M)':>7s} {'sep@lEGe':>8s} "
        f"{'minSepSlk':>9s} {'#nonconsecVals':>14s} {'allConsec?':>10s}"
    )

    any_all_consecutive = []
    for name, (fn, is_ei) in FAMILIES.items():
        if is_ei:
            continue
        c, cinv, n = fn(NMAX)
        for a, b in pairs:
            if b + 5 >= n or a >= b:
                continue
            Dmax = n - b - 1
            half = Dmax // 2
            M = b
            p = M % 2
            sprime = leastEvenGe(M + 1)
            q = sprime - a
            # both-finite test on tail
            Jlast = max((D for D in range(Dmax) if in_J(c, a, b, D, p)), default=-1)
            Jddlast = max((D for D in range(Dmax) if in_Jdd(c, a, b, D, q)), default=-1)
            both_finite = Jlast < half and Jddlast < half
            if not both_finite:
                continue

            lge = leastEvenGe(M)
            # does the smallest even slack >= M recur on the tail?
            seplge = sum(1 for D in range(half, Dmax) if sep_at_slack(c, a, b, lge, D))
            # tail fiber values (x,y) = (phi(a+D), phi(b+D)); record consecutiveness of (a+x, b+y)
            fiber = Counter()
            for D in range(half, Dmax):
                x = c(a + D) - (a + D)
                y = c(b + D) - (b + D)
                fiber[(x, y)] += 1
            # recurring values: count above a threshold (appear "infinitely")
            thr = max(3, (Dmax - half) // 200)
            recurring = {(x, y): cnt for (x, y), cnt in fiber.items() if cnt >= thr}

            # consecutive: |va - vb| = 1 where va = a + x, vb = b + y
            def consec(xy):
                x, y = xy
                va = a + x
                vb = b + y
                return abs(va - vb) == 1

            nonconsec = [xy for xy in recurring if not consec(xy)]
            all_consec = len(nonconsec) == 0
            # min recurring separating even slack >= M
            min_sep_slack = None
            for xy, cnt in sorted(recurring.items()):
                x, y = xy
                va = a + x
                vb = b + y
                lo, hi = min(va, vb), max(va, vb)
                # an even slack s>=M separates this fiber-value iff lo < s <= hi (window),
                # equivalently there's an even s with lo - 0 < s <= hi after shifting by D... but on
                # constant fiber the separator slack is s with lo < D+s <= hi? Actually window is
                # (lo - D ... ) wait values c are va+D? No: c(a+D)=a+D+x=va+D, c(b+D)=vb+D.
                # window: min(va+D,vb+D) < D+s <= max => min(va,vb) < s <= max(va,vb).
                # so even s in (lo, hi] separates. smallest even s>=M in that interval:
                cand = None
                s = leastEvenGe(M)
                while s <= hi + 2:
                    if lo < s <= hi and s >= M:
                        cand = s
                        break
                    s += 2
                if cand is not None and (min_sep_slack is None or cand < min_sep_slack):
                    min_sep_slack = cand
            if all_consec:
                any_all_consecutive.append((name, a, b, list(recurring.keys())))
            print(
                f"{name:22s} ({a},{b})  {M:3d} {lge:7d} {seplge:8d} "
                f"{str(min_sep_slack):>9s} {len(nonconsec):14d} {str(all_consec):>10s}"
            )

    print(
        f"\n# both-finite cases where ALL recurring values are consecutive (band would fail): "
        f"{len(any_all_consecutive)}"
    )
    for x in any_all_consecutive:
        print("   ***", x)
    if not any_all_consecutive:
        print(
            "  => every both-finite case has a NON-consecutive recurring value => band holds."
        )


if __name__ == "__main__":
    main()
