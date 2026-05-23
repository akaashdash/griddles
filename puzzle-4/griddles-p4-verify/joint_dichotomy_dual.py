"""Verify the SYMMETRIC joint condition J'' for band_recurrence_ge_max (GOAL 1)
and the comonotone+bounded structure of the both-finite residue (GOAL 2 setup).

For a < b, M = b.val:
  ORIGINAL  J   := { D : c(a+D) <= a+D          AND  c(b+D) >= b+D + (M%2) }
                   (a weak-descends, b ascends-with-parity)  slack s  = M + M%2 (even, >= M)

  SYMMETRIC J'' := { D : c(a+D) >= a+D + q       AND  c(b+D) <= b+D }
                   (a ascends-with-offset q, b weak-descends)
      slack s' = leastEvenGe(M+1)  (= M+1 if M odd, M+2 if M even)  (even, >= M)
      q = s' - a.val  (so a + q = s' exactly, q >= 1 since s' > a)

Claims to verify:
  (A')  memJ''_imp_separator: every D in J'' is a slack-s' separator at fixed even s'.
        i.e. min(c(a+D),c(b+D)) < D+s' <= max(c(a+D),c(b+D)).
  (B')  J''-infinite => slack-s' separators infinite.
  (C')  BOTH J and J'' finite  =>  phi(a+D)=c(a+D)-(a+D) and phi(b+D)=c(b+D)-(b+D)
        are eventually COMONOTONE (same strict sign) AND bounded.
"""

from families import FAMILIES


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


def sep_at_slack(c, a, b, s, D):
    return (c(a + D) < D + s) != (c(b + D) < D + s)


def in_J(c, a, b, D, p):
    return (c(a + D) <= a + D) and (c(b + D) >= b + D + p)


def in_Jdd(c, a, b, D, q):
    # a ascends-with-offset q ; b weak-descends
    return (c(a + D) >= a + D + q) and (c(b + D) <= b + D)


def main():
    NMAX = 200000
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
        (1, 6),
        (5, 6),
    ]

    total_Add_fail = 0
    total_A_fail = 0
    both_finite_noncomono = []
    both_finite_unbounded = []
    qvals = set()
    checks = 0

    print(
        f"{'family':22s} {'(a,b)':8s} {'M':>3s} {'s':>4s} {'q':>3s} {'sprime':>6s} "
        f"{'|J|':>6s} {'|Jdd|':>6s} {'A_f':>3s} {'Add_f':>5s} {'bothFin':>7s} {'comono':>6s} {'mdisp':>5s}"
    )

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
            s = M + p
            sprime = leastEvenGe(M + 1)
            q = sprime - a
            assert q >= 1, (a, b, sprime, q)
            assert a + q == sprime
            qvals.add((M % 2, a % 2, q))

            Jcount = 0
            Jlast = -1
            Jddcount = 0
            Jddlast = -1
            A_fail = 0
            Add_fail = 0
            # comonotone / boundedness tracking on the TAIL (D in [half, Dmax))
            signs = set()
            maxabs = 0
            for D in range(Dmax):
                pa = c(a + D) - (a + D)
                pb = c(b + D) - (b + D)
                checks += 1
                if in_J(c, a, b, D, p):
                    Jcount += 1
                    Jlast = D
                    if not sep_at_slack(c, a, b, s, D):
                        A_fail += 1
                if in_Jdd(c, a, b, D, q):
                    Jddcount += 1
                    Jddlast = D
                    if not sep_at_slack(c, a, b, sprime, D):
                        Add_fail += 1
                if D >= half:
                    maxabs = max(maxabs, abs(pa), abs(pb))
                    # record comonotone signedness when both nonzero
                    if pa != 0 and pb != 0:
                        signs.add((pa > 0, pb > 0))
            total_A_fail += A_fail
            total_Add_fail += Add_fail

            J_inf = Jlast >= half and Jcount >= 3
            Jdd_inf = Jddlast >= half and Jddcount >= 3
            both_finite = (not J_inf) and (not Jdd_inf)
            # POINTWISE comonotone on tail: NO opposite-sign pair (each both-nonzero D has same sign).
            opp = sum(1 for sp in signs if sp in {(True, False), (False, True)})
            comono = opp == 0
            mdisp = maxabs

            if both_finite:
                if not comono:
                    both_finite_noncomono.append((name, a, b, signs))
                # boundedness: with bounded prefix scan, just record mdisp; "unbounded" families flagged
                if name.startswith("growing"):
                    both_finite_unbounded.append((name, a, b, mdisp))

            print(
                f"{name:22s} ({a},{b})    {M:3d} {s:4d} {q:3d} {sprime:6d} "
                f"{Jcount:6d} {Jddcount:6d} {A_fail:3d} {Add_fail:5d} {str(both_finite):>7s} {str(comono):>6s} {mdisp:5d}"
            )

    print(f"\ntotal checks ~ {checks}")
    print(f"(A) original memJ_imp_separator failures = {total_A_fail}")
    print(f"(A') symmetric memJ''_imp_separator failures = {total_Add_fail}")
    print(
        f"(C') both-finite cases that are NON-comonotone = {len(both_finite_noncomono)}"
    )
    for x in both_finite_noncomono:
        print(f"    *** NON-COMONOTONE both-finite: {x}")
    print(
        f"(C') both-finite cases that are UNBOUNDED (growing*) = {len(both_finite_unbounded)}"
    )
    for x in both_finite_unbounded:
        print(f"    *** UNBOUNDED both-finite: {x}")
    print(
        f"\nq values seen as (M%2, a%2, q): not printed individually; distinct count = {len(qvals)}"
    )
    print("  q = sprime - a always >= 1 and a+q == sprime (asserted): OK")


if __name__ == "__main__":
    main()
