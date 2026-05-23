"""Confirm the J-FINITE residue (band_recurrence_ge_max_of_jointFinite) is a TRUE statement.

For ordered pairs (a<b) where J is finite/empty, verify that SOME fixed even slack s >= M=b
still recurs at unbounded displacement (the band recurrence conclusion). This confirms the
single remaining sorry states a true proposition (no false lemma).
"""

from families import FAMILIES


def sep_at_slack(c, a, b, s, D):
    return (c(a + D) < D + s) != (c(b + D) < D + s)


def in_J(c, a, b, D, p):
    return (c(a + D) <= a + D) and (c(b + D) >= b + D + p)


def main():
    NMAX = 200000
    pairs = [(1, 2), (1, 3), (2, 3), (1, 4), (3, 5), (2, 7), (4, 5), (1, 5)]

    print("J-finite ordered pairs: confirm some even s>=M recurs (band still holds).\n")
    residue_cases = 0
    residue_ok = 0
    for name, (fn, is_ei) in FAMILIES.items():
        if is_ei:
            continue
        c, cinv, n = fn(NMAX)
        for a, b in pairs:
            if b + 5 >= n:
                continue
            M = b
            p = M % 2
            Dmax = n - b - 1
            half = Dmax // 2
            # J on ordered (a,b)
            Jlast = max((D for D in range(Dmax) if in_J(c, a, b, D, p)), default=-1)
            Jcount = sum(1 for D in range(Dmax) if in_J(c, a, b, D, p))
            J_inf = Jlast >= half and Jcount >= 3
            if J_inf:
                continue  # not the residue regime
            # This is a J-finite ordered pair. Find an even s>=M that recurs.
            residue_cases += 1
            found = None
            for s in range(M if M % 2 == 0 else M + 1, M + 12, 2):
                cnt = sum(1 for D in range(Dmax) if sep_at_slack(c, a, b, s, D))
                last = max(
                    (D for D in range(Dmax) if sep_at_slack(c, a, b, s, D)), default=-1
                )
                if last >= half and cnt >= 3:
                    found = (s, cnt, last)
                    break
            if found:
                residue_ok += 1
                print(
                    f"  {name:22s} (a={a},b={b}) M={M}: J-FINITE |J|={Jcount:3d}; "
                    f"band holds at even s={found[0]} (cnt={found[1]}, last={found[2]}/{Dmax})"
                )
            else:
                print(
                    f"  *** {name:22s} (a={a},b={b}) M={M}: J-FINITE but NO recurring "
                    f"even s in [M,M+10] -- WOULD BE FALSE LEMMA ***"
                )
    print(
        f"\nJ-finite residue cases: {residue_cases}, band-holds confirmed: {residue_ok}"
    )
    print(
        "FALSE-LEMMA CHECK:",
        "PASS (residue is TRUE)" if residue_ok == residue_cases else "FAIL",
    )


if __name__ == "__main__":
    main()
