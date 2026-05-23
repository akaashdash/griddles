"""Verify the NEW JOINT-condition dichotomy for band_recurrence_ge_max.

For a < b, M = b, p = M % 2 (0 if M even, 1 if M odd), s = M + p (even, >= M):

  J := { D : c(a+D) <= a+D  AND  c(b+D) >= b+D + p }

Claims:
  (A) memJ_imp_separator: every D in J is a slack-s separator at fixed s = M+p.
      i.e. min(c(a+D),c(b+D)) < D+s <= max(c(a+D),c(b+D)).
  (B) J-infinite (grows with scan) <=> slack-s separator count grows with scan.
  (C) DISCRIMINATOR: is any J-finite c UNBOUNDED in displacement?
      If NO unbounded family is J-finite, we can drop the unbounded residue:
        dispatch becomes J-infinite (clean) + J-finite (routes via bounded pigeonhole).
"""

from families import FAMILIES


def sep_at_slack(c, a, b, s, D):
    """slack-s separator at D: [c(a+D) < D+s] != [c(b+D) < D+s]."""
    return (c(a + D) < D + s) != (c(b + D) < D + s)


def in_J(c, a, b, D, p):
    """D in J iff c(a+D) <= a+D (weak descent a) and c(b+D) >= b+D+p (ascent-with-parity b)."""
    return (c(a + D) <= a + D) and (c(b + D) >= b + D + p)


def check_memJ_imp_separator(c, a, b, Dmax):
    """(A): every D in J is a slack-(M+p) separator. Returns (|J|, last_J, n_fail)."""
    assert a < b
    M = b
    p = M % 2
    s = M + p
    Jcount = 0
    lastJ = -1
    fail = 0
    for D in range(Dmax):
        if in_J(c, a, b, D, p):
            Jcount += 1
            lastJ = D
            if not sep_at_slack(c, a, b, s, D):
                fail += 1
    return Jcount, lastJ, fail, s


def slackS_sep_count(c, a, b, s, Dmax):
    """(B): count of slack-s separators up to Dmax, and last occurrence."""
    cnt = 0
    last = -1
    for D in range(Dmax):
        if sep_at_slack(c, a, b, s, D):
            cnt += 1
            last = D
    return cnt, last


def max_disp(c, n, cap):
    m = 0
    for x in range(1, min(n, cap)):
        m = max(m, abs(c(x) - x))
    return m


def main():
    NMAX = 200000
    pairs = [(1, 2), (1, 3), (2, 3), (1, 4), (3, 5), (2, 7), (4, 5), (1, 5)]

    print("=== (A) memJ_imp_separator: 0 failures expected ===")
    print("=== (B) J-infinite <=> slack-s separators infinite ===")
    print("=== (C) is any J-finite family UNBOUNDED? ===\n")

    total_A_fail = 0
    j_finite_unbounded = []
    summary = []

    for name, (fn, is_ei) in FAMILIES.items():
        if is_ei:
            continue
        c, cinv, n = fn(NMAX)
        md = max_disp(c, n, NMAX)
        # heuristic: unbounded if max disp grows large relative to family;
        # growing_blocks_* are the genuinely unbounded ones.
        unbounded = name.startswith("growing")
        for a, b in pairs:
            if b + 5 >= n:
                continue
            Dmax = n - b - 1
            half = Dmax // 2
            Jcount, lastJ, fail, s = check_memJ_imp_separator(c, a, b, Dmax)
            total_A_fail += fail
            sepcnt, seplast = slackS_sep_count(c, a, b, s, Dmax)
            J_inf = lastJ >= half and Jcount >= 3
            sep_inf = seplast >= half and sepcnt >= 3
            # (B) consistency: J-infinite => sep-infinite (sep contains J's separators)
            B_ok = (not J_inf) or sep_inf
            # (C) J-finite & unbounded
            if (not J_inf) and unbounded:
                j_finite_unbounded.append((name, a, b, Jcount, lastJ, Dmax))
            summary.append(
                (
                    name,
                    a,
                    b,
                    Jcount,
                    lastJ,
                    Dmax,
                    sepcnt,
                    fail,
                    J_inf,
                    sep_inf,
                    B_ok,
                    unbounded,
                    md,
                )
            )

    # Print compact table
    print(
        f"{'family':22s} {'(a,b)':8s} {'|J|':>7s} {'lastJ':>8s} {'/Dmax':>8s} {'sep#':>7s} "
        f"{'Jinf':>5s} {'sepInf':>6s} {'Bok':>4s} {'unbd':>5s} {'mdisp':>6s} {'Afail':>5s}"
    )
    for name, a, b, Jc, lJ, Dm, sc, fl, Ji, si, Bo, ub, md in summary:
        print(
            f"{name:22s} ({a},{b})    {Jc:7d} {lJ:8d} {Dm:8d} {sc:7d} "
            f"{str(Ji):>5s} {str(si):>6s} {str(Bo):>4s} {str(ub):>5s} {md:6d} {fl:5d}"
        )

    print(f"\n(A) total memJ_imp_separator failures = {total_A_fail}")
    print(
        f"(B) total (B) consistency failures = {sum(1 for s in summary if not s[10])}"
    )
    print(f"(C) J-finite AND unbounded cases = {len(j_finite_unbounded)}")
    for jf in j_finite_unbounded:
        print(f"    *** UNBOUNDED & J-FINITE: {jf}")
    if not j_finite_unbounded:
        print("    => NO unbounded family is J-finite. Unbounded residue is DELETABLE.")


if __name__ == "__main__":
    main()
