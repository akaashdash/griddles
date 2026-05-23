"""Does S(N)/N -> 0 for the flagged families? (decisive for the density angle)

swap_at_powers: separators only at D = 2^k - b  => S(N) ~ log2(N), so S(N)/N -> 0.
growing_blocks_rev: block sizes grow; check if density is stable or decays with N.

Also: even allowing ALL even slacks >= M (not just the 2-element window), does
swap_at_powers have positive density? (It must not, if separators are log-sparse in D.)
"""

import families

FAM = families.FAMILIES


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


def slack_sep(c, a, b, s, D):
    return (c(a + D) < D + s) != (c(b + D) < D + s)


def count_seps_2window(c, n, a, b, Nwindow):
    M = max(a, b)
    s0 = leastEvenGe(M)
    cnt = 0
    valid = 0
    for D in range(Nwindow):
        if b + D + s0 + 2 >= n:
            break
        valid += 1
        if slack_sep(c, a, b, s0, D) or slack_sep(c, a, b, s0 + 2, D):
            cnt += 1
    return cnt, valid


def count_seps_allslack(c, n, a, b, Nwindow):
    """Count D with a separator at ANY even slack >= M (the full hno scope)."""
    M = max(a, b)
    cnt = 0
    valid = 0
    for D in range(Nwindow):
        # max meaningful slack: max(c(a+D),c(b+D)) - D
        hi = max(c(a + D), c(b + D)) - D
        if b + D >= n or hi < 0:
            break
        valid += 1
        found = False
        s = leastEvenGe(M)
        while s <= hi + 2:
            if slack_sep(c, a, b, s, D):
                found = True
                break
            s += 2
        if found:
            cnt += 1
    return cnt, valid


def main():
    print("=== swap_at_powers: S(N) growth (2-window AND all-slack) ===")
    mk, _ = FAM["swap_at_powers"]
    a, b = 2, 3
    for NMAX in [2000, 8000, 32000, 128000, 500000]:
        c, cinv, n = mk(NMAX)
        cnt2, v2 = count_seps_2window(c, n, a, b, NMAX)
        cntA, vA = count_seps_allslack(c, n, a, b, NMAX)
        print(
            f"  N~{v2:<8} 2win S={cnt2:<5} dens={cnt2 / max(v2, 1):.6f} | "
            f"allslack S={cntA:<5} dens={cntA / max(vA, 1):.6f}"
        )
    # show WHERE the separators are
    c, cinv, n = mk(500000)
    locs = [
        D
        for D in range(min(n - b - 10, 400000))
        if slack_sep(c, a, b, leastEvenGe(b), D)
        or slack_sep(c, a, b, leastEvenGe(b) + 2, D)
    ]
    print(f"  swap_at_powers (2,3) separator D-locations (2-window): {locs[:25]}")
    print("    (these are 2^k - b = 2^k - 3 : log-sparse => density -> 0)")

    print("\n=== growing_blocks_rev: density stability with N ===")
    mk, _ = FAM["growing_blocks_rev"]
    for a, b in [(1, 2), (3, 4)]:
        print(f"  pair ({a},{b}):")
        for NMAX in [4000, 16000, 64000, 256000, 800000]:
            c, cinv, n = mk(NMAX)
            cnt2, v2 = count_seps_2window(c, n, a, b, NMAX)
            cntA, vA = count_seps_allslack(c, n, a, b, NMAX)
            print(
                f"    N~{v2:<8} 2win dens={cnt2 / max(v2, 1):.6f} | "
                f"allslack dens={cntA / max(vA, 1):.6f}"
            )


if __name__ == "__main__":
    main()
