"""Check whether swap_at_powers really violates HYP (separators at unbounded D)
for the flagged pairs. Separators are log-sparse (D = 2^k - b roughly), so a
fixed-window 'last fail near Dmax' detector misses them. List ALL separating D
for each even slack up to a large NMAX and check the largest one scales with NMAX."""

import families

FAM = families.FAMILIES


def phi(c, n):
    return c(n) - n


def list_separators(c, a, b, s, Dmax, NM):
    e = s - b
    out = []
    for D in range(0, Dmax):
        if a + D >= NM or b + D >= NM:
            break
        if (phi(c, a + D) < e + (b - a)) != (phi(c, b + D) < e):
            out.append(D)
    return out


def main():
    print("=== swap_at_powers: are flagged pairs REAL lemma counterexamples? ===")
    for NMAX in [70000, 280000]:
        mk, _ = FAM["swap_at_powers"]
        c, cinv, NM = mk(NMAX)
        print(f"\n NMAX={NMAX}")
        for a, b in [(1, 3), (2, 3), (1, 5), (3, 5)]:
            mx = max(a, b)
            s0 = mx if mx % 2 == 0 else mx + 1
            for s in range(s0, s0 + 8, 2):
                seps = list_separators(c, a, b, s, NM, NM)
                if seps:
                    print(
                        f"  (a,b)=({a},{b}) s={s}: #seps={len(seps)} "
                        f"max_D={max(seps)} (last few: {seps[-4:]})"
                    )
                else:
                    print(f"  (a,b)=({a},{b}) s={s}: NO separators in [0,{NM})")


if __name__ == "__main__":
    main()
