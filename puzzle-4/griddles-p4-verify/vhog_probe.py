"""Probe the value-hogging angle on noSeparator_allSlack_imp_eventuallyIdentity.

HYP (the open lemma's hypothesis): for every EVEN s >= max(a,b),
  eventually (all large D) NOT separatorAtSlack, i.e. [c(a+D)<D+s] <=> [c(b+D)<D+s].
GOAL: c eventually identity.

Key questions:
  Q1. Confirm HYP genuinely FAILS for non-EI families (some even s>=max has separators
      at unbounded D) -- i.e. the lemma's contrapositive `band_recurrence_ge_max` is the
      thing to prove.
  Q2. The WALL witness: parity_shift agrees at slack 4 (e=0 for pair (2,4)) forever yet
      is non-EI. Confirm and find which slack DOES separate (the recurring slack).
  Q3. Value-hogging diagnostic: the engine `cofinitely_bad_impossible` fires from
      "c(a+D) < D for ALL D >= T". Does HYP (single-slack agreement, all even s>=max)
      force some `c(a+D) < D+const` cofinitely? Or some translate that pigeonholes?
"""

import families

FAM = families.FAMILIES


def sep_at_slack(c, a, b, s, D):
    return (c(a + D) < D + s) != (c(b + D) < D + s)


def least_even_ge(m):
    return m if m % 2 == 0 else m + 1


def recurring_slacks(c, a, b, NMAX, Dwindow=(0, None), max_excess=20):
    """For each even s in [max, max+max_excess], does a separator recur at large D?
    Return list of (s, count_in_high_window) for s that separate in the high window.
    """
    mx = max(a, b)
    s0 = least_even_ge(mx)
    Dlo = NMAX - a - 3000
    Dhi = NMAX - a - 5
    out = []
    for s in range(s0, s0 + max_excess + 1, 2):
        cnt = 0
        last = -1
        for D in range(Dlo, Dhi):
            if a + D >= NMAX or b + D >= NMAX:
                break
            if sep_at_slack(c, a, b, s, D):
                cnt += 1
                last = D
        out.append((s, cnt, last))
    return s0, out


def main():
    NMAX = 60000
    pairs = [(1, 2), (1, 3), (2, 4), (1, 4), (3, 5), (2, 5), (5, 9)]
    print("=== Q1/Q2: recurring even slacks (in high-D window) per (family, pair) ===")
    print(
        "    For non-EI c, SOME even s>=max must recur (HYP fails). s0=leastEvenGe(max)."
    )
    any_fail = False
    for name, (mk, is_ei) in FAM.items():
        c, cinv, N = mk(NMAX)
        for a, b in pairs:
            if a >= b:
                continue
            s0, out = recurring_slacks(c, a, b, N)
            recurring = [(s, cnt, last) for (s, cnt, last) in out if cnt > 0]
            if not recurring and not is_ei:
                # zoom: maybe needs larger excess
                s0b, out2 = recurring_slacks(c, a, b, N, max_excess=60)
                recurring = [(s, cnt, last) for (s, cnt, last) in out2 if cnt > 0]
            tag = "EI" if is_ei else "nonEI"
            if not recurring:
                if not is_ei:
                    any_fail = True
                    print(
                        f"  !! {name:22s} {tag} (a,b)=({a},{b}) s0={s0}: NO recurring slack found"
                    )
            else:
                excesses = sorted({s - max(a, b) for (s, _, _) in recurring})
                # only print the interesting/non-trivial ones
                if name in (
                    "parity_shift",
                    "growing_blocks_rev",
                    "swap_at_powers",
                ) and (a, b) in ((2, 4), (1, 2), (1, 4)):
                    print(
                        f"  {name:22s} {tag} (a,b)=({a},{b}) s0={s0}: recurring s={[s for s, _, _ in recurring][:6]} excess(s-max)={excesses[:6]}"
                    )
    print(
        f"\n  Q1 verdict: any non-EI family with NO recurring slack? {any_fail}  (expect False)"
    )

    print("\n=== Q2 detail: parity_shift pair (2,4), which slack separates? ===")
    c, cinv, N = FAM["parity_shift"][0](NMAX)
    a, b = 2, 4
    for s in [4, 6, 8]:
        cnt = sum(1 for D in range(N - 2000, N - 10) if sep_at_slack(c, a, b, s, D))
        # also g-coords
        print(f"  s={s}: separators in high window = {cnt}")
    print("  g-coords at large D: phi(a+D)=c(a+D)-(a+D), phi(b+D)=c(b+D)-(b+D)")
    for D in [N - 100, N - 99, N - 98, N - 97]:
        pa = c(a + D) - (a + D)
        pb = c(b + D) - (b + D)
        print(f"    D={D} (a+D parity {(a + D) % 2}): phi(a+D)={pa} phi(b+D)={pb}")


if __name__ == "__main__":
    main()
