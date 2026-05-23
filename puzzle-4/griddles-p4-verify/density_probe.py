"""DENSITY ANGLE probe.

Target: S(N) := #{D < N : exists even s in {leastEvenGe(M), leastEvenGe(M)+2}
                          with a slack-s separator at D}
where M = max(a,b).

A slack-s separator at D :  [c(a+D) < D+s] XOR [c(b+D) < D+s].

Question: is S(N)/N >= const > 0 for ALL non-EI families, INCLUDING b-odd pairs
and growing_blocks_rev (genuine no-identity-tail, unbounded displacement)?

If density is NOT bounded below for some family/pair -> the angle FAILS; report witness.
"""

import families

FAM = families.FAMILIES


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


def slack_sep(c, a, b, s, D):
    """[c(a+D) < D+s] XOR [c(b+D) < D+s]."""
    la = c(a + D) < D + s
    lb = c(b + D) < D + s
    return la != lb


def density_for_pair(mk, NMAX, a, b, Nwindow):
    c, cinv, n = mk(NMAX)
    M = max(a, b)
    s0 = leastEvenGe(M)
    slacks = [s0, s0 + 2]
    # only count D where both b+D and (with margin) are in range
    cnt = 0
    valid = 0
    per_slack = {s: 0 for s in slacks}
    for D in range(0, Nwindow):
        if b + D + s0 + 2 >= n:  # need c-values defined and threshold meaningful
            break
        valid += 1
        hit = False
        for s in slacks:
            if slack_sep(c, a, b, s, D):
                per_slack[s] += 1
                hit = True
        if hit:
            cnt += 1
    return cnt, valid, per_slack, s0


def main():
    pairs = [
        (1, 2),
        (2, 3),
        (1, 4),
        (2, 4),
        (3, 4),
        (2, 5),
        (3, 5),
        (4, 6),
        (5, 7),
        (1, 3),
        (4, 5),
        (5, 8),
        (3, 7),
    ]
    NMAX = 80000
    Nwindow = 8000

    print(
        f"{'family':<22}{'pair':<8}{'M':<3}{'s0':<4}{'S(N)/N':<10}{'per-slack densities'}"
    )
    print("-" * 90)
    worst = {}
    for fname, (mk, is_ei) in sorted(FAM.items()):
        if is_ei:
            continue
        for a, b in pairs:
            try:
                cnt, valid, per_slack, s0 = density_for_pair(mk, NMAX, a, b, Nwindow)
            except Exception:
                continue
            if valid < 100:
                continue
            dens = cnt / valid
            ps = {s: round(v / valid, 3) for s, v in per_slack.items()}
            worst.setdefault(fname, 1.0)
            worst[fname] = min(worst[fname], dens)
            if dens < 0.05:  # flag low-density cases
                print(
                    f"{fname:<22}{str((a, b)):<8}{max(a, b):<3}{s0:<4}{dens:<10.4f}{ps}  <-- LOW"
                )
    print("\n=== WORST (min over pairs) density per family ===")
    for fname in sorted(worst):
        flag = "  <-- BELOW 0.05" if worst[fname] < 0.05 else ""
        print(f"  {fname:<22} min density = {worst[fname]:.4f}{flag}")


if __name__ == "__main__":
    main()
