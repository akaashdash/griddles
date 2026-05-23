"""Discriminator test (advisor step 1): is the value-hogging "uniformization" lead
alive or dead?

The lead: "for large D the active s-range is controlled" -- i.e. the active window
  W(D) := (min(c(a+D),c(b+D)) - D,  max(c(a+D),c(b+D)) - D]
is bounded, so finitely many even slacks cover it; per-slack agreement (HYP) would
then compose to full Indistinguishable-style agreement at all active thresholds.

A slack-s separator at D exists IFF (s in the window): s in W(D), i.e.
  min(c(a+D),c(b+D)) - D  <  s  <=  max(c(a+D),c(b+D)) - D.
(This is `separatorAtSlack_iff_window` in Lean, with threshold t = D+s.)

So HYP at slack s says: for all large D, s NOT in W(D).

KILL TEST for the lead: on parity_shift pair (2,4), at large D compute W(D) and the
even slacks in it. If for EVERY even s in [max, max+bound] there is a TAIL of D with
s not in W(D) (HYP holds) EXCEPT the ONE recurring slack -- and that one recurring
slack is in W(D) at unbounded D -- then the "uniformize over active s" cannot
manufacture full agreement, because the recurring slack is genuinely active forever.
The lead is dead iff: the active window CONTAINS a fixed even slack at unbounded D
(so it never empties of even slacks) AND that fixed slack is the lone non-EI bit.
"""

import families

FAM = families.FAMILIES


def window(c, a, b, D):
    x = c(a + D)
    y = c(b + D)
    lo = min(x, y) - D
    hi = max(x, y) - D
    return lo, hi  # open at lo, closed at hi: s in (lo, hi]


def sep_at_slack(c, a, b, s, D):
    return (c(a + D) < D + s) != (c(b + D) < D + s)


def even_slacks_in_window(lo, hi):
    out = []
    s = lo + 1
    while s <= hi:
        if s % 2 == 0:
            out.append(s)
        s += 1
    return out


def run(name, a, b, NMAX=60000):
    c, cinv, N = FAM[name][0](NMAX)
    mx = max(a, b)
    print(f"\n=== {name} pair ({a},{b}), max={mx} ===")
    # Tail of large D: tabulate window and even slacks in it.
    samples = []
    for D in range(N - 40, N - 8):
        if a + D >= N or b + D >= N:
            break
        lo, hi = window(c, a, b, D)
        es = [s for s in even_slacks_in_window(lo, hi) if s >= mx]
        samples.append((D, lo, hi, es))
    for D, lo, hi, es in samples[:8]:
        print(f"  D={D}: window=({lo},{hi}]  even slacks>=max in window: {es}")
    # Which even slacks >= max are in the window at UNBOUNDED D (recurring)?
    from collections import Counter

    cnt = Counter()
    Dlo, Dhi = N - 3000, N - 8
    for D in range(Dlo, Dhi):
        if a + D >= N or b + D >= N:
            break
        lo, hi = window(c, a, b, D)
        for s in even_slacks_in_window(lo, hi):
            if s >= mx:
                cnt[s] += 1
    print(f"  recurring even slacks>=max in high window {Dlo}..{Dhi}: {dict(cnt)}")
    # Crux check: is there a FIXED even slack >= max that is active (in window) at
    # unbounded D?  If yes -> the active window never empties of that slack -> the
    # "uniformize over active s and compose to Indistinguishable" lead cannot fire
    # (HYP at THAT slack fails, by construction, so you never had agreement there).
    recurring = [s for s, k in cnt.items() if k > 5]
    print(f"  => fixed even slack(s) active at unbounded D: {recurring}")
    return recurring


def main():
    # The wall witness:
    run("parity_shift", 2, 4)
    # And a few others to triangulate:
    run("growing_blocks_rev", 2, 4)
    run("swap_at_powers", 1, 4, NMAX=300000)
    run("block_cycle_5", 2, 4)


if __name__ == "__main__":
    main()
