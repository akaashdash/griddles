"""Find the rigorous proof that 'window contains an even s>=M' recurs at unbounded D.

This is the recurrence hypothesis I feed to the (>=M) pigeonhole.  I need a bijectivity
reason it holds infinitely often, NOT just empirics.

Window at D: (lo_D, hi_D] with lo_D=min(c(a+D),c(b+D))-D, hi_D=max(...)-D.
'separates at even s>=M' at D  <=>  exists even s in (lo_D,hi_D] with s>=M
                              <=>  leastEvenGe(max(lo_D+1,M)) <= hi_D.

CANDIDATE BIJECTIVITY ARGUMENT (test each piece):
  We have TWO engines on the b-ray:
    descents:  inf many D with c(b+D)<=b+D    (vb<=b => lo_D could be small via b? no, lo is min)
    ascents:   inf many D with c(b+D)>=b+D    (vb>=b => hi_D>=b=M)
  And on a-ray likewise.

  The cleanest: I claim separators_unbounded ALREADY gives a separator at SOME even slack at
  unbounded D; the slack is in the window so <= hi_D <= b+B.  Combined with the slack being
  >=? ... NOT necessarily >=M.

  KEY TEST: Is it true that at unbounded D, the window contains an even s with M<=s<=b+B?
  Decompose: separators_unbounded gives a separator (even slack, in window).  At a D where
  the MINIMAL even slack in the window is < M, can we always find ANOTHER D (cofinally) where
  it's >=M?  Test the direct claim that the >=M-separator recurs, and ALSO test whether the
  combination [separator exists] AND [hi_D>=M] at the SAME D forces a >=M even separator.
"""

from families import FAMILIES

BOUNDED = [
    "block_cycle_2",
    "block_cycle_3",
    "rev_block_5",
    "adjacent_involution",
    "parity_shift",
    "swap_at_powers",
    "random_per_4_0",
    "random_per_6_2",
]


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


def disp_bound(c, n, upto):
    return max(abs(c(x) - x) for x in range(1, min(n, upto)))


# TEST CLAIM 1: at unbounded D, window contains even s>=M.
# TEST CLAIM 2 (the would-be CLEAN proof): if hi_D >= M AND lo_D < M, then window contains
#    an even s in [M, hi_D]?  i.e. leastEvenGe(M) <= hi_D.   Need hi_D >= leastEvenGe(M).
# TEST CLAIM 3: combine: infinitely many D have hi_D >= leastEvenGe(M)  (ascent-driven)
#    AND lo_D < leastEvenGe(M).   Then even s=leastEvenGe(M) in (lo_D,hi_D] => separator!
#    => the FIXED slack s* = leastEvenGe(M) ... but parity-shift needs M+2.  So claim 3 with
#    s*=leastEvenGe(M) FAILS for parity-shift.  Need s* possibly leastEvenGe(M) OR +2.
print("CLAIM: inf many D have lo_D < s* <= hi_D for s*=leastEvenGe(M) (FIXED) ?\n")
for name in BOUNDED:
    NMAX = 60000
    c, cinv, n = FAMILIES[name][0](NMAX)
    B = disp_bound(c, n, NMAX)
    for a, b in [(2, 4), (2, 3), (1, 5)]:
        M = b
        sstar = leastEvenGe(M)
        Dlim = min(n - b - 1, 60000)
        # for each candidate fixed even slack s in [M, b+B], count recurrence (last D)
        cands = list(range(leastEvenGe(M), b + B + 1, 2))
        recurring_slacks = []
        for s in cands:
            last = -1
            cnt = 0
            for D in range(Dlim):
                va, vb = c(a + D), c(b + D)
                lo, hi = min(va, vb) - D, max(va, vb) - D
                if lo < s <= hi:
                    last = D
                    cnt += 1
            if last >= Dlim // 2 and cnt >= 3:
                recurring_slacks.append(s)
        print(
            f"{name:18s} a={a} b={b} M={M} B={B} sstar={sstar} "
            f"recurring_even_slacks_in[M,b+B]={recurring_slacks}"
        )
