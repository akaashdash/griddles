"""Verify the CLEAN bounded-case argument (uniform D-floor from bounded displacement).

CLAIM CHAIN:
  Bounded disp |phi|<=B.  M=b.  Suppose (for contradiction) NO even s>=M separates at
  infinitely many D.
  STEP A: any separator (at any D) has slack s = (some t-D) with the slack-s window being
          s in (lo_D, hi_D], lo_D=min(va,vb)-D, hi_D=max(va,vb)-D, va=c(a+D),vb=c(b+D).
          Bounded disp => hi_D <= max(a,b)+B = b+B.  So a separator at slack s>=M=b needs
          s in [b, b+B].  FINITE set of even slacks: E = {even s : b<=s<=b+B}.
  STEP B: each s in E has finite separating-D set (by the contra hypothesis).  Take D* =
          max over s in E of its floor.  Then for all D>=D*, NO even s in E separates,
          hence (by step A) NO even s>=M separates at all, for ALL D>=D*.
  STEP C: "for all D>=D*, no even s>=M separates" must contradict bijectivity (=> would
          force EI).  VERIFY: what does no-even-s>=M-separator at D actually say, and does
          it force c=id past some point?

This file verifies STEP A (the slack-bound) and STEP C's contradiction empirically: we
take a bounded NON-EI perm and confirm that step C's hypothesis is VIOLATED for it (i.e.
there ARE separators past every D*), consistent with the claim that step C => EI.
"""

from families import FAMILIES

BOUNDED = [
    "block_cycle_2",
    "block_cycle_3",
    "rev_block_2",
    "rev_block_5",
    "adjacent_involution",
    "parity_shift",
    "swap_at_powers",
    "random_per_4_0",
    "random_per_6_2",
]


def disp_bound(c, n, upto):
    return max(abs(c(x) - x) for x in range(1, min(n, upto)))


def separator_at_slack(c, a, b, s, D):
    va, vb = c(a + D), c(b + D)
    # slack-s separator: exactly one of va,vb < D+s
    return (va < D + s) != (vb < D + s)


def any_even_sep_geM(c, a, b, M, D, smax):
    """Is there an even s with M<=s<=smax separating at D?"""
    s = M if M % 2 == 0 else M + 1
    while s <= smax:
        if separator_at_slack(c, a, b, s, D):
            return s
        s += 2
    return None


print("STEP A check: every separator has slack s<=b+B (B=disp bound).  And")
print(
    "STEP C check: for non-EI bounded c, separators at even s in [b,b+B] recur unboundedly.\n"
)
for name in BOUNDED:
    NMAX = 100000
    c, cinv, n = FAMILIES[name][0](NMAX)
    B = disp_bound(c, n, NMAX)
    for a, b in [(1, 2), (2, 3), (1, 4), (2, 4), (3, 5), (1, 5)]:
        M = b
        smax = b + B  # finite slack cap
        # STEP A: verify no separator exists at slack > b+B (for any D)
        Dlim = n - b - 1
        viol_A = 0
        for D in range(0, min(Dlim, 20000)):
            va, vb = c(a + D), c(b + D)
            hi = max(va, vb) - D
            if hi > b + B:
                viol_A += 1
        # STEP C: last D (within scan) at which SOME even s in [M, smax] separates
        last_sep = -1
        count_sep = 0
        for D in range(0, min(Dlim, 100000)):
            if any_even_sep_geM(c, a, b, M, D, smax) is not None:
                last_sep = D
                count_sep += 1
        scanned = min(Dlim, 100000)
        recurs = last_sep >= scanned // 2 and count_sep >= 3
        print(
            f"{name:18s} a={a} b={b} B={B} smax={smax} | A_viol={viol_A} "
            f"| #sep={count_sep} last_sep={last_sep}/{scanned} recurs={recurs}"
        )
