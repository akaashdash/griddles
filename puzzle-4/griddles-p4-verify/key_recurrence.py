"""Pin the EXACT bijectivity statement that yields the KEY RECURRENCE.

KEY RECURRENCE: at unbounded D, window (lo_D,hi_D] contains an even s>=M=b.

I will test a SEQUENCE of candidate sufficient conditions, each provable from existing
engines, and report which is TRUE for ALL bounded non-EI families:

  Engines available (Lean, axiom-clean):
    E1 weak_descents_infinite on ray a:  inf many D, c(a+D)<=a+D  i.e. va(D)<=a, so lo_D<=a-D+?
         actually va=c(a+D), lo_D=min(va,vb)-D.  c(a+D)<=a+D => va-D<=a => the a-coordinate
         contributes  va-D <= a  to the min, so lo_D <= a < b = M.   GOOD: lo_D <= a.
    E2 weak_ascents on ray b:  inf many D, c(b+D)>=b+D i.e. vb-D>=b, so hi_D>=vb-D>=b=M. GOOD.

  PROBLEM: E1 and E2 give inf many D EACH, but maybe never the SAME D.

CANDIDATE A (the dream): inf many D with BOTH lo_D<=a AND hi_D>=M.
   At such D: window (lo_D,hi_D] contains (a, M] = (a, b].  Does (a,b] contain an even s>=M=b?
   Need even s with a < s <= b and s>=b, i.e. s=b if b even.  If b ODD, (a,b] has no even >=b
   (b odd, b-1<b).  So CANDIDATE A alone insufficient for odd b -- need hi_D>=b+1.

CANDIDATE B: inf many D with lo_D<=a AND hi_D>=b+1.
   Then window contains (a,b+1] which has an even s in {b if even, b+1 if b odd}, and that
   even s satisfies s>=b=M and s>a>=... s>a so s>lo_D. SEPARATOR at even s>=M.  CHECK if B holds.

CANDIDATE C: just test the raw fact 'inf many D: window contains even s>=M' and separately
   the joint engine facts, to see what's really needed.
"""

from families import FAMILIES

BOUNDED = [
    "block_cycle_2",
    "block_cycle_3",
    "block_cycle_7",
    "rev_block_2",
    "rev_block_5",
    "adjacent_involution",
    "parity_shift",
    "swap_at_powers",
    "random_per_4_0",
    "random_per_4_1",
    "random_per_6_0",
    "random_per_6_2",
]


def disp_bound(c, n, upto):
    return max(abs(c(x) - x) for x in range(1, min(n, upto)))


def recurs(cnt, last, Dlim):
    return cnt >= 3 and last >= Dlim // 2


for name in BOUNDED:
    NMAX = 80000
    c, cinv, n = FAMILIES[name][0](NMAX)
    B = disp_bound(c, n, NMAX)
    for a, b in [(2, 4), (2, 3), (1, 3), (3, 5), (1, 5), (1, 2)]:
        M = b
        Dlim = min(n - b - 1, 80000)
        # counters
        cA = [0, -1]  # lo<=a AND hi>=M
        cB = [0, -1]  # lo<=a AND hi>=b+1
        cKEY = [0, -1]  # window has even s>=M
        cE1 = [0, -1]  # lo<=a (descent-of-a contributes)
        cE2 = [0, -1]  # hi>=M (ascent contributes)
        for D in range(Dlim):
            va, vb = c(a + D), c(b + D)
            lo, hi = min(va, vb) - D, max(va, vb) - D
            if lo <= a:
                cE1[0] += 1
                cE1[1] = D
            if hi >= M:
                cE2[0] += 1
                cE2[1] = D
            if lo <= a and hi >= M:
                cA[0] += 1
                cA[1] = D
            if lo <= a and hi >= b + 1:
                cB[0] += 1
                cB[1] = D
            # even s>=M in (lo,hi]
            start = max(lo + 1, M)
            if start % 2:
                start += 1
            if start <= hi:
                cKEY[0] += 1
                cKEY[1] = D
        print(
            f"{name:18s} a={a} b={b}(odd={b % 2}) B={B} | "
            f"E1(lo<=a):{recurs(*cE1, Dlim)} E2(hi>=M):{recurs(*cE2, Dlim)} "
            f"A(lo<=a&hi>=M):{recurs(*cA, Dlim)} B(lo<=a&hi>=b+1):{recurs(*cB, Dlim)} "
            f"KEY:{recurs(*cKEY, Dlim)}"
        )
