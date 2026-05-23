"""Pin the EXACT mechanism: why does a separating recurring value exist?

A recurring value v has window (lo, hi] with lo=min(va,vb), hi=max(va,vb).
NON-separating means: no even s in (lo,hi] with s>=M.

Equivalent characterizations of non-separating (given hi>=lo):
  Let s0 = smallest even >= max(lo+1, M).  Non-sep <=> s0 > hi.

Type (i):  hi < M.            (window entirely below M)
Type (ii): hi >= M but s0>hi. Then the only even candidates in (lo,hi] are < M, so
           there's no even in [max(M,lo+1), hi].  This needs hi - max(M,lo+1) small.

KEY QUESTION: among ALL recurring values, why must one be separating?

HYPOTHESIS TO TEST (the rigorous core):
  Use weak_descents on ray b:  infinitely many D have c(b+D) <= b+D, i.e. vb(D) <= b.
  Use weak_ascents  on ray b:  infinitely many D have c(b+D) >= b+D, i.e. vb(D) >= b.
  Also c(a+D), c(b+D) are DISTINCT (injectivity, since a+D != b+D), so va != vb always:
       the window (lo,hi] is NONEMPTY (lo<hi), i.e. always at least width 1.

  Refined: consider the LARGER ray b alone? No - need a JOINT statement.

  Let me just empirically find: is it true that some recurring value has
     lo < M <= hi   AND   (hi-lo >= 2  OR  the even parity lands)?
  More usefully: test whether the recurring value realized at a WEAK ASCENT of b
  (vb>=b => hi>=vb>=b=M) combined with bijectivity forcing lo low enough, separates.
"""

from collections import Counter

from families import FAMILIES

BOUNDED = [
    "block_cycle_2",
    "block_cycle_3",
    "block_cycle_4",
    "block_cycle_5",
    "block_cycle_7",
    "rev_block_2",
    "rev_block_3",
    "rev_block_4",
    "rev_block_5",
    "rev_block_7",
    "adjacent_involution",
    "parity_shift",
    "swap_at_powers",
    "random_per_4_0",
    "random_per_4_1",
    "random_per_6_0",
    "random_per_6_2",
]


def even_in(lo, hi, M):
    start = max(lo + 1, M)
    if start % 2:
        start += 1
    return start if start <= hi else None


def recurring(c, n, a, b, Dmax):
    pc = Counter()
    last = {}
    win = {}
    Dlim = min(Dmax, n - b - 1)
    for D in range(Dlim):
        va, vb = c(a + D) - D, c(b + D) - D
        v = (va, vb)
        pc[v] += 1
        last[v] = D
        win[v] = (min(va, vb), max(va, vb))
    half = Dlim // 2
    return {v: win[v] for v in pc if pc[v] >= 3 and last[v] >= half}, Dlim


# Test: is the set of all NON-separating recurring windows necessarily NOT covering, i.e.
# the union of (lo,hi] over recurring values must contain an even s>=M.
# Reformulate cleanly: the recurring values' windows, do they JOINTLY always contain an
# even s>=M?  (We just need ONE recurring value to contain one, which is the same thing.)

# Deeper: let's verify the SPECIFIC rigorous claim I'll prove:
#   (P) There is a recurring value with hi >= M and lo <= M-2, OR a recurring value with
#       hi >= M+1 (even M) reach... -- just enumerate the cases and find a UNIFORM reason.
#
# Cleanest provable statement candidate:
#   Let s* = leastEvenGe(M).  Among recurring values, is there ALWAYS one with
#   lo < s* <= hi  for SOME even s* >= M ?   This is exactly "separating", circular.
#
# Instead test the DESCENT+ASCENT JOINT claim that gives a clean Lean proof:
#   There exist infinitely many D with  va(D) <= a   (weak descent of a)  -- call set Da.
#   There exist infinitely many D with  vb(D) >= b   (weak ascent  of b)  -- call set Ab.
#   If a SINGLE recurring value lies in Da ∩ Ab fiber, then lo<=va<=a<b<=vb<=hi so
#       (lo,hi] ⊇ (a, b] ∋ leastEvenGe(... ) ... contains every integer in (a,b], and since
#       b-a>=1, and we need an EVEN one >= M=b in (a,b]... but (a,b] only goes UP TO b=M.
#   Hmm: an even s>=M=b in (lo,hi] with lo<=a, hi>=b: need even s in [b, hi]. s=b works if
#       b even (b in (lo,b]). If b odd, need even s in (b, hi] => need hi>=b+1.
# So the joint "descent of a AND ascent of b at same fiber" gives lo<=a, hi>=b. Then:
#     b even  => s=b works (b>lo since lo<=a<b).            SEPARATES.
#     b odd   => need hi>=b+1, i.e. STRICT ascent vb>=b+1 OR va contributes... test it.
print("Testing joint descent-of-a / ascent-of-b structure on recurring values\n")
for name in BOUNDED:
    NMAX = 300000
    c, cinv, n = FAMILIES[name][0](NMAX)
    for a, b in [(2, 3), (1, 3), (3, 5), (1, 5), (2, 5)]:  # focus on ODD b (hard case)
        M = b
        R, Dlim = recurring(c, n, a, b, NMAX)
        sep = {v: w for v, w in R.items() if even_in(w[0], w[1], M)}
        # check the strict-ascent property among separating values
        info = []
        for v, w in sep.items():
            lo, hi = w
            info.append(
                (
                    v,
                    w,
                    "b-even" if b % 2 == 0 else ("hi>=b+1" if hi >= b + 1 else "OTHER"),
                )
            )
        print(f"{name:20s} a={a} b={b}(odd={b % 2 == 1}) #R={len(R)} #sep={len(sep)}")
        for v, w, why in info[:3]:
            print(f"     sep value {v} window {w}: {why}")
