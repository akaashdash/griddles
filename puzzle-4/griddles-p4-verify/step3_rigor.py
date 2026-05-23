"""Work out the RIGOROUS step-3 argument for the bounded case.

We want: bounded-displacement non-EI c  =>  exists EVEN s>=M=b with separators at infinitely many D.

CANDIDATE CLEAN ARGUMENT (avoid per-value casework; use bijectivity engines directly):

Consider the joint map  F(D) := (va(D), vb(D)) = (c(a+D)-D, c(b+D)-D)   in ZxZ.
  Bounded disp => va(D)=a+phi(a+D) in [a-B, a+B], vb(D) in [b-B, b+B].  FINITE range.
By pigeonhole, some value (Va, Vb) recurs at infinitely many D.  On that fiber,
separator at slack s (s in (min(Va,Vb), max(Va,Vb)]) is CONSTANT in D.

So band_recurrence holds  <=>  SOME recurring (Va,Vb) has an even s>=M in its window.
Equivalently FAILS  <=>  EVERY recurring (Va,Vb) is non-separating.

Define for the fiber value v=(Va,Vb):  lo=min(Va,Vb), hi=max(Va,Vb).
Non-separating means: no even integer s with lo < s <= hi and s>=M=b.

Now bijectivity.  KEY engines available in Lean:
  (A) weak_descents_infinite (on ray a): infinitely many D with c(a+D) <= a+D, i.e. va(D) <= a.
  (B) weak_ascents:  infinitely many cells p with c(p) >= p.

PROPOSED ARGUMENT (TEST THIS):
  Among the FINITELY many fiber-values, consider those that recur infinitely.
  Call the set R.  Each r in R has window (lo_r, hi_r].
  Claim: there is r in R with hi_r >= M=b  (i.e. max(Va,Vb) >= b).
     Reason: weak_ASCENTS on ray b would give vb(D) = c(b+D)-D >= b infinitely often;
     among those infinitely many D, the (finitely many) fiber values means some recurring
     value has vb >= b, so hi_r >= b = M.
  But hi_r >= M alone is not enough (need an even s in (lo_r, M-1 ... hi_r]).

So I must ALSO use descents to push lo down.  Let me TEST several candidate joint claims
and see which is TRUE empirically, to find the right rigorous statement.
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


def recurring_values(c, n, a, b, Dmax):
    """Return dict value->(count,last_D,window) for values surviving to far half."""
    pc = Counter()
    last = {}
    win = {}
    Dlim = min(Dmax, n - b - 1)
    for D in range(Dlim):
        ca, cb = c(a + D), c(b + D)
        va, vb = ca - D, cb - D
        v = (va, vb)
        pc[v] += 1
        last[v] = D
        win[v] = (min(va, vb), max(va, vb))
    half = Dlim // 2
    R = {v: (pc[v], last[v], win[v]) for v in pc if pc[v] >= 3 and last[v] >= half}
    return R, Dlim


def even_in(lo, hi, M):
    start = max(lo + 1, M)
    if start % 2:
        start += 1
    return start if start <= hi else None


# ---- TEST CANDIDATE CLAIMS over all bounded (family, pair) ----
# Claim structure: among recurring values R, classify by window.
# We want to find the SIMPLEST true sufficient condition guaranteeing a separating r.

results = []
for name in BOUNDED:
    NMAX = 300000
    c, cinv, n = FAMILIES[name][0](NMAX)
    for a, b in [
        (1, 2),
        (1, 3),
        (1, 4),
        (2, 4),
        (2, 3),
        (3, 5),
        (1, 5),
        (2, 5),
        (3, 7),
        (4, 6),
    ]:
        if a >= b:
            continue
        M = b
        R, Dlim = recurring_values(c, n, a, b, NMAX)
        # the separating recurring values
        sep = {
            v: w for v, (cnt, ld, w) in R.items() if even_in(w[0], w[1], M) is not None
        }
        # diagnostic facts:
        #  - max over recurring of hi  (does some recurring value reach >= M?)
        #  - is there a recurring value with hi>=M AND  hi>=M is even-reachable
        max_hi = max((w[1] for (_, _, w) in R.values()), default=-99)
        # among recurring with hi>=M, the min lo:
        recs_hi_geM = [(v, w) for v, (_, _, w) in R.items() if w[1] >= M]
        min_lo_among = min((w[0] for (_, w) in recs_hi_geM), default=99)
        results.append(
            (name, a, b, M, len(R), len(sep), max_hi, min_lo_among, bool(sep))
        )

allok = all(r[-1] for r in results)
nsep0 = [r for r in results if r[5] == 0]
print(
    f"Total (family,pair): {len(results)}, all have separating recurring value: {allok}"
)
if nsep0:
    print("CASES WITH NO SEPARATING RECURRING VALUE:")
    for r in nsep0:
        print("  ", r)

# Now characterize: is it ALWAYS true that some recurring value has hi>=M?
no_hi = [r for r in results if r[6] < r[3]]
print(f"\nCases where NO recurring value reaches hi>=M (max_hi<M): {len(no_hi)}")
for r in no_hi[:10]:
    print("  ", r)

# And: among recurring values with hi>=M, is there always one with an even slack in window?
# i.e. is "exists recurring with hi>=M" SUFFICIENT? Check: cases with max_hi>=M but no sep.
hi_but_nosep = [r for r in results if r[6] >= r[3] and r[5] == 0]
print(f"\nCases with some recurring hi>=M but NO separating value: {len(hi_but_nosep)}")
for r in hi_but_nosep[:20]:
    print("  ", r)
