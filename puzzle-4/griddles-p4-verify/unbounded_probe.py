"""Probe the UNBOUNDED-displacement case (growing_blocks_rev: reverse blocks 2,3,4,...).

Bounded pigeonhole fails (infinitely many phi values).  Questions:
  Q1: what is the recurring fixed slack (>=M) for growing_blocks_rev, and is the slack
      range bounded or unbounded?
  Q2: Is the unbounded case EASIER (large displacements => abundant high-slack separators)?
  Q3: Test the CLAMPED-pigeonhole idea: replace phi by min(phi, B') for some cap B' so that
      the SEPARATION-RELEVANT part recovers finiteness.  Does a clamped value recur and
      separate at even s>=M in a finite range?
  Q4: Test the 'joint weak-descent(a) + weak-ascent(b) giving slack-M separator' idea.
"""

from collections import Counter

from families import FAMILIES


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


def sep_window(lo, hi, M):
    s = max(lo + 1, M)
    if s % 2:
        s += 1
    return s <= hi


NMAX = 300000
c, cinv, n = FAMILIES["growing_blocks_rev"][0](NMAX)

print("=== growing_blocks_rev (UNBOUNDED phi) ===")
# displacement growth
maxabs = 0
for x in range(1, min(n, NMAX)):
    maxabs = max(maxabs, abs(c(x) - x))
print(f"max |c(x)-x| over prefix {min(n, NMAX)} = {maxabs} (UNBOUNDED, grows ~sqrt(N))")

for a, b in [(1, 2), (2, 4), (2, 3), (1, 5)]:
    M = b
    Dlim = min(n - b - 1, NMAX)
    # Q1: which even slacks >=M separate, and the RANGE of separating slacks (windows).
    sep_slacks = Counter()
    last_for_slack = {}
    win_lo_hi = []
    for D in range(Dlim):
        va, vb = c(a + D), c(b + D)
        lo, hi = min(va, vb) - D, max(va, vb) - D
        win_lo_hi.append((lo, hi))
        # smallest even >=M in window
        s = max(lo + 1, M)
        if s % 2:
            s += 1
        if s <= hi:
            sep_slacks[s] += 1
            last_for_slack[s] = D
    his = [hi for (lo, hi) in win_lo_hi]
    los = [lo for (lo, hi) in win_lo_hi]
    # which slacks recur (last in far half)?
    half = Dlim // 2
    recurring = sorted(
        s for s in sep_slacks if last_for_slack[s] >= half and sep_slacks[s] >= 3
    )
    print(
        f"\n a={a} b={b} M={M}: hi range [{min(his)},{max(his)}]  lo range [{min(los)},{max(los)}]"
    )
    print(f"   smallest-even-slack histogram (top): {sep_slacks.most_common(6)}")
    print(
        f"   RECURRING even slacks >=M (last in far half): {recurring[:15]}{'...' if len(recurring) > 15 else ''}"
    )
    print(f"   #recurring slacks = {len(recurring)}")
    # Q2/Q3: does the CLAMPED smallest-even-slack (=leastEvenGe(M)) recur?
    sstar = leastEvenGe(M)
    cnt_sstar = sum(1 for (lo, hi) in win_lo_hi if lo < sstar <= hi)
    last_sstar = max(
        (D for D, (lo, hi) in enumerate(win_lo_hi) if lo < sstar <= hi), default=-1
    )
    print(
        f"   FIXED s*=leastEvenGe(M)={sstar}: recurs? count={cnt_sstar} last={last_sstar}/{Dlim} "
        f"-> {'YES' if last_sstar >= half and cnt_sstar >= 3 else 'NO'}"
    )
