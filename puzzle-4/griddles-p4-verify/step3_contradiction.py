"""Nail the EXACT contradiction in step 3.

Contrapositive form (what noSeparator_allSlack_imp_eventuallyIdentity needs in bounded case):
  HYP: cofinitely many D, window (lo_D,hi_D] has NO even s>=M.   [for the fixed pair a<b]
  GOAL: EI.

We do NOT prove EI per single pair (Lemma A needs Indistinguishable, three-time signal).
BUT the band_recurrence_ge_max statement quantifies the pair INTERNALLY: it's stated for a
GIVEN pair a,b but used (in main) for ALL pairs via slackOf.  So actually band_recurrence_ge_max
is per-pair: for EACH a!=b, exists recurring s>=max.  The contradiction must therefore be:
  bounded non-EI c, fixed pair a<b  =>  window separates (even s>=M) infinitely often.

So I must derive a contradiction from: 'cofinitely many D, no even s>=M in (lo_D,hi_D]'.
This is a SINGLE-PAIR statement.  Does it force a contradiction with bijectivity ALONE
(no Lemma A)?  Let me test: build a NON-EI bijection that is cofinitely non-separating for
some pair (a,b).  If NONE exists, the single-pair bijectivity contradiction is the right tool.
If one EXISTS (non-EI but cofinitely-non-sep for a pair), then per-pair bijectivity is NOT
enough and we'd need Lemma A / multiple pairs.

CRUCIAL TEST: is there a bounded NON-EI c and a pair a<b with cofinitely-non-separating window?
"""

from families import FAMILIES


def disp_bound(c, n, upto):
    return max(abs(c(x) - x) for x in range(1, min(n, upto)))


ALL = list(FAMILIES.keys())
print("Searching for a bounded NON-EI c + pair (a,b) that is COFINITELY non-separating")
print(
    "(i.e. window has no even s>=M for all large D). If found -> single-pair bijectivity"
)
print(
    "insufficient. If none -> per-pair bijectivity contradiction is the right tool.\n"
)

found = []
for name in ALL:
    fn, is_ei = FAMILIES[name]
    if is_ei:
        continue
    NMAX = 60000
    try:
        c, cinv, n = fn(NMAX)
    except Exception:
        continue
    B = disp_bound(c, n, NMAX)
    if B > 50:  # skip clearly-unbounded growing families for THIS test
        continue
    from collections import Counter

    for a in range(1, 6):
        for b in range(a + 1, 8):
            M = b
            Dlim = min(n - b - 1, 60000)
            # FIBER-BASED test: collect values (va,vb), their windows, and recurrence.
            # A value is "recurring" if hit at >=3 D AND its last hit is in the far half
            # (log-sparse values like swap_at_powers (0,1) still pass this).
            pc = Counter()
            last = {}
            win = {}
            for D in range(Dlim):
                va, vb = c(a + D), c(b + D)
                v = (va - D, vb - D)
                pc[v] += 1
                last[v] = D
                win[v] = (min(va, vb) - D, max(va, vb) - D)
            half = Dlim // 2
            R = [v for v in pc if pc[v] >= 3 and last[v] >= half]

            def sep_value(w):
                lo, hi = w
                start = max(lo + 1, M)
                if start % 2:
                    start += 1
                return start <= hi

            sep_recurring = [v for v in R if sep_value(win[v])]
            # GENUINE cofinitely-non-separating <=> NO recurring value separates
            if len(sep_recurring) == 0:
                found.append((name, a, b, len(R), Dlim, B))

if found:
    print(
        "FOUND cofinitely-non-separating (non-EI) cases (single-pair bijectivity INSUFFICIENT):"
    )
    for f in found[:30]:
        print("  ", f)
    print(f"\n  total: {len(found)}")
else:
    print(
        "NONE FOUND: every bounded non-EI c separates (even s>=M) at unbounded D for EVERY"
    )
    print(
        "pair (a,b).  => the per-pair recurrence holds; the contradiction is single-pair."
    )
