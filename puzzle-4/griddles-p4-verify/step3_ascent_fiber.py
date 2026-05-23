"""Test: pigeonhole the fiber RESTRICTED to weak-ascent displacements of b.

On Ab := {D : c(b+D) >= b+D}  (infinite, by weak_ascents_infinite), the value (va,vb)
has vb = c(b+D)-D >= b.  Pigeonhole on Ab (bounded disp => finite values) gives a recurring
value v* with vb* >= b, hence hi_{v*} >= b = M.
QUESTION: is v* ALWAYS separating?  (would give a clean proof using only weak_ascents +
finite pigeonhole, no i/ii casework).

Test variants:
  A_asc: recurring value on Ab maximizing hi  -> separating?
  any_asc: ANY recurring value on Ab  -> at least one separating?
Also test the symmetric: restrict to STRICT ascents c(b+D) >= b+D+1 (vb>=b+1 => hi>=b+1,
which for odd b gives the even s=b+1>=M in window if lo<b+1).
"""

from collections import Counter

from families import FAMILIES


def disp_bound(c, n, upto):
    return max(abs(c(x) - x) for x in range(1, min(n, upto)))


def sep_window(lo, hi, M):
    start = max(lo + 1, M)
    if start % 2:
        start += 1
    return start <= hi


ALL = [k for k, v in FAMILIES.items() if not v[1]]
fail_any_asc = []
fail_any_strict = []
total = 0
for name in ALL:
    NMAX = 80000
    try:
        c, cinv, n = FAMILIES[name][0](NMAX)
    except Exception:
        continue
    B = disp_bound(c, n, NMAX)
    if B > 50:
        continue
    for a in range(1, 5):
        for b in range(a + 1, 7):
            M = b
            Dlim = min(n - b - 1, 80000)
            # restrict to weak ascents of b
            pc = Counter()
            last = {}
            win = {}
            pcs = Counter()
            lasts = {}
            wins = {}
            for D in range(Dlim):
                va, vb = c(a + D), c(b + D)
                if vb >= b + D:  # weak ascent of b
                    v = (va - D, vb - D)
                    pc[v] += 1
                    last[v] = D
                    win[v] = (min(va, vb) - D, max(va, vb) - D)
                if vb >= b + D + 1:  # strict ascent of b
                    v = (va - D, vb - D)
                    pcs[v] += 1
                    lasts[v] = D
                    wins[v] = (min(va, vb) - D, max(va, vb) - D)
            half = Dlim // 2
            R = [v for v in pc if pc[v] >= 3 and last[v] >= half]
            Rs = [v for v in pcs if pcs[v] >= 3 and lasts[v] >= half]
            if R:
                total += 1
                if not any(sep_window(*win[v], M) for v in R):
                    fail_any_asc.append((name, a, b, [(v, win[v]) for v in R]))
            if Rs and not any(sep_window(*wins[v], M) for v in Rs):
                fail_any_strict.append((name, a, b, [(v, wins[v]) for v in Rs]))

print(f"total (family,pair) with weak-ascent recurring set: {total}\n")
print(
    f"WEAK-ASCENT fiber: cases where NO recurring value separates: {len(fail_any_asc)}"
)
for f in fail_any_asc[:8]:
    print("   ", f)
print(
    f"\nSTRICT-ASCENT fiber: cases where NO recurring value separates: {len(fail_any_strict)}"
)
for f in fail_any_strict[:8]:
    print("   ", f)
