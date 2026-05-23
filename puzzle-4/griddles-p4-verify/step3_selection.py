"""Find a SELECTION RULE picking a separating recurring value, with a bijectivity reason.

Candidates for 'which recurring value is guaranteed separating':
  R1: the recurring value maximizing hi_v = max(va,vb).
  R2: the recurring value maximizing vb (= c(b+D)-D), i.e. driven by b's ascent.
  R3: the recurring value with the WIDEST window (hi-lo).
  R4: among recurring values with hi>=M, the one with SMALLEST lo.

For each, check: is the SELECTED value always separating?  Find one with 0 failures, and
a bijectivity reason it's separating.
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
fails = {f"R{i}": [] for i in range(1, 5)}
total = 0
for name in ALL:
    NMAX = 60000
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
            Dlim = min(n - b - 1, 60000)
            pc = Counter()
            last = {}
            win = {}
            vbv = {}
            for D in range(Dlim):
                va, vb = c(a + D), c(b + D)
                v = (va - D, vb - D)
                pc[v] += 1
                last[v] = D
                win[v] = (min(va, vb) - D, max(va, vb) - D)
                vbv[v] = vb - D
            half = Dlim // 2
            R = [v for v in pc if pc[v] >= 3 and last[v] >= half]
            if not R:
                continue
            total += 1
            # R1: max hi
            v1 = max(R, key=lambda v: win[v][1])
            # R2: max vb
            v2 = max(R, key=lambda v: vbv[v])
            # R3: widest window
            v3 = max(R, key=lambda v: win[v][1] - win[v][0])
            # R4: among hi>=M, smallest lo
            R4c = [v for v in R if win[v][1] >= M]
            v4 = min(R4c, key=lambda v: win[v][0]) if R4c else None
            for tag, v in [("R1", v1), ("R2", v2), ("R3", v3), ("R4", v4)]:
                if v is None or not sep_window(win[v][0], win[v][1], M):
                    fails[tag].append((name, a, b, v, win.get(v)))

print(f"total (family,pair) with recurring set: {total}\n")
for tag in ["R1", "R2", "R3", "R4"]:
    print(f"{tag}: failures = {len(fails[tag])}")
    for f in fails[tag][:5]:
        print("    ", f)
