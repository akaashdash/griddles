"""Rigorous verification of the BOUNDED-displacement case of band_recurrence_ge_max.

Setup (from the Lean repo):
  - c : bijection of N+, NOT eventually identity.
  - a < b cells, M := b.  phi(n) := c(n) - n.
  - va(D) := a + phi(a+D) = c(a+D),  vb(D) := b + phi(b+D) = c(b+D).
  - slack-s separator at D  <=>  s in (min(va,vb), max(va,vb)]   (half-open window)
        equivalently exactly one of va, vb >= D+s ... but with the window in absolute
        coords: NOTE the Lean separatorAtSlack compares c(.).val against D+s.
        So separator at slack s, displ D  <=>  min(c(a+D),c(b+D)) < D+s <= max(...).
        Writing va=c(a+D), vb=c(b+D): s in (min(va,vb) - D, max(va,vb) - D].

GOAL: exists EVEN s >= M with separators at INFINITELY MANY D.

We probe: for bounded families, find the infinitely-recurring (phi(a+D),phi(b+D)) values,
their windows, and confirm at least one recurring value separates with an even s>=M.
"""

from collections import Counter

from families import FAMILIES


def window_abs(c, a, b, D):
    """Return (lo, hi) such that slack-s separator at D <=> s in (lo, hi] (absolute slack)."""
    va = c(a + D)
    vb = c(b + D)
    lo = min(va, vb) - D
    hi = max(va, vb) - D
    return lo, hi


def even_in_window_ge_M(lo, hi, M):
    """Smallest even s with lo < s <= hi and s >= M, or None."""
    start = max(lo + 1, M)
    # round start up to even
    if start % 2 != 0:
        start += 1
    if start <= hi:
        return start
    return None


def analyze(name, NMAX, a, b, Dmax):
    c_fn, cinv, n = FAMILIES[name][0](NMAX), None, None
    c, cinv, nlen = c_fn if isinstance(c_fn, tuple) else (None, None, None)
    M = b
    # recurring phi-pair counter, restricted to D where both cells defined
    pair_count = Counter()
    pair_windows = {}
    pair_last = {}  # last displacement at which the value occurred
    Dlim = min(Dmax, nlen - b - 1)
    for D in range(0, Dlim):
        ca = c(a + D)
        cb = c(b + D)
        pa = ca - (a + D)
        pb = cb - (b + D)
        pair_count[(pa, pb)] += 1
        pair_last[(pa, pb)] = D
        lo, hi = (min(ca, cb) - D, max(ca, cb) - D)
        pair_windows[(pa, pb)] = (lo, hi)
    # "Recurring" = occurs at unbounded D.  A log-sparse value (swap_at_powers: D=2^k-b)
    # is genuinely infinite but its last occurrence sits near the previous power of two.
    # Robust test: occurs at >=3 distinct displacements AND last occurrence > Dlim/2 (it
    # survived into the far half of the scan).  Catches dense and log-sparse recurrence.
    half = Dlim // 2
    recurring = [
        (p, cnt) for p, cnt in pair_count.items() if cnt >= 3 and pair_last[p] >= half
    ]
    recurring.sort(key=lambda t: -t[1])
    # find separating recurring values (even s >= M in window)
    separating = []
    nonsep = []
    for p, cnt in recurring:
        lo, hi = pair_windows[p]
        s = even_in_window_ge_M(lo, hi, M)
        if s is not None:
            separating.append((p, cnt, (lo, hi), s))
        else:
            nonsep.append((p, cnt, (lo, hi)))
    return M, recurring, separating, nonsep, Dlim


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

if __name__ == "__main__":
    NMAX = 200000
    fails = []
    for name in BOUNDED:
        for a, b in [(1, 2), (1, 3), (1, 4), (2, 4), (2, 3), (3, 5), (1, 5), (2, 5)]:
            if a >= b:
                continue
            M, rec, sep, nonsep, Dlim = analyze(name, NMAX, a, b, NMAX)
            ok = len(sep) >= 1
            tag = "OK " if ok else "FAIL"
            if not ok:
                fails.append((name, a, b))
            # print a compact summary; show whether some recurring value separates
            srep = sep[0] if sep else None
            print(
                f"{tag} {name:20s} a={a} b={b} M={M} #rec={len(rec)} #sep={len(sep)} "
                f"#nonsep={len(nonsep)} witness={srep}"
            )
    print()
    if fails:
        print("FAILURES:", fails)
    else:
        print("ALL BOUNDED (family,pair) HAVE A SEPARATING RECURRING VALUE.")
