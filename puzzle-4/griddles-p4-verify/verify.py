import sys

import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from families import FAMILIES

# Lemma (slack form). a<b. For even s >= max(a,b)=b:
#   separator at slack s, displacement D  iff  [c(a+D)<D+s] != [c(b+D)<D+s].
# HYP: for every even s>=b, separators eventually absent (exists D0 forall D>=D0 no sep).
# Claim: HYP => EI.  Contrapositive: non-EI => some even s>=b has separators at unbounded D.


def sep_at(c, a, b, s, D):
    A = c(a + D) < D + s
    B = c(b + D) < D + s
    return A != B


def separating_Ds(c, a, b, s, Dmax, NMAX):
    """Return list of D in [0,Dmax) with a separator at slack s, requiring a+D,b+D<=NMAX."""
    out = []
    for D in range(0, Dmax):
        if b + D > NMAX:
            break
        if sep_at(c, a, b, s, D):
            out.append(D)
    return out


def analyze_pair(c, NMAX, a, b, Dmax=20000, smax_excess=12):
    """For pair a<b, find which even slacks s in [b, b+smax_excess] have separators,
    and where the LAST separator is (proxy for D0(s)). Also find recurring (unbounded) slacks."""
    b0 = b
    results = {}
    for s in range(b0, b0 + smax_excess + 1):
        if s % 2 != 0:
            continue
        Ds = separating_Ds(c, a, b, s, Dmax, NMAX)
        if Ds:
            results[s] = (len(Ds), Ds[0], Ds[-1])
        else:
            results[s] = (0, None, None)
    return results


def is_recurring(c, a, b, s, Dmax, NMAX, tail_frac=0.5):
    """Heuristic: separators appear in the upper tail of the window -> likely unbounded."""
    Ds = separating_Ds(c, a, b, s, Dmax, NMAX)
    if not Ds:
        return False, 0, None
    # max usable D
    maxD = min(Dmax, NMAX - b)
    cutoff = int(maxD * tail_frac)
    in_tail = [D for D in Ds if D >= cutoff]
    return (len(in_tail) > 0), len(Ds), (Ds[-1] if Ds else None)


if __name__ == "__main__":
    NMAX = 60000
    Dmax = 30000
    pairs = [
        (1, 2),
        (2, 3),
        (1, 3),
        (2, 4),
        (1, 4),
        (3, 5),
        (1, 5),
        (2, 5),
        (4, 6),
        (3, 6),
        (5, 7),
    ]
    total = 0
    fails = 0
    print(
        "=== Lemma truth check: non-EI => some even s>=max(a,b) recurs (separators in tail) ==="
    )
    for fname, (builder, is_EI) in sorted(FAMILIES.items()):
        if is_EI:
            continue
        c, cinv, n = builder(NMAX)
        # restrict NMAX to actual built length
        Nlim = n
        for a, b in pairs:
            if b + 200 > Nlim:
                continue
            total += 1
            # does some even s>=b recur?
            found = None
            for s in range(b, b + 14 + 1):
                if s % 2:
                    continue
                rec, cnt, last = is_recurring(c, a, b, s, Dmax, Nlim)
                if rec:
                    found = (s, cnt, last)
                    break
            if found is None:
                fails += 1
                print(f"  FAIL (no recurring slack): {fname} pair ({a},{b})")
    print(
        f"checked {total} (family,pair) non-EI combos; recurring-slack failures = {fails}"
    )

    print(
        "\n=== Identity (EI) sanity: NO even s>=max recurs (Bob can't distinguish) ==="
    )
    c, cinv, n = FAMILIES["identity"][0](NMAX)
    for a, b in pairs[:6]:
        anyrec = False
        for s in range(b, b + 20):
            if s % 2:
                continue
            rec, cnt, last = is_recurring(c, a, b, s, Dmax, n)
            if rec:
                anyrec = True
                break
        # also count total separators across all slacks
        tot = sum(
            len(separating_Ds(c, a, b, s, Dmax, n))
            for s in range(b, b + 20)
            if s % 2 == 0
        )
        print(
            f"  id pair ({a},{b}): recurring? {anyrec}, total separators(any even s<b+20)={tot}"
        )
