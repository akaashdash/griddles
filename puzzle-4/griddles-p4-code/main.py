"""Trolley Retrieval (Puzzle 4) — computational verification of the solution.

ANSWER.  Bob has a winning strategy  <=>  the labelling permutation `c` is NOT eventually
the identity (i.e. `c(n) != n` for infinitely many `n`).

The *authoritative* proof is the machine-checked Lean development in `../griddles-p4-lean`
(`theorem main : BobWins c <-> ~ EventuallyIdentity c`, fully `sorry`-free and axiom-clean:
`#print axioms main = [propext, Classical.choice, Quot.sound]`).  This script reproduces the
*empirical* facts that motivate and corroborate that proof:

  (1) ANSWER         A belief-state (minimax) solver wins from every start cell for
                     non-eventually-identity permutations, and provably cannot for the
                     identity (eventually-identity => Bob loses).  The winner only ever uses
                     displacement `D >= 0` (so safety -- never falling to position <= 0 -- is
                     automatic), matching the Lean construction.
  (2) BAND IS FALSE  The naive "single fixed lag" band recurrence is false.  For the AP-split
                     permutation the separating lag climbs (~sqrt(D)), so no fixed even lag
                     recurs -- which is exactly why the proof needs the bounded/unbounded
                     dichotomy rather than one band lemma.
  (3) Q2-EVEN        For unbounded-above permutations every pair nonetheless has separators at
                     arbitrarily large EVEN lag (the enabling fact for the unbounded-above
                     case, `q2even` in Lean); for bounded-above permutations the lag is capped.

The game.  An invisible trolley starts at unknown cell `k0 >= 1`.  At each time `t = 1,2,...`
Bob pushes the trolley one cell left/right to position `k_t = k0 + D_t` (`D_t` = net
displacement); if `k_t <= 0` Bob loses; otherwise the trolley emits the bit `[c(k_t) < t]`.
Bob may instead guess the trolley's current cell; a correct guess wins.  Bob sees only the
signal history, not `k0`.

Run:  uv run main.py
"""

from __future__ import annotations

import sys
from functools import lru_cache
from math import isqrt

sys.setrecursionlimit(2_000_000)


# ---------------------------------------------------------------------------
# Permutations of N+ = {1, 2, 3, ...}, each returned as an array-backed function
# c : [1, n] -> [1, n].  `phi(n) = c(n) - n` is the (signed) displacement.
# ---------------------------------------------------------------------------


def _from_vals(vals: list[int]):
    """vals[i-1] = c(i); must be a permutation of {1,...,len(vals)}."""
    n = len(vals)
    assert sorted(vals) == list(range(1, n + 1)), "not a permutation prefix"
    return (lambda i: vals[i - 1]), n


def identity(nmax: int):
    return _from_vals(list(range(1, nmax + 1)))


def block_cycle(nmax: int, b: int):
    """Forward `b`-cycle on each block [kb+1, kb+b]:  bounded displacement."""
    m = (nmax // b) * b
    vals = [b * ((n - 1) // b) + ((n - 1) % b + 1) % b + 1 for n in range(1, m + 1)]
    return _from_vals(vals)


def rev_block(nmax: int, b: int):
    """Reverse each block [kb+1, kb+b]:  bounded displacement."""
    m = (nmax // b) * b
    vals = [b * ((n - 1) // b) + (b - 1 - (n - 1) % b) + 1 for n in range(1, m + 1)]
    return _from_vals(vals)


def adjacent_involution(nmax: int):
    """Swap (1 2)(3 4)... :  bounded displacement (|phi| = 1)."""
    m = (nmax // 2) * 2
    vals = [n + 1 if n % 2 == 1 else n - 1 for n in range(1, m + 1)]
    return _from_vals(vals)


def parity_shift(nmax: int):
    """c(1)=2; c(2k)=2k+2, c(2k+1)=2k-1.  Bounded displacement (|phi| = 2); non-EI.

    The hardest bounded example: it makes the joint sets vacuous, yet the band recurrence
    holds (at a fixed even lag).  Image of the prefix is an initial segment up to a boundary,
    so we evaluate via the formula rather than asserting a permutation prefix."""

    def c(x: int) -> int:
        if x == 1:
            return 2
        return x + 2 if x % 2 == 0 else x - 2

    return c, nmax


def growing_blocks_rev(nmax: int):
    """Reverse blocks of size 2, 3, 4, ... :  UNBOUNDED displacement; non-EI."""
    vals: list[int] = []
    start, size = 1, 2
    while start + size - 1 <= nmax:
        vals.extend(range(start + size - 1, start - 1, -1))
        start += size
        size += 1
    return _from_vals(vals)


def ap_split(nmax: int):
    """AP-split: evens slowly ASCEND, odds DESCEND to fill.  UNBOUNDED above; non-EI.

    A = {a_k = 2k + 2*isqrt(k)}; c(2k) = a_k (so phi(2k) = 2*isqrt(k) -> +inf), and
    c(2k-1) = the k-th positive integer not in A (so the odds descend).  This is the
    counterexample to the fixed-slack band recurrence: the separating lag climbs ~sqrt(D).
    """
    k = 1
    while True:  # choose K so that block of evens/odds covers [1, nmax]
        if 2 * k > nmax:
            break
        k += 1
    K = k + 2
    A = [2 * j + 2 * isqrt(j) for j in range(1, K + 1)]
    Aset = set(A)
    B: list[int] = []
    m = 1
    while len(B) < K:
        if m not in Aset:
            B.append(m)
        m += 1
    c_arr = [0] * (2 * K + 1)
    for j in range(1, K + 1):
        c_arr[2 * j] = A[j - 1]
        c_arr[2 * j - 1] = B[j - 1]
    return (lambda i: c_arr[i]), 2 * K


# (name, builder, eventually_identity?, bounded_above?)
FAMILIES = [
    ("identity", identity, True, True),
    ("block_cycle_3", lambda N: block_cycle(N, 3), False, True),
    ("block_cycle_5", lambda N: block_cycle(N, 5), False, True),
    ("rev_block_4", lambda N: rev_block(N, 4), False, True),
    ("adjacent_involution", adjacent_involution, False, True),
    ("parity_shift", parity_shift, False, True),
    ("growing_blocks_rev", growing_blocks_rev, False, False),
    ("ap_split", ap_split, False, False),
]


# ---------------------------------------------------------------------------
# (1) ANSWER:  belief-state minimax solver (D >= 0, hence always safe).
#     Returns True iff Bob can drive every start cell in {1..M} to a correct guess.
# ---------------------------------------------------------------------------


def bob_wins(cf, M: int, max_t: int, cap: int) -> bool:
    @lru_cache(maxsize=None)
    def win(belief: frozenset[int], D: int, t: int) -> bool:
        if len(belief) <= 1:  # localized -> guess current cell -> win
            return True
        if t >= max_t:
            return False
        for step in (1, -1):  # push right / left
            nd, nt = D + step, t + 1
            if nd < 0:  # keep displacement >= 0  =>  safety is free
                continue
            if min(belief) + nd < 1 or max(belief) + nd > cap:
                continue
            yes = frozenset(k for k in belief if cf(k + nd) < nt)
            no = belief - yes
            if yes and no:
                if win(yes, nd, nt) and win(no, nd, nt):
                    return True
            elif win(belief, nd, nt):
                return True
        return False

    return win(frozenset(range(1, M + 1)), 0, 0)


# ---------------------------------------------------------------------------
# Separators.  At displacement D and even lag s, cells a,b are "separated" iff
# [c(a+D) < D+s] != [c(b+D) < D+s], i.e. s in (min(va,vb), max(va,vb)] where
# va = c(a+D) - D, vb = c(b+D) - D.  (Bob's lag t - D is always even.)
# ---------------------------------------------------------------------------


def max_even_sep_lag(cf, a: int, b: int, d_lo: int, d_hi: int) -> int:
    """Largest even lag occurring as a separator for (a,b) over D in [d_lo, d_hi)."""
    best = -1
    for D in range(d_lo, d_hi):
        va, vb = cf(a + D) - D, cf(b + D) - D
        lo, hi = min(va, vb), max(va, vb)
        s = hi if hi % 2 == 0 else hi - 1  # largest even <= hi
        if s > lo and s > best:
            best = s
    return best


def fixed_even_lag_recurs(cf, a: int, b: int, d_hi: int) -> bool:
    """Does SOME fixed even lag s >= b separate (a,b) across all three octaves of [0, d_hi)?

    True  => a single fixed lag works (band recurrence holds).
    False => the working lag climbs (band recurrence fails -- needs the growing-lag staircase).
    """
    third = d_hi // 3
    counts: dict[int, list[int]] = {}
    for octave, (lo, hi) in enumerate(
        [(0, third), (third, 2 * third), (2 * third, d_hi)]
    ):
        for D in range(lo, hi):
            va, vb = cf(a + D) - D, cf(b + D) - D
            mn, mx = min(va, vb), max(va, vb)
            s = b if b % 2 == 0 else b + 1
            while s <= mx:
                if mn < s <= mx:
                    counts.setdefault(s, [0, 0, 0])[octave] += 1
                s += 2
    return any(all(oc > 0 for oc in c) for c in counts.values())


# ---------------------------------------------------------------------------
# Verifications.
# ---------------------------------------------------------------------------


def verify_answer() -> bool:
    print("(1) ANSWER:  Bob wins  <=>  c not eventually identity")
    print("    belief-state solver (D >= 0, always safe), candidate set {1..16}")
    ok = True
    for name, builder, is_ei, _ in FAMILIES:
        cf, n = builder(20_000)
        won = bob_wins(cf, 16, max_t=260, cap=min(n - 4, 6000))
        expected = not is_ei  # Bob wins iff NOT eventually identity
        flag = "OK" if won == expected else "FAIL"
        ok = ok and (won == expected)
        print(f"      {name:22s} EI={is_ei!s:5s}  Bob wins={won!s:5s}  [{flag}]")
    return ok


def verify_band_false() -> bool:
    print("\n(2) BAND RECURRENCE IS FALSE (the climbing-lag phenomenon)")
    print("    a fixed even lag s>=b recurs across all octaves?")
    ok = True
    cases = [
        ("parity_shift (bounded)", parity_shift, 2, 4, True),
        ("ap_split    (unbounded)", ap_split, 2, 4, False),
        ("ap_split    (unbounded)", ap_split, 1, 3, False),
    ]
    for label, builder, a, b, expect_fixed in cases:
        cf, n = builder(200_000)
        recurs = fixed_even_lag_recurs(cf, a, b, min(n - 8, 150_000))
        flag = "OK" if recurs == expect_fixed else "FAIL"
        ok = ok and (recurs == expect_fixed)
        verdict = "fixed lag recurs" if recurs else "lag CLIMBS (band false)"
        print(f"      {label} pair({a},{b}): {verdict}  [{flag}]")
    return ok


def verify_q2even() -> bool:
    print("\n(3) Q2-EVEN: unbounded-above => separators at arbitrarily large EVEN lag")
    print("    (max even separator lag grows with the D-range; capped for bounded)")
    ok = True
    for name, builder, _, bounded_above in FAMILIES:
        if name == "identity":
            continue
        cf, n = builder(300_000)
        a, b = 2, 4
        lo = max_even_sep_lag(cf, a, b, 0, n // 4)
        hi = max_even_sep_lag(cf, a, b, n // 2, n - 4)
        grows = hi > lo + 1
        # unbounded-above => Q2-even (grows);  bounded-above => capped (does not grow)
        expected = not bounded_above
        flag = "OK" if grows == expected else "FAIL"
        ok = ok and (grows == expected)
        kind = "GROWS (Q2-even)" if grows else "capped"
        print(
            f"      {name:22s} bdd-above={bounded_above!s:5s}  lag {lo}->{hi}  {kind}  [{flag}]"
        )
    return ok


def main() -> int:
    print("=" * 72)
    print("Trolley Retrieval (Puzzle 4) -- empirical verification")
    print("Authoritative proof: ../griddles-p4-lean (Lean, sorry-free, axiom-clean)")
    print("=" * 72)
    results = [verify_answer(), verify_band_false(), verify_q2even()]
    print("\n" + "=" * 72)
    if all(results):
        print("ALL CHECKS PASSED.")
        return 0
    print("SOME CHECKS FAILED.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
