r"""Johnston subgroup R sub-split of class C.

R = { p : sup over intervals I of |I \ p(I)| < infinity }  (Witula survey, Johnston [31]).
R is a subgroup of CC (two-sided convergent).  Test which class-C witnesses are in R, and
whether membership in R yields a clean "intervals move boundedly" structure that proves the
per-pair separator recurrence.

J(p, L) := max over windows I of length up to L of |I \ p(I)|.  If this saturates (stops
growing with L), p is plausibly in R; if it grows with L, p is not in R.
"""

from families import (
    adjacent_involution,
    block_cycle,
    growing_blocks,
    parity_shift,
    rev_block,
    swap_at_powers,
)


def jncoeff(c, eff, Lmax):
    r"""max over intervals I=[lo,hi], hi-lo+1 <= Lmax, of |I \ c(I)|."""
    best = 0
    best_I = None
    # sample windows; full scan over all (lo,len) up to caps
    for L in range(1, Lmax + 1):
        for lo in range(1, eff - L + 1):
            hi = lo + L - 1
            I = set(range(lo, hi + 1))
            cI = set(c(x) for x in I)
            d = len(I - cI)
            if d > best:
                best = d
                best_I = (lo, hi)
    return best, best_I


def jn_profile(name, c, eff):
    print(f"\n--- {name} ---")
    prev = None
    for Lmax in [4, 8, 16, 32, 64]:
        if Lmax > eff - 2:
            break
        b, I = jncoeff(c, min(eff, 400), Lmax)  # cap scan region for speed
        flag = ""
        if prev is not None and b > prev:
            flag = "  (grew)"
        print(f"   Lmax={Lmax:3}: J={b}  worst I={I}{flag}")
        prev = b


def main():
    N = 500
    print(
        "=== Johnston J(p,Lmax) = max_I |I \\ p(I)| over intervals up to length Lmax ==="
    )
    print("R-membership <=> J saturates (bounded as Lmax->inf)")
    c, _, _ = parity_shift(N + 10)
    jn_profile("parity_shift", c, N)
    c, _, nm = swap_at_powers(N + 10)
    jn_profile("swap_at_powers", c, nm - 1)
    c, _, nm = growing_blocks(N + 10, True)
    jn_profile("growing_blocks_rev", c, nm - 1)
    c, _, nm = adjacent_involution(N + 10)
    jn_profile("adjacent_involution", c, nm - 1)
    c, _, nm = block_cycle(N + 10, 5)
    jn_profile("block_cycle_5", c, nm - 1)
    c, _, nm = rev_block(N + 10, 5)
    jn_profile("rev_block_5", c, nm - 1)


if __name__ == "__main__":
    main()
