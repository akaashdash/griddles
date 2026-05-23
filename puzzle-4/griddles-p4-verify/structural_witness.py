"""Structural deep-dive: WHY the band recurrence holds, and WHICH even s works.

For the hardest family, doubling_blocks_rev (reverse block [2^k, 2^(k+1)-1]):
  - When a+D and b+D both lie in block k, c(x)=M_k-(x-2^k)=3*2^k-1-x with M_k=3*2^k-1.
    => u_D = c(a+D)-D = 3*2^k-1 - a - 2D,   v_D = ... - b - 2D.
    => R - L = b - a  (band width = b-a, INDEPENDENT of D).
  - So per block, as D sweeps the block, the band [L,R] of width (b-a) slides DOWN by 2 each
    step. Any FIXED even s is in (L,R] for at most ceil((b-a)/2) consecutive D within a block,
    and this happens once per block (until s exits the block's R-range). Net: each fixed even s
    gets O(1) separators PER BLOCK, hence ~log_2(D) separators in [0,D]: UNBOUNDED but log-sparse.

This script empirically confirms:
  (1) band width R-L = b-a exactly while both points are co-block (and jumps at boundaries),
  (2) every fixed even s>=b recurs (>=1 separator) in EVERY sufficiently deep block,
  (3) the separator count per fixed s ~ (number of blocks) = log_2(D).

Run: uv run --no-project structural_witness.py
"""

import math

from counterexample_search import doubling_blocks_rev, squared_blocks_rev


def coblock_doubling(x, B_unused=None):
    return int(math.log2(x))


def run_doubling(a, b, Dmax=4_000_000):
    c, cinv, n = doubling_blocks_rev(16_000_000)
    Dmax = min(Dmax, n - b - 1)
    # (1) band width when co-block
    same_block_widths = set()
    cross_block_widths = set()
    for D in range(Dmax):
        x, y = a + D, b + D
        kx, ky = int(math.log2(x)), int(math.log2(y))
        u, v = c(x) - D, c(y) - D
        w = abs(u - v)
        if kx == ky:
            same_block_widths.add(w)
        else:
            cross_block_widths.add(w)
    print(f"  (a,b)=({a},{b}) b-a={b - a}")
    print(
        f"    co-block band widths R-L: {sorted(same_block_widths)} (predict {{{b - a}}})"
    )
    print(f"    cross-block band widths (sample): {sorted(cross_block_widths)[:8]}...")

    # (2)/(3): per fixed even s, count separators per block index k
    from collections import defaultdict

    for s in [b if b % 2 == 0 else b + 1, (b if b % 2 == 0 else b + 1) + 4]:
        per_block = defaultdict(int)
        total = 0
        for D in range(Dmax):
            u, v = c(a + D) - D, c(b + D) - D
            L, R = min(u, v), max(u, v)
            if L < s <= R:
                k = int(math.log2(a + D))
                per_block[k] += 1
                total += 1
        blocks_hit = sorted(per_block)
        nblocks = int(math.log2(a + Dmax))
        print(
            f"    s={s}: total seps={total} over D<{Dmax}; "
            f"blocks with >=1 sep: {len(blocks_hit)}/{nblocks} "
            f"(deep blocks {blocks_hit[-6:]}); counts/block {[per_block[k] for k in blocks_hit[-6:]]}"
        )
        print("      => count grows like #blocks = log2(D); UNBOUNDED, LOG-density.")


def run_squared(a, b, Dmax=2_000_000):
    c, cinv, n = squared_blocks_rev(4_000_000)
    Dmax = min(Dmax, n - b - 1)
    same = set()
    for D in range(Dmax):
        x, y = a + D, b + D
        kx, ky = int(math.isqrt(x)), int(math.isqrt(y))
        if kx == ky:
            u, v = c(x) - D, c(y) - D
            same.add(abs(u - v))
    print(
        f"  squared (a,b)=({a},{b}): co-block band widths = {sorted(same)} (predict {{{b - a}}})"
    )


if __name__ == "__main__":
    print("=== doubling_blocks_rev: structural confirmation ===")
    for a, b in [(2, 4), (1, 3), (3, 5), (1, 2), (5, 9)]:
        run_doubling(a, b)
        print()
    print("=== squared_blocks_rev: co-block band width = b-a ===")
    for a, b in [(2, 4), (1, 3), (3, 7)]:
        run_squared(a, b)
