"""Bijections of N+ ({1,2,3,...}) given as a function c(n) computed on a prefix.

Each family returns (c, cinv) closures defined on [1, NMAX], plus a flag whether EI.
We always supply a permutation that is a genuine bijection on the prefix range it touches.
"""


def make_perm_from_list(vals):
    # vals[i] = c(i+1).  Must be a permutation of 1..len(vals).
    n = len(vals)
    cmap = {i + 1: vals[i] for i in range(n)}
    inv = {v: k for k, v in cmap.items()}
    assert sorted(cmap.values()) == list(range(1, n + 1)), "not a permutation prefix"

    def c(x):
        return cmap[x]

    def cinv(y):
        return inv[y]

    return c, cinv, n


def identity(NMAX):
    vals = list(range(1, NMAX + 1))
    return make_perm_from_list(vals)


def block_cycle(NMAX, B):
    # within each block [kB+1, kB+B], cyclic shift: c(kB+i) = kB + (i mod B)+1
    vals = []
    for n in range(1, NMAX + 1):
        k = (n - 1) // B
        i = (n - 1) % B  # 0..B-1
        vals.append(k * B + (i % B) + 1 if False else k * B + ((i + 1) % B) + 1)
    # fix up: ensure permutation by truncating to multiple of B
    m = (NMAX // B) * B
    vals = vals[:m]
    return make_perm_from_list(vals)


def rev_block(NMAX, B):
    vals = []
    m = (NMAX // B) * B
    for n in range(1, m + 1):
        k = (n - 1) // B
        i = (n - 1) % B
        vals.append(k * B + (B - 1 - i) + 1)
    return make_perm_from_list(vals)


def adjacent_involution(NMAX):
    # c(2i-1)=2i, c(2i)=2i-1
    m = (NMAX // 2) * 2
    vals = []
    for n in range(1, m + 1):
        if n % 2 == 1:
            vals.append(n + 1)
        else:
            vals.append(n - 1)
    return make_perm_from_list(vals)


def parity_shift(NMAX):
    # c(1)=2; for k>=1: c(2k)=2k+2, c(2k+1)=2k-1.  Bijection of N+ (formula-defined).
    def c(x):
        if x == 1:
            return 2
        if x % 2 == 0:
            return x + 2
        else:
            return x - 2

    def cinv(y):
        if y == 2:
            return 1
        if y % 2 == 0:
            return y - 2
        else:
            return y + 2

    for x in range(1, min(NMAX, 5000)):
        assert cinv(c(x)) == x, (x, c(x), cinv(c(x)))
    return c, cinv, NMAX


def swap_at_powers(NMAX):
    # identity except swap (2^j, 2^j+1) for each j>=1
    cmap = {n: n for n in range(1, NMAX + 1)}
    j = 1
    while 2**j + 1 <= NMAX:
        a = 2**j
        cmap[a], cmap[a + 1] = cmap[a + 1], cmap[a]
        j += 1
    vals = [cmap[i] for i in range(1, NMAX + 1)]
    return make_perm_from_list(vals)


def growing_blocks(NMAX, reverse=True):
    # tile N+ with blocks of size 2,3,4,5,... ; within each block reverse (or cycle)
    vals = []
    start = 1
    bsize = 2
    while start + bsize - 1 <= NMAX:
        block = list(range(start, start + bsize))
        if reverse:
            block = block[::-1]
        else:
            block = block[1:] + block[:1]
        vals.extend(block)
        start += bsize
        bsize += 1
    return make_perm_from_list(vals)


def random_periodic(NMAX, B, seed=0):
    import random

    rng = random.Random(seed)
    # random permutation pattern of 0..B-1, applied per block
    pat = list(range(B))
    rng.shuffle(pat)
    if pat == list(range(B)):
        pat = pat[1:] + pat[:1]
    vals = []
    m = (NMAX // B) * B
    for n in range(1, m + 1):
        k = (n - 1) // B
        i = (n - 1) % B
        vals.append(k * B + pat[i] + 1)
    return make_perm_from_list(vals)


FAMILIES = {}


def register():
    FAMILIES["identity"] = (identity, True)
    for B in [2, 3, 4, 5, 7]:
        FAMILIES[f"block_cycle_{B}"] = (lambda N, B=B: block_cycle(N, B), False)
        FAMILIES[f"rev_block_{B}"] = (lambda N, B=B: rev_block(N, B), False)
    FAMILIES["adjacent_involution"] = (adjacent_involution, False)
    FAMILIES["parity_shift"] = (parity_shift, False)
    FAMILIES["swap_at_powers"] = (swap_at_powers, False)
    FAMILIES["growing_blocks_rev"] = (lambda N: growing_blocks(N, True), False)
    FAMILIES["growing_blocks_cyc"] = (lambda N: growing_blocks(N, False), False)
    for seed in range(5):
        for B in [4, 6]:
            FAMILIES[f"random_per_{B}_{seed}"] = (
                lambda N, B=B, s=seed: random_periodic(N, B, s),
                False,
            )


register()
