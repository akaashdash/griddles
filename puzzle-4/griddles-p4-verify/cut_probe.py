import sys

import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from families import FAMILIES

# Cut identity: psi(N) = |{n<=N : c(n)>N}| = |{n>N : c(n)<=N}|.
# EI <=> psi(N)=0 for all large N (easy direction: EI => c(n)=n>N for n>N so {n>N:c(n)<=N}=empty).
# Test the identity, and test whether psi is BOUNDED (it need not ->0 for non-EI; e.g. growing blocks).


def psi(c, cinv, N):
    # |{n<=N : c(n)>N}|
    left = sum(1 for n in range(1, N + 1) if c(n) > N)
    right = sum(
        1 for n in range(N + 1, N + N + 50) if c(n) <= N
    )  # n>N with c(n)<=N; bounded scan
    return left, right


def test(fname, NMAX=20000):
    builder, isEI = FAMILIES[fname]
    c, cinv, n = builder(NMAX)
    Nlim = n
    ids_ok = True
    psis = []
    for N in range(10, min(Nlim - 200, 5000)):
        l, r = psi(c, cinv, N)
        if l != r:
            ids_ok = False
            print(f"  IDENTITY FAIL {fname} N={N}: left={l} right={r}")
            break
        psis.append(l)
    return ids_ok, (max(psis) if psis else None), psis[-20:] if psis else []


if __name__ == "__main__":
    for fname in [
        "identity",
        "parity_shift",
        "adjacent_involution",
        "growing_blocks_rev",
        "block_cycle_5",
        "swap_at_powers",
        "rev_block_5",
    ]:
        ok, mx, tail = test(fname)
        print(f"{fname:22s}: identity_holds={ok} max_psi={mx} psi_tail={tail}")
