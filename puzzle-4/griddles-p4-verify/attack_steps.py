"""Steps 1-3 and m0(e) growth: where does the attack actually break?

Reframing (verified): separator at slack s=b+e
   <=> [phi(a+D) < e+delta] XOR [phi(b+D) < e].
HYP (no separator eventually) at slack s=b+e means eventually-in-D:
   [phi(a+D) < e+delta] <=> [phi(b+D) < e].          (HYP_e)

Only even s>=b are quantified. So e ranges over:
   b even: e in {0,2,4,...}
   b odd : e in {1,3,5,...}
"""

import families

FAM = families.FAMILIES


def phi(c, n):
    return c(n) - n


# ----------------------------------------------------------------------------
# m0(e): for a given (c,a,b,e), the SMALLEST D0 such that HYP_e holds for all
# D in [D0, Dmax). Returns None if HYP_e fails on a tail (separators unbounded).
def m0_of_e(c, a, b, e, Dmax, NMAX):
    delta = b - a
    last_fail = -1
    for D in range(0, Dmax):
        if a + D >= NMAX or b + D >= NMAX:
            break
        sepr = (phi(c, a + D) < e + delta) != (phi(c, b + D) < e)
        if sepr:
            last_fail = D
    # If last_fail near Dmax, likely unbounded -> None.
    if last_fail >= Dmax - max(50, Dmax // 20):
        return None  # treat as "fails on tail"
    return last_fail + 1


def m0_growth():
    print("=== (M0) m0(e) growth over e ===")
    Dmax = 20000
    NMAX = 60000
    pairs = [(1, 2), (2, 4), (1, 4), (2, 5)]
    for name in [
        "parity_shift",
        "growing_blocks_rev",
        "block_cycle_5",
        "swap_at_powers",
    ]:
        mk, _ = FAM[name]
        c, cinv, NM = mk(NMAX)
        for a, b in pairs:
            if a >= b:
                continue
            estart = 0 if b % 2 == 0 else 1
            row = []
            for e in range(estart, estart + 16, 2):
                m0 = m0_of_e(c, a, b, e, Dmax, NM)
                row.append("inf" if m0 is None else str(m0))
            print(
                f"  {name:20s} (a,b)=({a},{b}) e={list(range(estart, estart + 16, 2))}"
            )
            print(f"      m0 = {row}")


# ----------------------------------------------------------------------------
# STEP 1: e=0 residue closure of A := {n: phi(n)>=1}.
# HYP_0 (b even only): eventually [phi(a+D) < delta] <=> [phi(b+D) < 0].
# phi(b+D)<0 is "strict descent". phi(a+D)<delta. Hmm the task's e=0 form:
# task said: A:={phi>=1}, A_delta:={phi>delta}; m+delta in A <=> m in A_delta.
# That came from the OTHER reindexing. Let's just directly report what HYP_0 says
# and whether A is eventually downward-delta-closed.
def step1_residue():
    print("=== (S1) e=0 / level-set structure ===")
    NMAX = 60000
    for name in [
        "parity_shift",
        "block_cycle_5",
        "growing_blocks_rev",
        "swap_at_powers",
    ]:
        mk, _ = FAM[name]
        c, cinv, NM = mk(NMAX)
        # Report phi on residue classes mod delta for a couple deltas.
        for delta in [1, 2, 3]:
            # eventual phi values seen per residue class mod delta on a tail
            tail = range(NM - 4000, NM - 1)
            classes = {r: set() for r in range(delta)}
            for n in tail:
                classes[n % delta].add(phi(c, n))
            summary = {
                r: (
                    sorted(v)[:6]
                    if len(v) <= 12
                    else f"{len(v)} vals range[{min(v)},{max(v)}]"
                )
                for r, v in classes.items()
            }
            print(f"  {name:20s} delta={delta}: phi per residue (tail) = {summary}")


if __name__ == "__main__":
    step1_residue()
    print()
    m0_growth()
