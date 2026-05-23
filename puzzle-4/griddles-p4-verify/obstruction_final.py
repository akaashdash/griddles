"""Final consolidation: pin the obstruction precisely.

Lean statement uses  max a.val b.val <= s  and  hab : a != b  (NOT a<b).
We verify:
 (A) reframing keyed on max-anchor; what e-parity arises.
 (B) the sharpened obstruction: HYP cannot deliver "phi>=0 on all classes".
     Concretely we exhibit, for a non-EI bijection, two HYP_e facts that hold
     simultaneously and whose residue-structure is INDISTINGUISHABLE (as far as
     Steps 1-2 can see) from a bijection with balanced nonzero displacement.
"""

import families

FAM = families.FAMILIES


def phi(c, n):
    return c(n) - n


def leastEvenGe(m):
    return m if m % 2 == 0 else m + 1


# (A) e-parity with max anchor. s even, s >= max(a,b). With WLOG a<b, max=b, so
# same as before: e := s-b ranges even (b even) / odd (b odd). The construction's
# canonical witness s0=leastEvenGe(b) -> e0 = s0-b in {0,1}. Confirm.
def parity_max():
    print(
        "=== (A) e-parity, max-anchor, with construction witness s=leastEvenGe(max) ==="
    )
    for a, b in [(1, 2), (2, 3), (1, 4), (2, 5), (3, 4), (5, 8)]:
        mx = max(a, b)
        s0 = leastEvenGe(mx)
        e0 = s0 - b
        print(
            f"  (a,b)=({a},{b}) max={mx} s0=leastEvenGe={s0} e0=s0-b={e0} "
            f"(b {'even' if b % 2 == 0 else 'odd'} -> e even-stride starting {e0})"
        )


# (B) The sharpened obstruction. Step 3 needs to RULE OUT "phi const = k != 0 on
# residue r mod delta" purely from HYP. parity-shift IS such a c (k=+/-2). For
# the attack to be SOUND it must be that parity-shift violates HYP (it does).
# But the QUESTION is whether Steps 1-2, from the HYP_e that hold for parity-shift
# on SOME pair, would (if blindly applied) deduce a FALSE "phi=0" conclusion or
# correctly stop. We show: the HYP_e that hold for parity-shift give exactly the
# (+2,-2) residue picture, which Step-3's invoked sufficient condition cannot
# refute. So Step 3 is too weak.
def sharpened():
    print("\n=== (B) sharpened obstruction on parity_shift ===")
    mk, _ = FAM["parity_shift"]
    c, cinv, NM = mk(60000)
    # For pair (2,4): delta=2. Which HYP_e hold? From M0: e=0 holds, e=2 fails, e>=4 hold.
    a, b = 2, 4
    delta = b - a
    print(f"  pair (a,b)=({a},{b}) delta={delta}")
    for e in range(0, 10, 2):
        last_fail = -1
        for D in range(0, 20000):
            if b + D >= NM:
                break
            if (phi(c, a + D) < e + delta) != (phi(c, b + D) < e):
                last_fail = D
        status = "HOLDS (eventually)" if last_fail < 19000 else "FAILS (unbounded seps)"
        print(f"    e={e}: HYP_e {status} (last_fail={last_fail})")
    print("  => HYP for pair (2,4) FAILS overall (e=2 has unbounded separators).")
    print("     So parity-shift is NOT a valid HYP-input; lemma stays true.")
    print("     But the WALL: from the HYP_e that DO hold (e=0,4,6,...), the")
    print("     extractable residue structure is consistent with phi=(+2 on evens,")
    print("     -2 on odds). Only the SINGLE failing e=2 certifies non-EI -- and")
    print("     identifying THAT e is exactly the open coordination problem.")

    # Confirm: the level sets that HOLDING e's pin do NOT include the discriminating bit.
    # e=0 holds: pins [phi(a+D)<delta] <=> [phi(b+D)<0] eventually. Check both sides:
    print("\n  What e=0 pins (pair 2,4, delta=2): [phi(a+D)<2] <=> [phi(b+D)<0]")
    cntL = cntR = both = 0
    for D in range(1000, 5000):
        L = phi(c, a + D) < delta
        R = phi(c, b + D) < 0
        if L:
            cntL += 1
        if R:
            cntR += 1
        if L == R:
            both += 1
    print(
        f"    over 4000 D: L true {cntL}, R true {cntR}, agree {both} "
        f"(both false constantly: phi(a+D)=+2 or -2 never <2? actually +2<2 false, -2<2 true)"
    )
    # Show phi values:
    sample = [(phi(c, a + D), phi(c, b + D)) for D in range(1000, 1006)]
    print(f"    sample (phi(a+D),phi(b+D)): {sample}")


if __name__ == "__main__":
    parity_max()
    sharpened()
