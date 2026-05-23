"""Step 3 (cut-balance) + the parity-shift misfire test.

Goal: determine whether the attack's reasoning, run as a PURE deduction from the
HYP_e facts that DO hold, can wrongly conclude EI on a genuinely non-EI bijection.

Key insight on the contrapositive logic:
  - The attack ASSUMES HYP (all even s>=b: HYP_s holds eventually) and derives EI.
  - For the attack to be SOUND, on any non-EI c the hypothesis HYP must FAIL
    (some even s>=b has separators at unbounded D). That's the lemma -- true.
  - The DANGER (soundness gap in the *attack's steps*) is: a step that, from the
    SUBSET of HYP_e that happen to hold, concludes structure that already implies
    EI -- meaning that step is using more than HYP gives, OR is just false.

We test the parity-shift, where the M0 table shows a rich pattern of which
HYP_e hold. We ask: do Steps 1-2 (residue/level-set pinning), applied to the
HYP_e that hold, conclude "phi eventually 0 on residue classes"? If they would,
that's WRONG (phi is +/-2), so the step is unsound.
"""

import families

FAM = families.FAMILIES


def phi(c, n):
    return c(n) - n


# ----------------------------------------------------------------------------
# (S3) cut identity B(N) := |{n<=N: c(n)>N}| = |{n>N: c(n)<=N}|, and EI<=>B(N)=0 ev.
def cut_check():
    print("=== (S3) cut identity B(N) and EI<=>B(N)=0 ===")
    NMAX = 60000
    for name in [
        "parity_shift",
        "block_cycle_5",
        "growing_blocks_rev",
        "swap_at_powers",
        "identity",
    ]:
        mk, is_ei = FAM[name]
        c, cinv, NM = mk(NMAX)
        bad = 0
        Bvals = []
        for N in range(1, min(NM - 1, 4000)):
            left = sum(1 for n in range(1, N + 1) if c(n) > N)
            # right: n>N with c(n)<=N. Need c on n>N; count via inverse on values<=N.
            right = sum(1 for v in range(1, N + 1) if cinv(v) > N)
            if left != right:
                bad += 1
            Bvals.append(left)
        tailB = Bvals[-2000:]
        print(
            f"  {name:20s} identity-match: B(N)==right always? {bad == 0};  "
            f"B(N) tail max={max(tailB)} min={min(tailB)} -> grows? "
            f"{'yes' if max(tailB) > max(Bvals[:200] or [0]) else 'bounded'}  is_ei={is_ei}"
        )


# ----------------------------------------------------------------------------
# THE PARITY-SHIFT MISFIRE TEST.
# parity_shift: phi == +2 on evens (residue 0 mod 2), phi == -2 on odds (residue 1 mod 2).
# Bijective, non-EI, B(N) bounded.  Step 3 claims "phi const nonzero on a residue
# class mod delta contradicts bijectivity via cut-balance" -> FALSE here (it balances).
def parity_shift_step3():
    print("\n=== parity-shift: Step-3 premise check ===")
    mk, _ = FAM["parity_shift"]
    c, cinv, NM = mk(60000)
    delta = 2  # pair like (2,4) has delta=2
    for r in range(delta):
        vals = set(phi(c, n) for n in range(NM - 4000, NM - 1) if n % delta == r)
        print(f"  residue {r} mod {delta}: phi eventual values = {sorted(vals)}")
    print("  => phi is constant NONZERO on each residue class mod 2, yet c is a")
    print(
        "     bijection (cut-balance B(N) bounded). Step-3 'nonzero const => contradiction'"
    )
    print("     is FALSE: the +2 class and -2 class balance each other.")

    # Now: which HYP_e actually HOLD for parity-shift, pair (2,4)? From M0: e in
    # {0,4,6,8,...} hold (m0=0), e=2 FAILS (separators unbounded).
    # So HYP for pair (2,4) does NOT hold (e=2 fails) -> lemma hypothesis violated -> OK, no misfire on (2,4).
    # The real soundness question: is there ANY pair where ALL even e>=... hold yet non-EI?
    # That would be a counterexample to the LEMMA itself. Test exhaustively below.


def lemma_truth_scan():
    """For each non-EI family, find whether SOME even s>=max(a,b) gives unbounded
    separators (lemma's contrapositive). If for some pair ALL even s>=max have
    finite m0 (HYP holds) but c non-EI, the LEMMA is false. Scan widely."""
    print("\n=== LEMMA truth scan: does HYP fail for every non-EI family/pair? ===")
    NMAX = 80000
    Dmax = 25000
    counter = 0
    checked = 0
    for name, (mk, is_ei) in FAM.items():
        if is_ei:
            continue
        c, cinv, NM = mk(NMAX)
        for a in range(1, 7):
            for b in range(a + 1, 9):
                mx = max(a, b)
                # even s >= mx
                s0 = mx if mx % 2 == 0 else mx + 1
                hyp_holds_all = True
                some_unbounded = False
                for s in range(s0, s0 + 20, 2):
                    e = s - b
                    # count separators on tail
                    last_fail = -1
                    for D in range(0, Dmax):
                        if a + D >= NM or b + D >= NM:
                            break
                        sepr = (phi(c, a + D) < e + (b - a)) != (phi(c, b + D) < e)
                        if sepr:
                            last_fail = D
                    if last_fail >= Dmax - 200:
                        some_unbounded = True
                        hyp_holds_all = False
                        break
                checked += 1
                if hyp_holds_all:
                    counter += 1
                    print(
                        f"  !! POSSIBLE LEMMA COUNTEREXAMPLE: {name} (a,b)=({a},{b}) "
                        f"HYP holds for all even s in [{s0},{s0 + 18}] yet non-EI"
                    )
    print(
        f"  checked {checked} (family,pair) combos; possible-counterexamples={counter}"
    )
    print(
        "  (0 => lemma empirically holds: every non-EI pair has some unbounded slack)"
    )


if __name__ == "__main__":
    cut_check()
    parity_shift_step3()
    lemma_truth_scan()
