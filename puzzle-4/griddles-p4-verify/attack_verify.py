"""Verify the proposed attack on noSeparator_allSlack_imp_eventuallyIdentity.

The lemma (contrapositive form / "band recurrence"):
  c bijection of N+, a<b, delta=b-a, phi(n)=c(n)-n.
  HYP: for every EVEN s>=b, eventually (all large D) [c(a+D)<D+s] <=> [c(b+D)<D+s].
  Then c is eventually identity.

Contrapositive (what the construction needs): if c NOT eventually identity, then
  there is an even s>=b (actually >= max(a,b)) with separators at unbounded D, i.e.
  the iff FAILS at unbounded D.

We verify:
  (R) the (★) crossing-distance reframing, tracking parity of b.
  (S1) e=0 residue closure of A := {phi>=1}.
  (S2) whether Steps 1-2 pin phi to residue-constants.
  (S3) cut identity B(N) and EI<=>B(N)=0; Step-3 contradiction.
  (M0) m0(e) growth obstruction.
"""

import families

FAM = families.FAMILIES


def sep_at_slack(c, a, b, s, D):
    """separatorAtSlack: [c(a+D)<D+s] != [c(b+D)<D+s]."""
    return (c(a + D) < D + s) != (c(b + D) < D + s)


def iff_holds(c, a, b, s, D):
    """The HYP iff at slack s, disp D: [c(a+D)<D+s] <=> [c(b+D)<D+s]."""
    return (c(a + D) < D + s) == (c(b + D) < D + s)


# ----------------------------------------------------------------------------
# (R) Verify the crossing-distance reframing.
# Claim from task: with separator at slack s = b + e (e := s - b),
#   separator <=> [phi(b+D) > e] XOR [phi(a+D) > e + delta].
# Let's verify DIRECTLY in the (a,b,D) coordinates (no reindex m), since the
# Lean lemma is in these coordinates. phi(n) = c(n)-n.
# c(a+D) < D+s  <=>  c(a+D)-(a+D) < D+s-(a+D) = s-a-D+D ... wait recompute.
#   c(a+D) < D+s  <=> phi(a+D) + (a+D) < D+s <=> phi(a+D) < s - a.
#   c(b+D) < D+s  <=> phi(b+D) < s - b.
# So separator <=> [phi(a+D) < s-a] XOR [phi(b+D) < s-b].
# With s = b+e: s-a = b+e-a = e+delta; s-b = e.  delta = b-a.
# separator <=> [phi(a+D) < e+delta] XOR [phi(b+D) < e].
# Negate both to ">=": [phi(a+D) >= e+delta] XOR [phi(b+D) >= e]   (XOR preserved under double-negation of both args).
# The task wrote [phi(m+δ)>e] XOR [phi(m)>e+δ] -- with m=a+D, m+δ=b+D, and
#   ">" vs ">=" and the +delta on which side. Let's just verify our derived form.
def reframe_check():
    print("=== (R) crossing-distance reframing ===")
    bad = 0
    total = 0
    for name, (mk, is_ei) in FAM.items():
        c, cinv, NMAX = mk(40000)
        delta_pairs = [(1, 4), (2, 5), (3, 4), (1, 2), (2, 4), (5, 9)]
        for a, b in delta_pairs:
            if b > a is False:
                continue
            if a >= b:
                continue
            delta = b - a
            for e in range(0, 8):
                s = b + e
                for D in range(0, 300):
                    if b + D >= NMAX or a + D >= NMAX:
                        break
                    lhs = sep_at_slack(c, a, b, s, D)
                    pa = c(a + D) - (a + D)
                    pb = c(b + D) - (b + D)
                    rhs = (pa < e + delta) != (pb < e)
                    total += 1
                    if lhs != rhs:
                        bad += 1
                        if bad <= 3:
                            print(
                                f"  MISMATCH {name} (a,b)=({a},{b}) e={e} D={D}: lhs={lhs} rhs={rhs}"
                            )
    print(f"  checked {total}, mismatches {bad}")
    return bad


# ----------------------------------------------------------------------------
# Parity dependence of e: s even, s >= b.  e = s - b.
#   e even  <=> s and b same parity.  s even, so e even <=> b even.
def parity_check():
    print("=== parity of e := s-b over even s>=b ===")
    for b in [2, 3, 4, 5]:
        evens = [s for s in range(b, b + 12) if s % 2 == 0]
        es = [s - b for s in evens]
        print(
            f"  b={b}: even s>=b -> e values {es}  (e parity = {'even' if b % 2 == 0 else 'odd'})"
        )


if __name__ == "__main__":
    parity_check()
    reframe_check()
