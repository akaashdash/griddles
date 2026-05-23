"""Nail the 'S finite => EI' contradiction PRECISELY.

S = {D : c(b+D) > b+D AND |c(a+D)-c(b+D)| >= 2}.   M = b (a<b).

Strict ascents of b: E = {D : c(b+D) > b+D}.  PROVABLY infinite (bijectivity).

Suppose S finite. Then cofinitely many D in E have |c(a+D)-c(b+D)| = 1.
Set n = b+D (ranges over the b-ray, cofinite in E). For such n:
  c(n) > n  (strict ascent), and  c(n - delta) = c(n) +- 1   where delta = b-a, a+D = n-delta.

KEY new idea (avoid the broken walk argument):  Use phi(m) = c(m) - m in [-B, B].
For n in E (cofinite), c(n)=c(n-delta) -+ 1 hmm let's write it as:
   c(n-delta) - c(n) in {-1, +1}.
   phi(n-delta) - phi(n) = (c(n-delta) - c(n)) - (n-delta - n) = (c(n-delta)-c(n)) + delta.
   So phi(n-delta) - phi(n) in {delta-1, delta+1}.
   Since delta>=1: delta-1>=0, delta+1>=2.
   For delta>=2 BOTH are >=1, so phi(n-delta) >= phi(n)+1 STRICTLY.   <-- this is the chain
   For delta=1: phi(n-1)-phi(n) in {0, 2}, so phi(n-1) >= phi(n) (non-strict). Need more care.

CLAIM for delta>=2: along any single residue class mod delta intersect E (cofinite),
phi strictly DECREASES as n increases (phi(n) <= phi(n-delta)-1). But phi >= -B bounded below.
Since E is infinite, SOME residue class r mod delta contains infinitely many n in E.
Order them n_1<n_2<...; consecutive ones differ by a multiple of delta. BUT the gap=1 relation
only relates n and n-delta, BOTH of which must be such that n in E AND the gap holds at n.
n-delta need NOT be in E. So the chain phi(n)<phi(n-delta) requires the relation to hold at n only.

Reframe via cofinitely_bad_impossible on cell a:
  We have c(n)>n at n in E (cofinite gap=1).  c(n-delta)=c(a+D)= c(n) +- 1 > n - 1 >= n-delta + (delta-1).
  So c(a+D) = c(n-delta) >= c(n)-1 > n-1, i.e. c(a+D) > a+D + (delta-1) -1?? recompute:
  c(a+D) >= c(n)-1 >= (n+1)-1 = n = a+D+delta.  So phi(a+D) >= delta. BIG ASCENT at a.

So: S finite => cofinitely many D in E have phi(a+D) >= delta >= 1, i.e. c(a+D) >= a+D+delta = b+D... wait
  c(a+D) >= n = b+D.  Combined with c(b+D) > b+D and c(a+D) = c(b+D) +-1:
  if c(a+D)=c(b+D)-1 >= b+D then c(b+D) >= b+D+1 (consistent). if c(a+D)=c(b+D)+1.

Let me just MEASURE: under S-finite hypothesis (cofinite gap=1 on E), what does phi(a+D) do?
And test the chain contradiction for delta>=2 by checking phi is forced unbounded if E-residue chains link up.

The REAL question: does 'gap=1 cofinitely on E' actually happen for ANY bounded non-EI c?
If NEVER (because it forces EI), then S is infinite. Let's CONSTRUCT a would-be counterexample
and see it must be EI.
"""

from families import FAMILIES


def make_c(fn, NMAX):
    return fn(NMAX)


def measure_phi_a_on_gap1_E(c, a, b, n):
    """For D in E with gap==1, record phi(a+D) and phi(b+D). Check the derived inequalities."""
    delta = b - a
    Dmax = n - b - 1
    recs = []
    for D in range(Dmax):
        cb = c(b + D)
        if cb > b + D:  # E
            ca = c(a + D)
            if abs(ca - cb) == 1:  # gap1
                phi_a = ca - (a + D)
                phi_b = cb - (b + D)
                recs.append((D, phi_a, phi_b, ca - cb))
    return recs, delta


def main():
    NMAX = 30000
    print("=== measure phi(a+D) on gap1-E displacements (S-finite witnesses) ===")
    print("checking derived claim: gap1 & strict-asc-b => phi(a+D) >= delta")
    for name, (fn, is_ei) in FAMILIES.items():
        if is_ei or name.startswith("growing"):
            continue
        for a, b in [(1, 2), (2, 3), (1, 3), (1, 4), (2, 5)]:
            c, cinv, n = make_c(fn, NMAX)
            recs, delta = measure_phi_a_on_gap1_E(c, a, b, n)
            if not recs:
                continue
            phis_a = [r[1] for r in recs]
            minphi = min(phis_a)
            maxphi = max(phis_a)
            # claim: phi_a >= delta on ALL gap1-E
            viol = sum(1 for p in phis_a if p < delta)
            print(
                f"  {name:18s}(a={a},b={b},d={delta}): #gap1E={len(recs):6d} "
                f"phi_a in [{minphi},{maxphi}] viol(phi_a<delta)={viol}"
            )


if __name__ == "__main__":
    main()
