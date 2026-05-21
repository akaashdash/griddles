import GriddlesP4Lean.LemmaA
import GriddlesP4Lean.Parity

/-!
# Winning direction: non-eventually-identity permutations admit a winning strategy

For `c` *not* eventually identity, we construct a two-phase strategy that wins from every
starting cell:

**Phase 1.**  Bob oscillates `D_t ∈ {0, 1}` by moving right-then-left repeatedly.  At each
even time `t = 2m`, the position equals `k₀`, so the signal "Yes" iff `(c k₀).val < 2m`.
The first "Yes" at time `2m*` reveals `c k₀ ∈ {2m* − 2, 2m* − 1}`, narrowing `k₀` to at
most two candidates `{p₁, p₂} = {c⁻¹(2m*−2), c⁻¹(2m*−1)}`.

**Phase 2.**  By `LemmaA`, a non-eventually-identity permutation admits a *discriminator*
for every pair `(p₁, p₂)`: a displacement `D` and time `t` for which the signals at
positions `p₁ + D` and `p₂ + D` at time `t` differ.  Bob navigates to displacement `D`
at time `t` (with safety preserved since `D > 0` for the discriminator that LemmaA picks),
observes which signal fires, and guesses the corresponding position.

## Status

This file currently states the headline theorem but defers the construction of the
explicit strategy.  Completing it requires (i) building Phase 1 + Phase 2 as a single
strategy function, (ii) discharging the safety obligations under the parity invariant,
and (iii) plugging in `LemmaA`.
-/

namespace TrolleyRetrieval

/-- **Main theorem (winning direction).**  If `c` is *not* eventually identity, then
    Bob has a winning strategy. -/
theorem NotEventuallyIdentity_wins (c : Perm) (h : ¬ EventuallyIdentity c) :
    BobWins c := by
  sorry

end TrolleyRetrieval
