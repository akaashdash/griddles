import GriddlesP4Lean.Losing
import GriddlesP4Lean.WinningRestricted

/-!
# Main theorem

**Puzzle 4 (Trolley Retrieval).**  Bob has a strategy to safely retrieve the trolley for
every starting cell if and only if the labelling permutation `c` is *not* eventually
identity — equivalently, `c n ≠ n` for infinitely many `n`.
-/

namespace TrolleyRetrieval

/-- **Main theorem.**  Bob wins on the trolley-retrieval game with labelling `c` iff
    `c` is *not* eventually identity. -/
theorem main (c : Perm) : BobWins c ↔ ¬ EventuallyIdentity c := by
  constructor
  · -- Losing direction (contrapositive).
    intro h_wins h_ei
    exact EventuallyIdentity_loses c h_ei h_wins
  · -- Winning direction. **OPEN.**
    -- RETRACTED (2026-05): the "monotone-right" strategy and its lemma `restricted_separation`
    -- were FALSE — `blkPerm` (block 3-cycle, non-EI, Bob-win) is a counterexample: with
    -- `c n ≤ n+1`, every rightward probe `[c(p+D) < T₁+D]` is vacuously true, so the two
    -- Phase-1 candidates are never separated by rightward probes alone. Bob actually wins it
    -- via the *odd-time* detector (an early wake-up at `t=3`), which the monotone-right strategy
    -- arrives too late to see. The correct route is the abstract `LemmaA`
    -- (`Indistinguishable c a b → … EventuallyIdentity`; it captures ALL reachable `t ≥ |D|`
    -- discriminators, including early wakes) plus a uniform "reach-the-discriminator" strategy.
    -- That lemma's `Δ ≥ 2` case (`odd_good_pair_gap`) and the strategy plumbing remain open.
    intro h_not_ei
    sorry

/-- **Capstone for the locally-decodable class** (fully `sorry`-free).  Connecting the
    machine-checked losing direction with the restricted winning theorem: every locally
    decodable permutation is a Bob-win *and* is necessarily not eventually identity.

The second conjunct is forced: were a locally-decodable `c` eventually identity, the losing
direction would give `¬ BobWins c`, contradicting the restricted winning theorem.  So this
also confirms the two verified halves are mutually consistent. -/
theorem locallyDecodable_main (c : Perm) (h : LocallyDecodable c) :
    BobWins c ∧ ¬ EventuallyIdentity c :=
  ⟨LocallyDecodable_BobWins c h,
   fun hEI => EventuallyIdentity_loses c hEI (LocallyDecodable_BobWins c h)⟩

end TrolleyRetrieval
