import GriddlesP4Lean.Losing
import GriddlesP4Lean.Winning
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
  · -- Winning direction.
    intro h_not_ei
    exact NotEventuallyIdentity_wins c h_not_ei

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
