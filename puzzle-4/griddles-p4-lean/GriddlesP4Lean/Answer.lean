import GriddlesP4Lean.Losing
import GriddlesP4Lean.Winning

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

end TrolleyRetrieval
