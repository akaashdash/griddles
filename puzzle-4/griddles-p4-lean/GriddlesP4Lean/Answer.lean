import GriddlesP4Lean.Losing
import GriddlesP4Lean.WinningRestricted
import GriddlesP4Lean.WinningKProbeGen
import GriddlesP4Lean.WinningAdaptive
import GriddlesP4Lean.BandBoundedAbove
import GriddlesP4Lean.GrowStair

/-!
# Main theorem

**Puzzle 4 (Trolley Retrieval).**  Bob has a strategy to safely retrieve the trolley for
every starting cell if and only if the labelling permutation `c` is *not* eventually
identity — equivalently, `c n ≠ n` for infinitely many `n`.

The proof is complete and fully machine-verified: `#print axioms main` reports only
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
-/

namespace TrolleyRetrieval

/-- **Main theorem.**  Bob wins on the trolley-retrieval game with labelling `c` iff
    `c` is *not* eventually identity. -/
theorem main (c : Perm) : BobWins c ↔ ¬ EventuallyIdentity c := by
  constructor
  · -- Losing direction (contrapositive): an eventually-identity `c` makes the signal a mere
    -- comparison `[k₀ + D_t < t]`, whose threshold `t − D_t` can only be raised by left moves,
    -- which are unsafe while small candidates survive — so Bob can never separate `k₀` from
    -- unboundedly-large alternatives.  Proven in `Losing.lean`.
    intro h_wins h_ei
    exact EventuallyIdentity_loses c h_ei h_wins
  · -- Winning direction.  Reduces (via `localizes_BobWins`) to a fixed, signal-independent
    -- exploration trajectory that keeps displacement `≥ 0` (so position `= k₀ + D ≥ k₀ ≥ 1`,
    -- making safety automatic) and *localizes* every start cell — distinct cells get distinct
    -- signal histories by a finite time, after which Bob decodes `k₀` and guesses.  Localization
    -- needs, for every pair of cells, a separator (a reachable time where their signals differ).
    -- We dispatch on whether the displacement `(c n).val − n.val` is bounded above:
    --
    --   * BOUNDED-ABOVE → `notEI_boundedAbove_BobWins` (BandBoundedAbove).  Here a *fixed* even
    --     lag works: separators recur at unbounded displacement (`band_of_boundedAbove`, via the
    --     cut lemma `descent_cofinite_imp_EI`).  This supplies an axiom-clean `BandProvider`,
    --     fed into the parameterized band-top staircase `BobWins_of_bandProvider`.  Covers the
    --     hardest bounded examples (e.g. the parity-shift permutation).
    --   * UNBOUNDED-ABOVE → `notEI_unboundedAbove_BobWins` (GrowStair).  No fixed lag works (the
    --     lag `t − D` is monotone non-decreasing, and the required lag must grow); instead
    --     separators exist at arbitrarily large *even* lag for every pair (`q2even`), and a
    --     c-tailored GROWING-LAG staircase visits one per pair, localizing via `ofMoves_localizes`.
    --
    -- Both regimes are fixed c-tailored trajectories — no adaptive belief-state strategy is
    -- needed.  (The tempting single-fixed-lag "band recurrence" is in fact FALSE — see the
    -- AP-split counterexample — which is exactly why the dichotomy is required.)
    intro h_not_ei
    by_cases hbdd : ∃ B : ℕ, ∀ n : ℕ+, (c n).val ≤ n.val + B
    · exact notEI_boundedAbove_BobWins c h_not_ei hbdd
    · exact notEI_unboundedAbove_BobWins c h_not_ei hbdd

-- Axiom audit.  `main` is FULLY `sorry`-free: both branches are axiom-clean
-- (`[propext, Classical.choice, Quot.sound]`).  The losing direction is in `Losing.lean`; the
-- bounded-above winner routes through `band_of_boundedAbove` + the parameterized staircase, and the
-- unbounded-above winner through `q2even` + the growing-lag staircase (`GrowStair`).
#print axioms main

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
