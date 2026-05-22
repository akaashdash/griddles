import GriddlesP4Lean.Losing
import GriddlesP4Lean.WinningRestricted
import GriddlesP4Lean.WinningKProbeGen

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
  · -- Winning direction. **OPEN** — the explicit *uniform* winning strategy.
    --
    -- WHAT IS PROVEN (axiom-clean):
    --   * `not_eventually_identity_implies_distinguishable` (LemmaA): ¬EI ⟹ every pair `(a,b)`
    --     has a *reachable discriminator* `(D, t)` (`D ≥ 0`, `t ≥ D`, `t ≡ D (mod 2)`, signals
    --     differ). This is the abstract distinguishability — the part long thought research-level.
    --   * Three concrete winning classes via the period-`2K` triangle sweep:
    --       `LocallyDecodable_BobWins`   (K=2, WinningRestricted),
    --       `LocallyK3Decodable_BobWins` (K=3, WinningKProbe),
    --       `LocallyKDecodable_BobWins`  (arbitrary K : ℕ+, WinningKProbeGen).
    --     Each: oscillate/sweep with amplitude `K`, read the `K+1` per-displacement first-"Yes"
    --     thresholds `upThr v K (c (k₀+v))`, decode `k₀`, guess. Strictly broadens with `K`
    --     (e.g. reverse-block-5 needs `K=4`).
    --
    -- THE PRECISE REMAINING OBSTACLE (verified by exact-dynamics simulation):
    --   The triangle-sweep architecture canNOT cover all non-EI `c`. A deterministic amplitude-`K`
    --   sweep's *entire* observable is its signal history, which (since `D_t` is a function of `t`)
    --   equals the `K+1`-tuple of per-displacement first-"Yes" times. So the sweep distinguishes
    --   `k₀` from `k₀'` iff that tuple differs — i.e. iff `c` is `LocallyKDecodable`.
    --
    --   WITNESS that no fixed `K` suffices: the **block-5 cycle** `c` (rotate each `{5b+1,…,5b+5}`
    --   forward) is non-EI, yet for EVERY `K` SOME pair of cells produces the IDENTICAL threshold
    --   tuple (so the sweep cannot distinguish them). Checked exhaustively for `K = 1..50`:
    --   block-5 is never `LocallyKDecodable`. For every `K ≥ 4` the colliding pair is `(4, 5)`:
    --   `c(4..9)=[5,1,7,8,9,10]`, `c(5..10)=[1,7,8,9,10,6]`, and at e.g. `K=5` both give the
    --   upswing-threshold tuple `(10,11,12,13,14,15)` (hence byte-identical histories).
    --   (LemmaA still distinguishes `(4,5)`: there is a reachable discriminator at displacement
    --   `D=0`, time `t=2` — `c(4)=5 ≥ 2` but `c(5)=1 < 2`, an *early wake at the start cell*. A
    --   `K=2` sweep, which samples `D=0` every other tick, catches it; but a large-`K` sweep
    --   samples `D=0` only once per `2K` ticks and rounds that early wake up to the same coarse
    --   threshold for both cells. One trajectory cannot finely monitor all displacements at once:
    --   this is the genuine timing/resolution tension that defeats the fixed-`K` architecture.)
    --
    -- CONCLUSION: closing this `sorry` requires a winning strategy that is NOT a fixed-amplitude
    -- triangle sweep (candidates: a fine small-amplitude core interleaved with periodic far
    -- excursions, or an adaptive belief-shrinking walk). LemmaA guarantees every non-EI `c` has,
    -- for every candidate pair, a reachable discriminator — so the information to win is always
    -- present; what is open is packaging it into one explicit, provably-complete *uniform*
    -- strategy. (The `→` direction of `main` is the open piece; the `←` losing direction is
    -- proven in `Losing.lean`, and the K-decodable classes above settle wide subclasses of `→`.)
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
