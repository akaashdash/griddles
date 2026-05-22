import GriddlesP4Lean.Parity

/-!
# Winning direction (restricted): a complete strategy under a discriminability hypothesis

The general winning direction (`¬ EventuallyIdentity c → BobWins c`) needs the full
`LemmaA` (including the research-level `Δ ≥ 2` value-hogging argument).  Here we instead
prove a *complete, sorry-free* winning theorem under an explicit hypothesis that supplies
the Phase-2 discriminator directly — capturing the entire game-strategy plumbing
(adaptive Phase 1 + Phase 2 navigation + safety + timing), which is the substantial part.

## The strategy

* **Phase 1.**  Bob oscillates `D_t ∈ {0,1}` (right on even decision times, left on odd).
  At even time `t = 2m` the position is exactly `k₀`, so the signal is `c(k₀) < 2m`.  The
  first "Yes" at an even time `2m*` reveals `c k₀ ∈ {2m*−2, 2m*−1}`, narrowing `k₀` to two
  candidates `p₁ = c⁻¹(2m*−2)`, `p₂ = c⁻¹(2m*−1)`.

* **Phase 2.**  The hypothesis hands Bob a displacement `D` and time `T` (with `T ≥ T₁`,
  parity-consistent) at which the signals from `p₁` and `p₂` differ.  Bob navigates right to
  displacement `D`, reads the signal at `T`, deduces `k₀`, and guesses its position.

This file builds the pieces bottom-up.  First: the Phase-1 oscillation behaviour.
-/

namespace TrolleyRetrieval

variable {c : Perm}

/-- Phase-1 oscillation direction at decision time `t`: right on even, left on odd.
    This keeps the displacement in `{0, 1}` and returns to `k₀` at every even time. -/
def oscDir (t : ℕ) : Dir := if t % 2 = 0 then .right else .left

/-- The pure oscillation strategy (Phase 1 in isolation): always move, never guess. -/
def oscStrat : Strategy := fun h => Action.move (oscDir h.length)

/-- Under any strategy that never guesses, the history length equals the time. -/
lemma history_length_oscStrat (k₀ : ℤ) :
    ∀ t : ℕ, (history c oscStrat k₀ t).length = t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
      have hmove : oscStrat (history c oscStrat k₀ n) = .move (oscDir n) := by
        simp only [oscStrat, ih]
      rw [history_succ_of_move hmove, List.length_cons, ih]

/-- **Phase-1 position.**  Under the oscillation strategy, the position at time `t` is
    `k₀ + (t % 2)`: exactly `k₀` at even times, `k₀ + 1` at odd times. -/
lemma position_oscStrat (k₀ : ℤ) :
    ∀ t : ℕ, position c oscStrat k₀ t = k₀ + (t % 2 : ℕ) := by
  intro t
  induction t with
  | zero => simp [position_zero]
  | succ n ih =>
      have hlen : (history c oscStrat k₀ n).length = n := history_length_oscStrat k₀ n
      have hmove : oscStrat (history c oscStrat k₀ n) = .move (oscDir n) := by
        simp only [oscStrat, hlen]
      rw [position_succ_of_move hmove, ih]
      -- goal: k₀ + (n % 2) + (oscDir n).delta = k₀ + ((n+1) % 2)
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- n even
        have h1 : n % 2 = 0 := by omega
        have h2 : (n + 1) % 2 = 1 := by omega
        have h3 : oscDir n = .right := by simp [oscDir, h1]
        rw [h1, h2, h3]
        push_cast
        simp [Dir.delta]
      · -- n odd
        have h1 : n % 2 = 1 := by omega
        have h2 : (n + 1) % 2 = 0 := by omega
        have h3 : oscDir n = .left := by simp [oscDir, h1]
        rw [h1, h2, h3]
        push_cast
        simp [Dir.delta]

/-- Phase-1 safety: the oscillation never falls off (position stays `≥ k₀ ≥ 1`). -/
lemma position_oscStrat_pos (k₀ : ℕ+) (t : ℕ) :
    1 ≤ position c oscStrat (k₀ : ℤ) t := by
  rw [position_oscStrat]
  have hk : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.property
  have : (0 : ℤ) ≤ ((t % 2 : ℕ) : ℤ) := by positivity
  linarith

/-- `Int.toPNat` is a left inverse of the `ℕ+ → ℤ` coercion. -/
lemma toPNat_coe (k : ℕ+) (h : (1 : ℤ) ≤ (k : ℤ)) : Int.toPNat (k : ℤ) h = k := by
  apply Subtype.ext
  show (k : ℤ).toNat = k.val
  simp

/-- At even times, the position is exactly `k₀`. -/
lemma position_oscStrat_even (k₀ : ℕ+) (t : ℕ) (ht : t % 2 = 0) :
    position c oscStrat (k₀ : ℤ) t = (k₀ : ℤ) := by
  rw [position_oscStrat, ht]; simp

/-- **Phase-1 signal at even times.**  The signal emitted at an even time `t` is exactly
    `c(k₀) < t` — Bob is probing the label of his own (unknown) starting cell. -/
lemma signal_even_oscStrat (k₀ : ℕ+) (t : ℕ) (ht : t % 2 = 0) :
    signalOf c (position c oscStrat (k₀ : ℤ) t) t = decide ((c k₀).val < t) := by
  rw [position_oscStrat_even k₀ t ht]
  have hk : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.property
  rw [signalOf, dif_pos hk, toPNat_coe k₀ hk]

/-- **Phase-1 signal at odd times.**  The signal emitted at an odd time `t` probes the
    label of the cell *next to* the start: `c(k₀ + 1) < t`. -/
lemma signal_odd_oscStrat (k₀ : ℕ+) (t : ℕ) (ht : t % 2 = 1) :
    signalOf c (position c oscStrat (k₀ : ℤ) t) t = decide ((c (k₀ + 1)).val < t) := by
  have hpos : position c oscStrat (k₀ : ℤ) t = ((k₀ + 1 : ℕ+) : ℤ) := by
    rw [position_oscStrat, ht]
    push_cast
    ring
  rw [hpos]
  have hk : (1 : ℤ) ≤ ((k₀ + 1 : ℕ+) : ℤ) := by exact_mod_cast (k₀ + 1).property
  rw [signalOf, dif_pos hk, toPNat_coe (k₀ + 1) hk]

end TrolleyRetrieval
