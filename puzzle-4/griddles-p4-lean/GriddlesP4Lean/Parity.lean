import GriddlesP4Lean.Defs

/-!
# Parity invariant

The displacement `D_t = k_t − k_0` advances by `±1` each time Bob *moves*, so as long
as Bob has not yet *guessed* by time `t`, the displacement has the same parity as `t`.

This is the key obstruction used in `Losing.lean`: starting positions `2j` and `2j+1`
produce identical signal traces for every strategy because the threshold `t − D_t` is
always even.
-/

namespace TrolleyRetrieval

variable {c : Perm} {σ : Strategy}

/-- Unfolding `state` at a successor index. -/
lemma state_succ (k₀ : ℤ) (t : ℕ) :
    state c σ k₀ (t+1) =
      step c σ (position c σ k₀ t) (history c σ k₀ t) (t+1) := rfl

/-- The position after a `.move`-action transitions by `d.delta`. -/
lemma position_succ_of_move {k₀ : ℤ} {t : ℕ} {d : Dir}
    (hd : σ (history c σ k₀ t) = .move d) :
    position c σ k₀ (t+1) = position c σ k₀ t + d.delta := by
  show (state c σ k₀ (t+1)).1 = _
  rw [state_succ]
  rw [step_move _ _ _ _ _ _ hd]

/-- The position after a `.guess`-action stays put (the game has already ended). -/
lemma position_succ_of_guess {k₀ : ℤ} {t : ℕ} {g : ℕ+}
    (hg : σ (history c σ k₀ t) = .guess g) :
    position c σ k₀ (t+1) = position c σ k₀ t := by
  show (state c σ k₀ (t+1)).1 = _
  rw [state_succ]
  rw [step_guess _ _ _ _ _ _ hg]

/-- The history after one step prepends the new signal. -/
lemma history_succ_of_move {k₀ : ℤ} {t : ℕ} {d : Dir}
    (hd : σ (history c σ k₀ t) = .move d) :
    history c σ k₀ (t+1) =
      signalOf c (position c σ k₀ t + d.delta) (t+1) :: history c σ k₀ t := by
  show (state c σ k₀ (t+1)).2 = _
  rw [state_succ]
  rw [step_move _ _ _ _ _ _ hd]

lemma history_succ_of_guess {k₀ : ℤ} {t : ℕ} {g : ℕ+}
    (hg : σ (history c σ k₀ t) = .guess g) :
    history c σ k₀ (t+1) =
      signalOf c (position c σ k₀ t) (t+1) :: history c σ k₀ t := by
  show (state c σ k₀ (t+1)).2 = _
  rw [state_succ]
  rw [step_guess _ _ _ _ _ _ hg]

/-- The recurrence for displacement under a `.move`-action. -/
lemma displacement_succ_of_move {k₀ : ℤ} {t : ℕ} {d : Dir}
    (hd : σ (history c σ k₀ t) = .move d) :
    displacement c σ k₀ (t+1) = displacement c σ k₀ t + d.delta := by
  unfold displacement
  rw [position_succ_of_move hd]
  ring

/-- **Parity invariant.**  If Bob has chosen a move at every step strictly before
    time `t`, then `t − D_t` is divisible by `2`. -/
lemma displacement_parity {k₀ : ℤ} :
    ∀ (t : ℕ),
      (∀ s, s < t → ∃ d, σ (history c σ k₀ s) = Action.move d) →
      ((t : ℤ) - displacement c σ k₀ t) % 2 = 0
  | 0,     _ => by simp [displacement]
  | n + 1, h => by
    obtain ⟨d, hd⟩ := h n (Nat.lt_succ_self n)
    have ih : ((n : ℤ) - displacement c σ k₀ n) % 2 = 0 :=
      displacement_parity n (fun s hs => h s (Nat.lt_succ_of_lt hs))
    have hdisp : displacement c σ k₀ (n+1) = displacement c σ k₀ n + d.delta :=
      displacement_succ_of_move hd
    have heq :
        ((n + 1 : ℕ) : ℤ) - displacement c σ k₀ (n + 1)
          = ((n : ℤ) - displacement c σ k₀ n) + (1 - d.delta) := by
      rw [hdisp]; push_cast; ring
    rw [heq]
    have hdd : (1 - d.delta) % 2 = 0 := by
      cases d <;> simp [Dir.delta]
    omega

/-- **Useful corollary**: the threshold `t − D_t` is an *even integer*. -/
lemma even_time_sub_displacement {k₀ : ℤ} {t : ℕ}
    (h : ∀ s, s < t → ∃ d, σ (history c σ k₀ s) = Action.move d) :
    Even ((t : ℤ) - displacement c σ k₀ t) :=
  Int.even_iff.mpr (displacement_parity (σ := σ) (c := c) (k₀ := k₀) t h)

/-- *Position lower bound.*  Under the no-guess hypothesis, the position cannot drop
    below `k₀ - t`. -/
lemma position_lower_bound {k₀ : ℤ} :
    ∀ (t : ℕ),
      (∀ s, s < t → ∃ d, σ (history c σ k₀ s) = Action.move d) →
      k₀ - (t : ℤ) ≤ position c σ k₀ t
  | 0,     _ => by simp [position_zero]
  | n + 1, h => by
      obtain ⟨d, hd⟩ := h n (Nat.lt_succ_self n)
      have ih := position_lower_bound n (fun s hs => h s (Nat.lt_succ_of_lt hs))
      have hpos : position c σ k₀ (n + 1) = position c σ k₀ n + d.delta :=
        position_succ_of_move hd
      rw [hpos]
      cases d
      · simp only [Dir.delta_left]; push_cast; linarith
      · simp only [Dir.delta_right]; push_cast; linarith

end TrolleyRetrieval
