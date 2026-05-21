import GriddlesP4Lean.Parity

/-!
# Losing direction: eventually-identity permutations have no winning strategy

For `c` *eventually identity* — `c n = n` past some threshold `N` — we show that no
strategy `σ` wins from every starting cell.

## Strategy of the proof

We use the *parallel-evolution lemma*: given two starting cells `k₁ ≠ k₂`, if the signals
emitted from the two trajectories agree at every time step, then the histories agree, the
actions agree, and the positions stay offset by exactly `k₂ − k₁`.  Hence at any guess time
Bob produces the same guess for both starting cells, but the actual positions differ by
`k₂ − k₁ ≠ 0`, so the guess is wrong from at least one.

The parity invariant feeds into this by ensuring signals agree between `2j` and `2j+1`
inside the identity region.  In the non-identity region `[1, N]`, the values `c n` are all
bounded by some constant `M`; for `j` chosen large enough that the trolley only enters
the non-identity region at times `t > M`, signals are then "Yes" universally and continue
to agree.

This file proves the structural backbone: the parallel-evolution lemma and the wrap-up
that no σ can win from two cells with everywhere-equal signal traces.  The signal-match
hypothesis required to apply it to a specific eventually-identity `c` will be established
in a subsequent file.
-/

namespace TrolleyRetrieval

variable {c : Perm} {σ : Strategy}

/-! ### Parallel-evolution lemma -/

/-- **Parallel evolution.**  Suppose two starting positions `k₁, k₂ : ℤ` satisfy

* Bob never guesses before time `t` when started at `k₁`, and
* at every time `s ≤ t`, the signal emitted from `k₁`'s position equals the signal
  emitted from `k₂`'s position.

Then the histories of the two trajectories agree at time `t` and the positions differ by
exactly `k₂ − k₁`. -/
lemma parallel_evolution {k₁ k₂ : ℤ} :
    ∀ (t : ℕ),
      (∀ s, s < t → ∀ g, σ (history c σ k₁ s) ≠ .guess g) →
      (∀ s, s ≤ t →
        signalOf c (position c σ k₁ s) s = signalOf c (position c σ k₂ s) s) →
      history c σ k₁ t = history c σ k₂ t ∧
      position c σ k₂ t = position c σ k₁ t + (k₂ - k₁)
  | 0,     _,    _    => by
      refine ⟨rfl, ?_⟩
      simp [position_zero]
  | n + 1, h_ng, h_sig => by
      have ih :=
        parallel_evolution (k₁ := k₁) (k₂ := k₂) n
          (fun s hs => h_ng s (Nat.lt_succ_of_lt hs))
          (fun s hs => h_sig s (Nat.le_succ_of_le hs))
      obtain ⟨h_hist_n, h_pos_n⟩ := ih
      have h_no_guess_n : ∀ g, σ (history c σ k₁ n) ≠ .guess g :=
        h_ng n (Nat.lt_succ_self n)
      have h_action_cases :
          (∃ d, σ (history c σ k₁ n) = .move d) ∨
          (∃ g, σ (history c σ k₁ n) = .guess g) := by
        match σ (history c σ k₁ n) with
        | .move  d => exact Or.inl ⟨d, rfl⟩
        | .guess g => exact Or.inr ⟨g, rfl⟩
      rcases h_action_cases with ⟨d, hd₁⟩ | ⟨g, hg⟩
      · -- σ moves at step n.
        have hd₂ : σ (history c σ k₂ n) = .move d := by rw [← h_hist_n]; exact hd₁
        have hp₁ : position c σ k₁ (n + 1) = position c σ k₁ n + d.delta :=
          position_succ_of_move hd₁
        have hp₂ : position c σ k₂ (n + 1) = position c σ k₂ n + d.delta :=
          position_succ_of_move hd₂
        refine ⟨?_, ?_⟩
        · rw [history_succ_of_move hd₁, history_succ_of_move hd₂, h_hist_n]
          have hsig := h_sig (n + 1) (le_refl _)
          rw [hp₁, hp₂] at hsig
          rw [hsig]
        · rw [hp₁, hp₂, h_pos_n]; ring
      · -- σ guesses at step n — contradicts the no-guess hypothesis.
        exact (h_no_guess_n g hg).elim

/-! ### Conclusion -/

/-- If two starting cells `k₁ ≠ k₂` have signal traces that agree at every time step,
    no strategy can win from both. -/
theorem not_wins_from_both
    {k₁ k₂ : ℕ+} (hne : k₁ ≠ k₂)
    (h_sig : ∀ t, signalOf c (position c σ (k₁ : ℤ) t) t =
                  signalOf c (position c σ (k₂ : ℤ) t) t) :
    ¬ (WinsFrom c σ k₁ ∧ WinsFrom c σ k₂) := by
  rintro ⟨h_win₁, h_win₂⟩
  obtain ⟨T, _h_safe₁, h_no_guess₁, g₁, hg₁, hg₁_pos⟩ := h_win₁
  obtain ⟨T', _h_safe₂, h_no_guess₂, g₂, hg₂, hg₂_pos⟩ := h_win₂
  -- First, both first-guess times coincide: T = T'.
  have h_T'_le_T : T' ≤ T := by
    by_contra h_not_le
    have h_lt : T < T' := by omega
    have h_no_guess_prefix : ∀ s, s < T → ∀ g, σ (history c σ (k₂ : ℤ) s) ≠ .guess g := by
      intro s hsT
      have hsT' : s < T' := lt_trans hsT h_lt
      exact h_no_guess₂ s hsT'
    -- Parallel evolution at T (using no-guess from k₁'s side through T-1)
    have ⟨h_hist_T, _⟩ :=
      parallel_evolution (k₁ := (k₁ : ℤ)) (k₂ := (k₂ : ℤ)) T h_no_guess₁
        (fun s _ => h_sig s)
    have h_guess_at_T_from_k₂ : σ (history c σ (k₂ : ℤ) T) = .guess g₁ := by
      rw [← h_hist_T]; exact hg₁
    exact h_no_guess₂ T h_lt g₁ h_guess_at_T_from_k₂
  have h_T_le_T' : T ≤ T' := by
    by_contra h_not_le
    have h_lt : T' < T := by omega
    have ⟨h_hist_T', _⟩ :=
      parallel_evolution (k₁ := (k₁ : ℤ)) (k₂ := (k₂ : ℤ)) T'
        (fun s hs => h_no_guess₁ s (lt_trans hs h_lt))
        (fun s _ => h_sig s)
    have h_guess_at_T'_from_k₁ : σ (history c σ (k₁ : ℤ) T') = .guess g₂ := by
      rw [h_hist_T']; exact hg₂
    exact h_no_guess₁ T' h_lt g₂ h_guess_at_T'_from_k₁
  have hTT' : T = T' := le_antisymm h_T_le_T' h_T'_le_T
  -- Apply parallel evolution at T to get history- and position-relations.
  have ⟨h_hist_T, h_pos_T⟩ :=
    parallel_evolution (k₁ := (k₁ : ℤ)) (k₂ := (k₂ : ℤ)) T h_no_guess₁
      (fun s _ => h_sig s)
  -- σ's action at history-time-T from k₂ is also `.guess g₁`.
  have h_act_k₂ : σ (history c σ (k₂ : ℤ) T) = .guess g₁ := by
    rw [← h_hist_T]; exact hg₁
  -- But σ from k₂ at time T (= T') guesses g₂.
  have hg₂_at_T : σ (history c σ (k₂ : ℤ) T) = .guess g₂ := by
    rw [hTT']; exact hg₂
  have h_g_eq : g₁ = g₂ := by
    have h_act : Action.guess g₁ = Action.guess g₂ := h_act_k₂.symm.trans hg₂_at_T
    injection h_act
  -- Position-relation: position(k₂, T) = position(k₁, T) + (k₂ - k₁).
  -- Correctness from k₁ gives g₁ = position(k₁, T); from k₂ gives g₂ = position(k₂, T').
  have h_pos_k₂_at_T : (g₂ : ℤ) = position c σ (k₂ : ℤ) T := by
    rw [hTT']; exact hg₂_pos
  -- Substitute and derive k₁ = k₂.
  have h_eq : (g₁ : ℤ) = position c σ (k₁ : ℤ) T + ((k₂ : ℤ) - (k₁ : ℤ)) := by
    rw [h_g_eq, h_pos_k₂_at_T, h_pos_T]
  have h_diff_zero : ((k₂ : ℤ) - (k₁ : ℤ)) = 0 := by linarith [hg₁_pos]
  apply hne
  have h_int_eq : (k₁ : ℤ) = (k₂ : ℤ) := by linarith
  exact_mod_cast h_int_eq

end TrolleyRetrieval
