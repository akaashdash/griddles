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

/-! ### A bound for the non-identity part of `c`

For `c` that is the identity past `N`, define a uniform bound `cBound c N` such that
* `cBound c N ≥ N + 1`, and
* `(c ⟨m, _⟩).val ≤ cBound c N` for every `1 ≤ m ≤ N`.

We use this bound to show that for very large starting cells `2j > cBound c N`, signals
at any cell in `[1, N]` are universally "Yes" once `t > cBound c N`. -/

/-- Recursive bound: `cBound c n ≥ n + 1` and `cBound c n ≥ (c m).val` for every
    `1 ≤ m ≤ n`. -/
def cBound (c : Perm) : ℕ → ℕ
  | 0     => 1
  | n + 1 => (cBound c n) ⊔ (c ⟨n + 1, Nat.succ_pos n⟩).val ⊔ (n + 2)

lemma cBound_ge_succ (c : Perm) (n : ℕ) : n + 1 ≤ cBound c n := by
  induction n with
  | zero      => simp [cBound]
  | succ k ih => simp only [cBound]; omega

lemma cBound_mono (c : Perm) : ∀ {m n : ℕ}, m ≤ n → cBound c m ≤ cBound c n := by
  intro m n h
  induction n with
  | zero =>
      interval_cases m
      rfl
  | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hlt | heq
      · have hmk : m ≤ k := Nat.lt_succ_iff.mp hlt
        have := ih hmk
        simp only [cBound]
        omega
      · subst heq
        rfl

lemma cBound_apply_succ (c : Perm) (n : ℕ) :
    (c ⟨n + 1, Nat.succ_pos n⟩).val ≤ cBound c (n + 1) := by
  simp only [cBound]; omega

lemma cBound_ge (c : Perm) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    (c ⟨m, hm⟩).val ≤ cBound c n := by
  cases m with
  | zero => exact absurd hm (lt_irrefl 0)
  | succ k =>
      calc (c ⟨k + 1, Nat.succ_pos k⟩).val
          ≤ cBound c (k + 1) := cBound_apply_succ c k
        _ ≤ cBound c n        := cBound_mono c hmn

/-! ### Static signal-match -/

/-- Unfolding `signalOf` at a valid (positive) position. -/
lemma signalOf_apply {c : Perm} {p : ℤ} (h : 1 ≤ p) (t : ℕ) :
    signalOf c p t = decide ((c (Int.toPNat p h)).val < t) := by
  unfold signalOf; rw [dif_pos h]

/-- **Static signal-match.**  For an eventually-identity `c` past `N`, picking
    `j > cBound c N` ensures that at any time `t` and any position `p : ℤ` with

    * `1 ≤ p` (valid cell),
    * `2j − t ≤ p` (reachable from `2j` by step ±1 in `t` steps, so the bound applies),
    * `(t + p) % 2 = 0` (parity; this is supplied by the parity invariant),

    the signals at `p` and `p + 1` at time `t` agree. -/
lemma signal_match
    {c : Perm} {N : ℕ}
    (hN : ∀ n : ℕ+, N < n.val → c n = n)
    {j : ℕ} (hj : cBound c N < j)
    {p : ℤ} (h_p_pos : 1 ≤ p) {t : ℕ}
    (h_lower : (2 * j : ℤ) - t ≤ p)
    (h_parity : ((t : ℤ) + p) % 2 = 0) :
    signalOf c p t = signalOf c (p + 1) t := by
  have h_p1_pos : (1 : ℤ) ≤ p + 1 := by linarith
  rw [signalOf_apply h_p_pos, signalOf_apply h_p1_pos, decide_eq_decide]
  -- Useful: relate `.toNat` to the integer.
  have h_p_nn : (0 : ℤ) ≤ p := by linarith
  have h_p1_nn : (0 : ℤ) ≤ p + 1 := by linarith
  have h_p_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg h_p_nn
  have h_p1_toNat : ((p + 1).toNat : ℤ) = p + 1 := Int.toNat_of_nonneg h_p1_nn
  -- `(Int.toPNat p h).val = p.toNat` by definition.
  -- Case split on whether p > N or p ≤ N.
  by_cases h_case : (N : ℤ) < p
  · -- Case (a): p > N.  Both positions land in the identity region.
    -- Show (toPNat p).val > N and (toPNat (p+1)).val > N.
    have h_pN_gt : N < (Int.toPNat p h_p_pos).val := by
      show N < p.toNat
      have : (N : ℤ) < (p.toNat : ℤ) := by rw [h_p_toNat]; exact h_case
      exact_mod_cast this
    have h_p1N_gt : N < (Int.toPNat (p + 1) h_p1_pos).val := by
      show N < (p + 1).toNat
      have : (N : ℤ) < ((p + 1).toNat : ℤ) := by rw [h_p1_toNat]; linarith
      exact_mod_cast this
    have hc_p : c (Int.toPNat p h_p_pos) = Int.toPNat p h_p_pos := hN _ h_pN_gt
    have hc_p1 : c (Int.toPNat (p + 1) h_p1_pos) = Int.toPNat (p + 1) h_p1_pos := hN _ h_p1N_gt
    rw [hc_p, hc_p1]
    -- Now goal: (Int.toPNat p _).val < t ↔ (Int.toPNat (p+1) _).val < t
    -- i.e. p.toNat < t ↔ (p+1).toNat < t.
    show p.toNat < t ↔ (p + 1).toNat < t
    constructor
    · intro hlt
      -- p < t (as integers); want (p+1) < t.  Suffices p+1 ≠ t.
      have hp_lt : (p : ℤ) < (t : ℤ) := by
        have : (p.toNat : ℤ) < (t : ℤ) := by exact_mod_cast hlt
        rwa [h_p_toNat] at this
      have h_ne : (t : ℤ) ≠ p + 1 := by
        intro heq
        -- t = p + 1 ⇒ t + p = 2p + 1 (odd), contradicts parity.
        have : ((t : ℤ) + p) = 2 * p + 1 := by linarith
        omega
      have h_p1_lt : (p + 1 : ℤ) < (t : ℤ) := by
        have h_le : (p + 1 : ℤ) ≤ (t : ℤ) := by linarith
        exact lt_of_le_of_ne h_le (fun e => h_ne e.symm)
      have : ((p + 1).toNat : ℤ) < (t : ℤ) := by rw [h_p1_toNat]; exact h_p1_lt
      exact_mod_cast this
    · intro hlt
      -- (p+1) < t ⇒ p < t.
      have h_p1_lt : ((p + 1).toNat : ℤ) < (t : ℤ) := by exact_mod_cast hlt
      rw [h_p1_toNat] at h_p1_lt
      have h_p_lt : (p : ℤ) < (t : ℤ) := by linarith
      have : (p.toNat : ℤ) < (t : ℤ) := by rw [h_p_toNat]; exact h_p_lt
      exact_mod_cast this
  · -- Case (b): p ≤ N.  Both c-values are bounded by `cBound c N`, hence < t.
    push_neg at h_case  -- p ≤ (N : ℤ)
    have h_p_le_N : p.toNat ≤ N := by
      have : (p.toNat : ℤ) ≤ (N : ℤ) := by rw [h_p_toNat]; exact h_case
      exact_mod_cast this
    have h_p1_le_succ : (p + 1).toNat ≤ N + 1 := by
      have : ((p + 1).toNat : ℤ) ≤ ((N + 1 : ℕ) : ℤ) := by
        rw [h_p1_toNat]; push_cast; linarith
      exact_mod_cast this
    -- t > cBound c N.  Established from `h_lower`: t ≥ 2j - p ≥ 2j - N > cBound.
    have h_t_gt_cBound : cBound c N < t := by
      -- 2j - p ≤ t and p ≤ N ⇒ 2j - N ≤ t.
      have h1 : (2 * j : ℤ) - N ≤ t := by
        have : (2 * j : ℤ) - N ≤ (2 * j : ℤ) - p := by linarith
        linarith
      -- 2j > 2 cBound (since j > cBound); and cBound ≥ N+1, so 2 cBound > N + cBound.
      have h_cBound_ge_N : N + 1 ≤ cBound c N := cBound_ge_succ c N
      have h_step : (2 * (cBound c N : ℤ) + 2 - N : ℤ) ≤ (2 * j : ℤ) - N := by
        have : 2 * (cBound c N : ℤ) + 2 ≤ 2 * (j : ℤ) := by
          have : (cBound c N + 1 : ℤ) ≤ j := by exact_mod_cast hj
          linarith
        linarith
      have h_combined : (2 * (cBound c N : ℤ) + 2 - N : ℤ) ≤ t := le_trans h_step h1
      -- 2 cBound + 2 - N > cBound iff cBound + 2 > N, holds since cBound ≥ N+1 > N - 2.
      have h_bound_arith : (cBound c N : ℤ) < 2 * (cBound c N : ℤ) + 2 - N := by
        have : (N : ℤ) ≤ cBound c N := by exact_mod_cast (le_of_lt (Nat.lt_succ_iff.mp (Nat.lt_succ_of_le h_cBound_ge_N)))
        linarith
      have : (cBound c N : ℤ) < (t : ℤ) := lt_of_lt_of_le h_bound_arith h_combined
      exact_mod_cast this
    -- Both `c`-values are ≤ cBound.
    -- (c (toPNat p)).val ≤ cBound c N, since (toPNat p).val = p.toNat ≤ N.
    have h_pN_pos : 0 < p.toNat := by
      have : (0 : ℤ) < (p.toNat : ℤ) := by rw [h_p_toNat]; linarith
      exact_mod_cast this
    have h_c_p_bound : (c (Int.toPNat p h_p_pos)).val ≤ cBound c N :=
      cBound_ge c h_pN_pos h_p_le_N
    have h_p1N_pos : 0 < (p + 1).toNat := by
      have : (0 : ℤ) < ((p + 1).toNat : ℤ) := by rw [h_p1_toNat]; linarith
      exact_mod_cast this
    -- For `p+1`: if p+1 ≤ N, use cBound_ge.  If p+1 = N+1, then c(N+1) = N+1 ≤ cBound.
    have h_c_p1_bound : (c (Int.toPNat (p + 1) h_p1_pos)).val ≤ cBound c N := by
      by_cases h_p1_le : (p + 1).toNat ≤ N
      · exact cBound_ge c h_p1N_pos h_p1_le
      · push_neg at h_p1_le
        -- (p+1).toNat > N and ≤ N+1, so (p+1).toNat = N+1.
        have h_p1_eq : (p + 1).toNat = N + 1 := by omega
        -- Then c(N+1) = N+1 ≤ cBound.
        have h_NN1 : N < (Int.toPNat (p + 1) h_p1_pos).val := by
          show N < (p + 1).toNat; omega
        have hc : c (Int.toPNat (p + 1) h_p1_pos) = Int.toPNat (p + 1) h_p1_pos := hN _ h_NN1
        rw [hc]
        show (p + 1).toNat ≤ cBound c N
        rw [h_p1_eq]
        exact cBound_ge_succ c N
    -- Both signals reduce to `true`.
    constructor
    · intro _; exact lt_of_le_of_lt h_c_p1_bound h_t_gt_cBound
    · intro _; exact lt_of_le_of_lt h_c_p_bound h_t_gt_cBound

end TrolleyRetrieval
