import GriddlesP4Lean.Defs
import Mathlib.Data.PNat.Interval

/-!
# Lemma A: distinguishability lemma

For a permutation `c : ℕ+ ≃ ℕ+` and two starting cells `a < b`, we say the pair is
*indistinguishable* if, at every reachable `(D, t)`, the signals from the two trajectories
agree.

**Lemma A.**  An indistinguishable pair exists iff `c` is eventually identity (and then
necessarily `b = a + 1`).

The forward direction is the heart of the winning argument: contrapositively, *if `c` is
not eventually identity, every pair of cells is distinguishable*.

## Proof sketch

From `Indistinguishable c a b`, for every `D` such that both `c (a+D)` and `c (b+D)` are
`≥ D` (which holds for all but finitely many `D`), the analysis of the signal-traces
forces:

* `c (a + D)` and `c (b + D)` are consecutive integers, and
* `min(c (a + D), c (b + D)) ≡ D (mod 2)`.

Set `Δ = b − a` and `σ(D) = sign(c(b+D) − c(a+D)) ∈ {−1, +1}`.  Indistinguishability gives
`c(n + Δ) = c(n) + σ(n−a)` for `n ≥ a` (in the good range).

1. **`σ` is `Δ`-periodic.**  Iterating: `c(n + 2Δ) − c(n) = σ(n−a) + σ(n−a+Δ)`.  If this
   were `0`, `c` would not be injective.  Hence `σ(n−a) = σ(n−a+Δ)`.

2. **`σ ≡ +1`.**  Iterating further: `c(n + kΔ) = c(n) + k · σ(n−a)`.  If `σ < 0`
   anywhere, the values would tend to `−∞`, impossible for `c : ℕ+ → ℕ+`.

3. **`Δ ≥ 2` is impossible.**  From `c(n + Δ) = c(n) + 1`, the image of `c` on `{n ≥ a}`
   is the union of `Δ` arithmetic rays of step `1`.  The largest initial value `v_max` is
   contained in all `Δ` rays, so it is hit `Δ` times — contradicting injectivity once
   `Δ ≥ 2`.

4. **`Δ = 1` ⇒ `c` is eventually identity.**  Then `c(n + 1) = c(n) + 1` for `n ≥ a`, so
   `c(n) = n + (c(a) − a)` on `{n ≥ a}`.  Bijectivity of `c : ℕ+ → ℕ+` forces the offset
   to be `0`, i.e. `c(n) = n` for all `n ≥ a`.

## Status

This file currently states the predicate `Indistinguishable` and the main Lemma A.
The proof is broken down into sub-lemmas (`c_shift_iter`, `c_shift_implies_cN_eq_N`,
`shift_one_implies_eventually_identity`) — these are tractable building blocks once
PNat arithmetic is handled carefully.  The proof of the main lemma combines these
with a case analysis on `Δ`.
-/

namespace TrolleyRetrieval

/-- Two cells `a < b` are *indistinguishable* (relative to `c`) if for every displacement
    `D ≥ 0` and every time `t ≥ D` with `t ≡ D (mod 2)`, the signals at positions
    `a + D` and `b + D` at time `t` are equal. -/
def Indistinguishable (c : Perm) (a b : ℕ+) : Prop :=
  ∀ D : ℕ, ∀ t : ℕ, (t : ℤ) ≥ D → ((t : ℤ) - D) % 2 = 0 →
    ((c ⟨a.val + D, Nat.lt_of_lt_of_le a.property (Nat.le_add_right _ _)⟩).val < t ↔
     (c ⟨b.val + D, Nat.lt_of_lt_of_le b.property (Nat.le_add_right _ _)⟩).val < t)

/-! ### Sub-lemma: iterated shift

If `c` satisfies `c (n + 1) = c n + 1` past some threshold `N`, then by induction
`c` shifts uniformly: `(c m).val = (c N).val + k` whenever `m.val = N.val + k`. -/

lemma c_shift_iter {c : Perm} {N : ℕ+}
    (h_shift : ∀ n : ℕ+, N ≤ n → c (n + 1) = c n + 1) :
    ∀ (k : ℕ) (m : ℕ+), m.val = N.val + k → (c m).val = (c N).val + k := by
  intro k
  induction k with
  | zero =>
      intro m hm
      have h_eq : m = N := by
        apply Subtype.ext
        show m.val = N.val
        have h_N_pos : 0 < N.val := N.property
        omega
      rw [h_eq]
      simp
  | succ k ih =>
      intro m hm
      have hN_pos : 0 < N.val := N.property
      have h_prev_pos : 0 < N.val + k := Nat.add_pos_left hN_pos k
      set m' : ℕ+ := ⟨N.val + k, h_prev_pos⟩ with hm'_def
      have h_n_ge_N : N ≤ m' := by
        show N.val ≤ N.val + k
        exact Nat.le_add_right N.val k
      have ih_at_m' : (c m').val = (c N).val + k := ih m' rfl
      have h_m_eq : m = m' + 1 := by
        apply Subtype.ext
        show m.val = m'.val + 1
        have h_m'_val : m'.val = N.val + k := rfl
        omega
      rw [h_m_eq, h_shift m' h_n_ge_N]
      show ((c m' + 1 : ℕ+)).val = (c N).val + (k + 1)
      have h_plus : ((c m' + 1 : ℕ+)).val = (c m').val + 1 := rfl
      rw [h_plus, ih_at_m']
      ring

/-! ### Sub-lemma: bijectivity forces `c N = N`

By the iterated-shift formula, `c` maps the ray `{N, N+1, ...}` onto the ray
`{c N, (c N) + 1, ...}`.  Bijectivity of `c : ℕ+ ≃ ℕ+` means `c` also maps the prefix
`{1, ..., N - 1}` bijectively onto the complement `{1, ..., (c N).val - 1}`.  Since
these prefixes have sizes `N.val - 1` and `(c N).val - 1` respectively, we get
`(c N).val = N.val`. -/

lemma c_shift_implies_cN_eq_N {c : Perm} {N : ℕ+}
    (h_shift : ∀ n : ℕ+, N ≤ n → c (n + 1) = c n + 1) :
    (c N).val = N.val := by
  -- **Step 1.** Establish the key bijection: m < c N ↔ c.symm m < N.
  have h_bij : ∀ m : ℕ+, m < c N ↔ c.symm m < N := by
    intro m
    constructor
    · -- m < c N → c.symm m < N.  By contradiction.
      intro hm
      by_contra h_not_lt
      push_neg at h_not_lt
      set n := c.symm m with hn_def
      have h_n_ge_N : N ≤ n := h_not_lt
      have h_n_val_ge : N.val ≤ n.val := h_n_ge_N
      have h_n_eq : n.val = N.val + (n.val - N.val) := by omega
      have h_cn : (c n).val = (c N).val + (n.val - N.val) :=
        c_shift_iter h_shift (n.val - N.val) n h_n_eq
      have h_cn_eq_m : c n = m := by rw [hn_def]; exact c.apply_symm_apply m
      have h_m_val : m.val = (c N).val + (n.val - N.val) := by
        rw [← h_cn_eq_m]; exact h_cn
      have h_m_lt : m.val < (c N).val := hm
      omega
    · -- c.symm m < N → m < c N.  By contradiction.
      intro hm
      by_contra h_not_lt
      push_neg at h_not_lt
      have h_cN_le_m : (c N).val ≤ m.val := h_not_lt
      set k := m.val - (c N).val with hk_def
      have h_m_eq : m.val = (c N).val + k := by omega
      have hN_pos : 0 < N.val := N.property
      have h_Nk_pos : 0 < N.val + k := Nat.add_pos_left hN_pos k
      set n_target : ℕ+ := ⟨N.val + k, h_Nk_pos⟩ with hn_target_def
      have h_cn_val : (c n_target).val = (c N).val + k :=
        c_shift_iter h_shift k n_target rfl
      have h_cn_eq_m : c n_target = m := by
        apply Subtype.ext
        show (c n_target).val = m.val
        rw [h_cn_val]; omega
      have h_csym : c.symm m = n_target := by
        rw [← h_cn_eq_m]; exact c.symm_apply_apply n_target
      have h_n_target_ge : N ≤ n_target := by
        show N.val ≤ N.val + k; omega
      have h_csym_ge : N ≤ c.symm m := by rw [h_csym]; exact h_n_target_ge
      have h_csym_lt : (c.symm m).val < N.val := hm
      have : N.val ≤ (c.symm m).val := h_csym_ge
      omega
  -- **Step 2.** The bijection induces equal Finset cardinality.
  have h_image_eq : (Finset.Iio (c N)).image c.symm = Finset.Iio N := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨m, hm, h_eq⟩
      subst h_eq
      exact (h_bij m).mp hm
    · intro hn
      refine ⟨c n, ?_, c.symm_apply_apply n⟩
      have := (h_bij (c n)).mpr
      rw [c.symm_apply_apply] at this
      exact this hn
  have h_card_eq : (Finset.Iio (c N)).card = (Finset.Iio N).card := by
    rw [← h_image_eq]
    exact (Finset.card_image_of_injective _ c.symm.injective).symm
  -- **Step 3.** The cardinality formula `(Finset.Iio b).card = b.val - 1` for `b : ℕ+`.
  -- We prove this by transporting to `ℕ` via the coercion (which is order-preserving
  -- and injective).
  have h_card_pnat_Iio : ∀ b : ℕ+, (Finset.Iio b).card = b.val - 1 := by
    intro b
    -- The Finset.Iio in PNat injects into ℕ via `PNat.val`, with image equal to
    -- `Finset.Ico 1 b.val` of cardinality `b.val - 1`.
    have h_inj : Function.Injective (PNat.val : ℕ+ → ℕ) := by
      intro x y hxy
      exact PNat.coe_injective hxy
    have h_image : (Finset.Iio b).image PNat.val = Finset.Ico 1 b.val := by
      apply Finset.ext
      intro k
      simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_Ico]
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m.property, hm⟩
      · rintro ⟨hk_pos, hk_lt⟩
        exact ⟨⟨k, hk_pos⟩, hk_lt, rfl⟩
    have h_card_image : ((Finset.Iio b).image PNat.val).card = (Finset.Iio b).card :=
      Finset.card_image_of_injective _ h_inj
    rw [h_image, Nat.card_Ico] at h_card_image
    omega
  have h_card_cN : (Finset.Iio (c N)).card = (c N).val - 1 := h_card_pnat_Iio (c N)
  have h_card_N : (Finset.Iio N).card = N.val - 1 := h_card_pnat_Iio N
  have hN_pos : 0 < N.val := N.property
  have hcN_pos : 0 < (c N).val := (c N).property
  omega

/-! ### Sub-lemma: shift implies eventually identity -/

lemma shift_one_implies_eventually_identity {c : Perm} {N : ℕ+}
    (h_shift : ∀ n : ℕ+, N ≤ n → c (n + 1) = c n + 1) :
    ∀ n : ℕ+, N ≤ n → c n = n := by
  intro n hn
  -- Apply iterated shift at offset k = n.val - N.val.
  set k := n.val - N.val with hk_def
  have h_n_val : n.val = N.val + k := by
    have : N.val ≤ n.val := hn
    omega
  have h_cn_val : (c n).val = (c N).val + k :=
    c_shift_iter h_shift k n h_n_val
  have h_cN : (c N).val = N.val := c_shift_implies_cN_eq_N h_shift
  apply Subtype.ext
  show (c n).val = n.val
  rw [h_cn_val, h_cN, ← h_n_val]

/-! ### Sub-lemma: indistinguishability forces consecutive c-values

For any `D : ℕ` such that both `c (a + D)` and `c (b + D)` have value at least `D`,
the `Indistinguishable` hypothesis pins down the two c-values to be *consecutive
integers*, with the *minimum* sharing parity with `D`.

The argument: any value strictly between (and inclusive of the max) of the two
c-values is a *witness time* `t` where the signals disagree.  For `Indistinguishable`
to hold, none of these witnesses can be a "valid time" (`t ≥ D` with the right
parity).  This rules out gaps ≥ 2 (which would force a parity-matching witness) and
also rules out the wrong parity for the minimum value. -/

/-- Helper: the position `a + D : ℕ+` (positivity from `a ≥ 1`). -/
private def aD (a : ℕ+) (D : ℕ) : ℕ+ :=
  ⟨a.val + D, Nat.lt_of_lt_of_le a.property (Nat.le_add_right _ _)⟩

@[simp] private lemma aD_val (a : ℕ+) (D : ℕ) : (aD a D).val = a.val + D := rfl

lemma indist_consec {c : Perm} {a b : ℕ+} (hab : a < b)
    (h_indist : Indistinguishable c a b) {D : ℕ}
    (h_a_ge : D ≤ (c (aD a D)).val) (h_b_ge : D ≤ (c (aD b D)).val) :
    ((c (aD a D)).val + 1 = (c (aD b D)).val ∨
     (c (aD b D)).val + 1 = (c (aD a D)).val) ∧
    min (c (aD a D)).val (c (aD b D)).val % 2 = D % 2 := by
  set X := (c (aD a D)).val with hX_def
  set Y := (c (aD b D)).val with hY_def
  -- Specialize `Indistinguishable` to this `D`.  The `aD` wrapper has the same `val`
  -- as the `⟨_, _⟩` form used inside `Indistinguishable`, so `simpa` reconciles.
  have h_sig : ∀ t : ℕ, (t : ℤ) ≥ D → ((t : ℤ) - D) % 2 = 0 → (X < t ↔ Y < t) := by
    intro t ht_ge ht_par
    have := h_indist D t ht_ge ht_par
    simpa [aD, hX_def, hY_def] using this
  -- X ≠ Y by bijectivity.
  have h_X_ne_Y : X ≠ Y := by
    intro h_eq
    have h_pnat_eq : c (aD a D) = c (aD b D) := Subtype.ext h_eq
    have h_arg_eq : aD a D = aD b D := c.injective h_pnat_eq
    have h_val_eq : a.val + D = b.val + D := by
      have := congrArg (fun (n : ℕ+) => n.val) h_arg_eq
      simpa [aD_val] using this
    have hab_val : a.val < b.val := hab
    omega
  -- Step 1: show |X - Y| = 1, i.e., either Y = X + 1 or X = Y + 1.
  -- Step 2: show min(X, Y) ≡ D (mod 2).
  -- We argue by trichotomy on X vs Y.
  rcases lt_or_gt_of_ne h_X_ne_Y with h_X_lt_Y | h_X_gt_Y
  · -- X < Y.  Show Y = X + 1.
    have h_Y_eq_X1 : Y = X + 1 := by
      by_contra h_ne
      have h_Y_ge_X2 : X + 2 ≤ Y := by omega
      -- Pick the witness t whose parity matches D's.
      -- Either t = X + 1 (if X + 1 ≡ D mod 2) or t = X + 2 (else).
      by_cases h_par : (X + 1 - D) % 2 = 0
      · -- t = X + 1 has correct parity.
        have h_t_ge : ((↑(X + 1) : ℤ)) ≥ D := by push_cast; omega
        have h_t_par : ((↑(X + 1) : ℤ) - D) % 2 = 0 := by
          have h_le : D ≤ X + 1 := by omega
          have h_cast : (((X + 1) - D : ℕ) : ℤ) = (↑(X + 1) - ↑D : ℤ) :=
            Nat.cast_sub h_le
          rw [← h_cast]
          exact_mod_cast h_par
        have h_iff := h_sig (X + 1) h_t_ge h_t_par
        have : X < X + 1 := by omega
        have h_Y_lt : Y < X + 1 := h_iff.mp this
        omega
      · -- t = X + 2 has correct parity.
        have h_X2_par : (X + 2 - D) % 2 = 0 := by omega
        have h_t_ge : ((↑(X + 2) : ℤ)) ≥ D := by push_cast; omega
        have h_t_par : ((↑(X + 2) : ℤ) - D) % 2 = 0 := by
          have h_le : D ≤ X + 2 := by omega
          have h_cast : (((X + 2) - D : ℕ) : ℤ) = (↑(X + 2) - ↑D : ℤ) :=
            Nat.cast_sub h_le
          rw [← h_cast]
          exact_mod_cast h_X2_par
        have h_iff := h_sig (X + 2) h_t_ge h_t_par
        have : X < X + 2 := by omega
        have h_Y_lt : Y < X + 2 := h_iff.mp this
        omega
    -- Parity: at t = Y = X + 1, signal differs.  Hence t is invalid: (t - D) % 2 ≠ 0.
    have h_par_diff : ((↑Y : ℤ) - D) % 2 ≠ 0 := by
      intro h_par
      have h_t_ge : ((↑Y : ℤ)) ≥ D := by exact_mod_cast h_b_ge
      have h_iff := h_sig Y h_t_ge h_par
      have hX : X < Y := h_X_lt_Y
      have hY : ¬ (Y < Y) := lt_irrefl Y
      exact hY (h_iff.mp hX)
    refine ⟨Or.inl h_Y_eq_X1.symm, ?_⟩
    -- min(X, Y) = X.  X ≡ D mod 2 since Y ≡ D + 1 mod 2 (from h_par_diff).
    rw [min_eq_left (by omega : X ≤ Y)]
    have h_X_le_Y : X ≤ Y := by omega
    have h_Y_ne_D_par : (Y - D) % 2 ≠ 0 := by
      intro h
      apply h_par_diff
      have h_nat : ((Y - D : ℕ) : ℤ) % 2 = 0 := by exact_mod_cast h
      have : ((Y - D : ℕ) : ℤ) = ((Y : ℤ) - D) := by
        have : D ≤ Y := h_b_ge
        push_cast; omega
      rw [← this]; exact h_nat
    -- Y = X + 1, and (Y - D) % 2 = 1, so (X + 1 - D) % 2 = 1, so (X - D) % 2 = 0.
    omega
  · -- X > Y.  Symmetric.
    have h_X_eq_Y1 : X = Y + 1 := by
      by_contra h_ne
      have h_X_ge_Y2 : Y + 2 ≤ X := by omega
      by_cases h_par : (Y + 1 - D) % 2 = 0
      · have h_t_ge : ((↑(Y + 1) : ℤ)) ≥ D := by push_cast; omega
        have h_t_par : ((↑(Y + 1) : ℤ) - D) % 2 = 0 := by
          have h_le : D ≤ Y + 1 := by omega
          have h_cast : (((Y + 1) - D : ℕ) : ℤ) = (↑(Y + 1) - ↑D : ℤ) :=
            Nat.cast_sub h_le
          rw [← h_cast]
          exact_mod_cast h_par
        have h_iff := h_sig (Y + 1) h_t_ge h_t_par
        have : Y < Y + 1 := by omega
        have h_X_lt : X < Y + 1 := h_iff.mpr this
        omega
      · have h_Y2_par : (Y + 2 - D) % 2 = 0 := by omega
        have h_t_ge : ((↑(Y + 2) : ℤ)) ≥ D := by push_cast; omega
        have h_t_par : ((↑(Y + 2) : ℤ) - D) % 2 = 0 := by
          have h_le : D ≤ Y + 2 := by omega
          have h_cast : (((Y + 2) - D : ℕ) : ℤ) = (↑(Y + 2) - ↑D : ℤ) :=
            Nat.cast_sub h_le
          rw [← h_cast]
          exact_mod_cast h_Y2_par
        have h_iff := h_sig (Y + 2) h_t_ge h_t_par
        have : Y < Y + 2 := by omega
        have h_X_lt : X < Y + 2 := h_iff.mpr this
        omega
    have h_par_diff : ((↑X : ℤ) - D) % 2 ≠ 0 := by
      intro h_par
      have h_t_ge : ((↑X : ℤ)) ≥ D := by exact_mod_cast h_a_ge
      have h_iff := h_sig X h_t_ge h_par
      have hY : Y < X := h_X_gt_Y
      have hX : ¬ (X < X) := lt_irrefl X
      exact hX (h_iff.mpr hY)
    refine ⟨Or.inr h_X_eq_Y1.symm, ?_⟩
    rw [min_eq_right (by omega : Y ≤ X)]
    have h_X_ne_D_par : (X - D) % 2 ≠ 0 := by
      intro h
      apply h_par_diff
      have h_nat : ((X - D : ℕ) : ℤ) % 2 = 0 := by exact_mod_cast h
      have : ((X - D : ℕ) : ℤ) = ((X : ℤ) - D) := by
        have : D ≤ X := h_a_ge
        push_cast; omega
      rw [← this]; exact h_nat
    omega

/-! ### Sub-lemma: Δ ≥ 2 with global shift-by-Δ-equals-plus-one is impossible

If `c (n + Δ) = c n + 1` for *every* `n : ℕ+` and `Δ ≥ 2`, then `c` cannot be a
bijection.

The argument: iterating the shift gives `c (N + k·Δ).val = c(N).val + k` and similarly
`c (N + 1 + k·Δ).val = c(N + 1).val + k`.  These two arithmetic rays both eventually
reach the value `max(c N, c (N+1))`, but at different positions, contradicting
injectivity.
-/

/-- Iterated form of the shift-by-Δ relation, starting from a threshold `N₀`.
    For any `M ≥ N₀`, the shift iterates to `(c (M + k·Δ)).val = (c M).val + k`. -/
private lemma c_iter_Delta {c : Perm} {Δ : ℕ} {N₀ : ℕ+}
    (h_shift : ∀ n : ℕ+, N₀ ≤ n → ∀ (h_pos : 0 < n.val + Δ),
      (c ⟨n.val + Δ, h_pos⟩).val = (c n).val + 1)
    {M : ℕ+} (hM : N₀ ≤ M) :
    ∀ (k : ℕ) (h_pos : 0 < M.val + k * Δ),
      (c ⟨M.val + k * Δ, h_pos⟩).val = (c M).val + k := by
  intro k
  induction k with
  | zero =>
      intro h_pos
      have h_eq : (⟨M.val + 0 * Δ, h_pos⟩ : ℕ+) = M := by
        apply Subtype.ext
        show M.val + 0 * Δ = M.val
        ring
      rw [h_eq]
      simp
  | succ k ih =>
      intro h_pos
      have hM_pos : 0 < M.val := M.property
      have h_prev_pos : 0 < M.val + k * Δ := Nat.add_pos_left hM_pos _
      set m : ℕ+ := ⟨M.val + k * Δ, h_prev_pos⟩ with hm_def
      have h_mΔ_pos : 0 < m.val + Δ := by
        show 0 < M.val + k * Δ + Δ
        exact Nat.add_pos_left h_prev_pos _
      have h_m_ge_N₀ : N₀ ≤ m := by
        show N₀.val ≤ M.val + k * Δ
        have h_N₀_le_M : N₀.val ≤ M.val := hM
        omega
      have h_step := h_shift m h_m_ge_N₀ h_mΔ_pos
      have h_pos_eq : (⟨M.val + (k + 1) * Δ, h_pos⟩ : ℕ+) =
                       ⟨m.val + Δ, h_mΔ_pos⟩ := by
        apply Subtype.ext
        show M.val + (k + 1) * Δ = M.val + k * Δ + Δ
        ring
      rw [h_pos_eq, h_step, ih h_prev_pos]
      ring

lemma shift_Delta_ge_2_contradiction {c : Perm} {Δ : ℕ} (hΔ : 2 ≤ Δ) {N₀ : ℕ+}
    (h_shift : ∀ n : ℕ+, N₀ ≤ n → ∀ (h_pos : 0 < n.val + Δ),
      (c ⟨n.val + Δ, h_pos⟩).val = (c n).val + 1) : False := by
  -- Specialize at N₀ and N1 := N₀ + 1.
  have hN1_pos : 0 < N₀.val + 1 := Nat.add_pos_left N₀.property 1
  set N1 : ℕ+ := ⟨N₀.val + 1, hN1_pos⟩ with hN1_def
  have h_N_le_N : N₀ ≤ N₀ := le_refl _
  have h_N_le_N1 : N₀ ≤ N1 := by show N₀.val ≤ N₀.val + 1; omega
  -- Iterated shift along both rays.
  have h_iter_N : ∀ (k : ℕ) (h_pos : 0 < N₀.val + k * Δ),
      (c ⟨N₀.val + k * Δ, h_pos⟩).val = (c N₀).val + k :=
    c_iter_Delta h_shift h_N_le_N
  have h_iter_N1 : ∀ (k : ℕ) (h_pos : 0 < N1.val + k * Δ),
      (c ⟨N1.val + k * Δ, h_pos⟩).val = (c N1).val + k :=
    c_iter_Delta h_shift h_N_le_N1
  -- N₀ ≠ N1.
  have h_N1_val : N1.val = N₀.val + 1 := rfl
  have h_N_ne_N1 : N₀ ≠ N1 := by
    intro h
    have h_val_eq : N₀.val = N1.val := congrArg _ h
    omega
  have h_cN_ne : (c N₀).val ≠ (c N1).val := by
    intro h_val
    apply h_N_ne_N1
    apply c.injective
    exact Subtype.ext h_val
  rcases lt_or_gt_of_ne h_cN_ne with h_lt | h_gt
  · -- c N₀ < c N1.  Choose k = c(N1).val - c(N₀).val ≥ 1.
    set k := (c N1).val - (c N₀).val with hk_def
    have hk_pos : 1 ≤ k := by omega
    have hN_kD_pos : 0 < N₀.val + k * Δ := Nat.add_pos_left N₀.property _
    have h_apply := h_iter_N k hN_kD_pos
    have h_val_eq : (c ⟨N₀.val + k * Δ, hN_kD_pos⟩).val = (c N1).val := by
      rw [h_apply]; omega
    have h_pnat_eq : c ⟨N₀.val + k * Δ, hN_kD_pos⟩ = c N1 :=
      Subtype.ext h_val_eq
    have h_pos_eq : (⟨N₀.val + k * Δ, hN_kD_pos⟩ : ℕ+) = N1 := c.injective h_pnat_eq
    have h_val_pos : N₀.val + k * Δ = N1.val := by
      have := congrArg (fun (n : ℕ+) => n.val) h_pos_eq
      simpa using this
    -- N₀.val + k·Δ = N₀.val + 1, so k·Δ = 1.  But k ≥ 1 and Δ ≥ 2.
    have h_kD_eq_1 : k * Δ = 1 := by omega
    have h_kD_ge_2 : 2 ≤ k * Δ := by
      calc 2 = 1 * 2 := by ring
        _ ≤ k * Δ := Nat.mul_le_mul hk_pos hΔ
    omega
  · -- c N₀ > c N1.  Choose k = c(N₀).val - c(N1).val ≥ 1.
    set k := (c N₀).val - (c N1).val with hk_def
    have hk_pos : 1 ≤ k := by omega
    have hN1_kD_pos : 0 < N1.val + k * Δ := Nat.add_pos_left N1.property _
    have h_apply := h_iter_N1 k hN1_kD_pos
    have h_val_eq : (c ⟨N1.val + k * Δ, hN1_kD_pos⟩).val = (c N₀).val := by
      rw [h_apply]; omega
    have h_pnat_eq : c ⟨N1.val + k * Δ, hN1_kD_pos⟩ = c N₀ :=
      Subtype.ext h_val_eq
    have h_pos_eq : (⟨N1.val + k * Δ, hN1_kD_pos⟩ : ℕ+) = N₀ := c.injective h_pnat_eq
    have h_val_pos : N1.val + k * Δ = N₀.val := by
      have := congrArg (fun (n : ℕ+) => n.val) h_pos_eq
      simpa using this
    -- N1.val + k·Δ = N₀.val, but N1.val = N₀.val + 1, so N₀.val + 1 + k·Δ = N₀.val.
    omega

/-! ### Auxiliary: shift relation from Indistinguishable -/

/-- For every `D : ℕ`, both positions `a + D` and `b + D` lie in `[1, ∞)` (since
    `a, b ≥ 1`). -/
private lemma aD_pos (a : ℕ+) (D : ℕ) : 0 < a.val + D :=
  Nat.lt_of_lt_of_le a.property (Nat.le_add_right _ _)

/-- **σ does not flip.**  Pure injectivity: along three positions `p, q, r` spaced by
    `Δ ≥ 1` (so `q = p + Δ`, `r = q + Δ`), if the step `p → q` is ascending by `1` and the
    step `q → r` is `±1` (consecutive), then `q → r` must also be ascending.

If instead `q → r` descended, `c r` would equal `c p`, forcing `r = p` by injectivity,
impossible since `r = p + 2Δ`. -/
private lemma sigma_no_flip {c : Perm} {p q r : ℕ+} {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hq : q.val = p.val + Δ) (hr : r.val = q.val + Δ)
    (h_pq : (c q).val = (c p).val + 1)
    (h_consec : (c r).val = (c q).val + 1 ∨ (c r).val + 1 = (c q).val) :
    (c r).val = (c q).val + 1 := by
  rcases h_consec with h | h
  · exact h
  · exfalso
    have h_cr_eq_cp : (c r).val = (c p).val := by omega
    have h_cr_cp : c r = c p := Subtype.ext h_cr_eq_cp
    have h_rp : r = p := c.injective h_cr_cp
    have h_rp_val : r.val = p.val := by rw [h_rp]
    omega

/-- **σ does not flip (descending version).**  Symmetric to `sigma_no_flip`: if the step
    `p → q` descends by `1` and `q → r` is `±1`, then `q → r` also descends.  An ascending
    `q → r` would give `c r = c p`, contradicting injectivity. -/
private lemma sigma_no_flip_desc {c : Perm} {p q r : ℕ+} {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hq : q.val = p.val + Δ) (hr : r.val = q.val + Δ)
    (h_pq : (c q).val + 1 = (c p).val)
    (h_consec : (c r).val = (c q).val + 1 ∨ (c r).val + 1 = (c q).val) :
    (c r).val + 1 = (c q).val := by
  rcases h_consec with h | h
  · exfalso
    have h_cr_eq_cp : (c r).val = (c p).val := by omega
    have h_cr_cp : c r = c p := Subtype.ext h_cr_eq_cp
    have h_rp : r = p := c.injective h_cr_cp
    have h_rp_val : r.val = p.val := by rw [h_rp]
    omega
  · exact h

/-- **Self-avoiding ±1 walks ascend.**  If `f : ℕ → ℕ` is injective and every step changes
    the value by exactly `1` (`f(k+1) = f k ± 1`), then in fact `f(k+1) = f k + 1` for all
    `k`.

Two ideas: (1) *no reversal* — an up-step then down-step (or vice versa) revisits a value,
contradicting injectivity, so the direction is globally constant; (2) the descending
direction is impossible on `ℕ` — it would force `f` below `0`.

This is the structural engine behind "an everywhere-consecutive chain is an ascending
ray", which (with `Δ ≥ 2`) yields the ray-overlap contradiction and (with `Δ = 1`) the
identity. -/
lemma pm1_injective_ascending (f : ℕ → ℕ) (hinj : Function.Injective f)
    (hstep : ∀ k, f (k + 1) = f k + 1 ∨ f (k + 1) + 1 = f k) :
    ∀ k, f (k + 1) = f k + 1 := by
  -- Ascending propagates (no reversal).
  have prop : ∀ k, f (k + 1) = f k + 1 → f (k + 1 + 1) = f (k + 1) + 1 := by
    intro k hk
    rcases hstep (k + 1) with h | h
    · exact h
    · exfalso
      have hval : f (k + 1 + 1) = f k := by omega
      have := hinj hval
      omega
  -- Descending propagates.
  have propd : ∀ k, f (k + 1) + 1 = f k → f (k + 1 + 1) + 1 = f (k + 1) := by
    intro k hk
    rcases hstep (k + 1) with h | h
    · exfalso
      have hval : f (k + 1 + 1) = f k := by omega
      have := hinj hval
      omega
    · exact h
  rcases hstep 0 with h0 | h0
  · -- Ascending start: propagate.
    intro k
    induction k with
    | zero => exact h0
    | succ n ih => exact prop n ih
  · -- Descending start: impossible on ℕ.
    exfalso
    have hdesc : ∀ k, f (k + 1) + 1 = f k := by
      intro k
      induction k with
      | zero => exact h0
      | succ n ih => exact propd n ih
    have hval : ∀ k, f k + k = f 0 := by
      intro k
      induction k with
      | zero => simp
      | succ n ih => have := hdesc n; omega
    have := hval (f 0 + 1)
    omega

/-- **Flat chain ⇒ ascending shift.**  If `|c(q+Δ) − c(q)| = 1` for *every* `q ≥ Q`
    (an "everywhere-flat" Δ-chain), then in fact `c(q+Δ) = c(q) + 1` for every `q ≥ Q`.

For each starting cell `n ≥ Q`, the forward chain `k ↦ c(n + kΔ).val` is an injective
±1 walk, so by `pm1_injective_ascending` it ascends; reading off its first step gives
`c(n+Δ) = c(n)+1`. -/
lemma flat_imp_ascending {c : Perm} {Δ : ℕ} (hΔ : 1 ≤ Δ) {Q : ℕ+}
    (hflat : ∀ q : ℕ+, Q ≤ q → ∀ (hq : 0 < q.val + Δ),
      (c ⟨q.val + Δ, hq⟩).val = (c q).val + 1 ∨
      (c ⟨q.val + Δ, hq⟩).val + 1 = (c q).val) :
    ∀ n : ℕ+, Q ≤ n → ∀ (hn : 0 < n.val + Δ),
      (c ⟨n.val + Δ, hn⟩).val = (c n).val + 1 := by
  intro n hn_ge hn_pos
  -- positions n + kΔ as ℕ+
  have hpos : ∀ k : ℕ, 0 < n.val + k * Δ := by
    intro k; exact Nat.lt_of_lt_of_le n.property (Nat.le_add_right _ _)
  -- the forward chain value function
  set f : ℕ → ℕ := fun k => (c ⟨n.val + k * Δ, hpos k⟩).val with hf_def
  -- f is injective
  have hf_inj : Function.Injective f := by
    intro k1 k2 hk
    simp only [hf_def] at hk
    have hc : c ⟨n.val + k1 * Δ, hpos k1⟩ = c ⟨n.val + k2 * Δ, hpos k2⟩ := Subtype.ext hk
    have hpe := c.injective hc
    have : n.val + k1 * Δ = n.val + k2 * Δ := by
      have := congrArg (fun (m : ℕ+) => m.val) hpe; simpa using this
    have hk12 : k1 * Δ = k2 * Δ := by omega
    have hΔ0 : Δ ≠ 0 := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) hk12
  -- f steps by ±1
  have hf_step : ∀ k, f (k + 1) = f k + 1 ∨ f (k + 1) + 1 = f k := by
    intro k
    -- position q_k = n + kΔ ≥ Q
    have hqk_pos : 0 < n.val + k * Δ := hpos k
    set qk : ℕ+ := ⟨n.val + k * Δ, hqk_pos⟩ with hqk_def
    have hqk_ge : Q ≤ qk := by
      show Q.val ≤ n.val + k * Δ
      have : Q.val ≤ n.val := hn_ge
      omega
    have hqkΔ_pos : 0 < qk.val + Δ := by show 0 < n.val + k * Δ + Δ; omega
    have hstep := hflat qk hqk_ge hqkΔ_pos
    -- (c ⟨qk.val + Δ, _⟩) = (c ⟨n.val + (k+1)Δ, _⟩) and f(k+1)
    have heq_pos : (⟨qk.val + Δ, hqkΔ_pos⟩ : ℕ+) = ⟨n.val + (k + 1) * Δ, hpos (k + 1)⟩ := by
      apply Subtype.ext
      show qk.val + Δ = n.val + (k + 1) * Δ
      show n.val + k * Δ + Δ = n.val + (k + 1) * Δ
      ring
    rw [heq_pos] at hstep
    -- now hstep relates f(k+1) and f(k) (= c qk)
    simpa only [hf_def, hqk_def] using hstep
  -- apply pm1
  have hasc := pm1_injective_ascending f hf_inj hf_step 0
  -- f 1 = f 0 + 1: c(n+Δ) = c(n) + 1
  simp only [hf_def] at hasc
  -- f 0 = c(n), f 1 = c(n + Δ)
  have h0 : (⟨n.val + 0 * Δ, hpos 0⟩ : ℕ+) = n := by
    apply Subtype.ext; show n.val + 0 * Δ = n.val; ring
  have h1 : (⟨n.val + 1 * Δ, hpos 1⟩ : ℕ+) = ⟨n.val + Δ, hn_pos⟩ := by
    apply Subtype.ext; show n.val + 1 * Δ = n.val + Δ; ring
  rw [h0, h1] at hasc
  exact hasc

/-- **Flat chain with `Δ ≥ 2` is impossible.**  An everywhere-flat `Δ`-chain ascends
    (`flat_imp_ascending`), but an ascending `Δ`-shift with `Δ ≥ 2` overlaps rays
    (`shift_Delta_ge_2_contradiction`). -/
lemma flat_Delta_ge_2 {c : Perm} {Δ : ℕ} (hΔ : 2 ≤ Δ) {Q : ℕ+}
    (hflat : ∀ q : ℕ+, Q ≤ q → ∀ (hq : 0 < q.val + Δ),
      (c ⟨q.val + Δ, hq⟩).val = (c q).val + 1 ∨
      (c ⟨q.val + Δ, hq⟩).val + 1 = (c q).val) :
    False :=
  shift_Delta_ge_2_contradiction hΔ (flat_imp_ascending (by omega) hflat)

/-- **Flat chain with `Δ = 1` forces eventual identity.**  An everywhere-flat `1`-chain
    ascends (`flat_imp_ascending`), giving `c (n+1) = c n + 1` for `n ≥ Q`, whence
    `shift_one_implies_eventually_identity` yields `c n = n` for `n ≥ Q`. -/
lemma flat_Delta_one {c : Perm} {Q : ℕ+}
    (hflat : ∀ q : ℕ+, Q ≤ q → ∀ (hq : 0 < q.val + 1),
      (c ⟨q.val + 1, hq⟩).val = (c q).val + 1 ∨
      (c ⟨q.val + 1, hq⟩).val + 1 = (c q).val) :
    ∀ n : ℕ+, Q ≤ n → c n = n := by
  have hasc := flat_imp_ascending (Δ := 1) (le_refl 1) hflat
  apply shift_one_implies_eventually_identity
  intro n hn
  have hpos : 0 < n.val + 1 := by have := n.property; omega
  have h := hasc n hn hpos
  have h_eq : (⟨n.val + 1, hpos⟩ : ℕ+) = n + (1 : ℕ+) := by
    apply Subtype.ext
    show n.val + 1 = (n + (1 : ℕ+)).val
    rfl
  rw [h_eq] at h
  apply Subtype.ext
  show (c (n + (1 : ℕ+))).val = (c n + (1 : ℕ+)).val
  have hplus : ((c n + (1 : ℕ+)).val) = (c n).val + 1 := rfl
  rw [hplus]
  exact h

/-- **Pigeonhole core.**  If the `M + 1` cells `a, a+1, …, a+M` all map under `c` into the
    `M`-element value-set `{1, …, M}`, then `c` is not injective — contradiction.

This is the engine of the `σ(0) = −1` impossibility: a descending start forces exactly
this over-stuffing of `{1, …, c(a).val}`. -/
private lemma maps_into_contradiction {c : Perm} {a : ℕ+} {M : ℕ}
    (h : ∀ D : ℕ, D ≤ M → (c ⟨a.val + D, aD_pos a D⟩).val ≤ M) : False := by
  -- The map `D ↦ (c (a+D)).val − 1` injects `Fin (M+1)` into `Fin M`.
  have key : ∀ D : Fin (M + 1), (c ⟨a.val + D.val, aD_pos a D.val⟩).val - 1 < M := by
    intro D
    have h1 := h D.val (Nat.lt_succ_iff.mp D.isLt)
    have h2 : 0 < (c ⟨a.val + D.val, aD_pos a D.val⟩).val :=
      (c ⟨a.val + D.val, aD_pos a D.val⟩).2
    omega
  let g : Fin (M + 1) → Fin M :=
    fun D => ⟨(c ⟨a.val + D.val, aD_pos a D.val⟩).val - 1, key D⟩
  have hg_inj : Function.Injective g := by
    intro D1 D2 hD
    have hv1 : 0 < (c ⟨a.val + D1.val, aD_pos a D1.val⟩).val :=
      (c ⟨a.val + D1.val, aD_pos a D1.val⟩).2
    have hv2 : 0 < (c ⟨a.val + D2.val, aD_pos a D2.val⟩).val :=
      (c ⟨a.val + D2.val, aD_pos a D2.val⟩).2
    have hD' : (c ⟨a.val + D1.val, aD_pos a D1.val⟩).val - 1 =
               (c ⟨a.val + D2.val, aD_pos a D2.val⟩).val - 1 := by
      simpa only [g, Fin.mk.injEq] using hD
    have h_val_eq : (c ⟨a.val + D1.val, aD_pos a D1.val⟩).val =
                    (c ⟨a.val + D2.val, aD_pos a D2.val⟩).val := by omega
    have h_c_eq : c ⟨a.val + D1.val, aD_pos a D1.val⟩ =
                  c ⟨a.val + D2.val, aD_pos a D2.val⟩ := Subtype.ext h_val_eq
    have h_pos_eq := c.injective h_c_eq
    have h_av : a.val + D1.val = a.val + D2.val := by
      have := congrArg (fun (n : ℕ+) => n.val) h_pos_eq
      simpa using this
    exact Fin.val_injective (by omega)
  have hcard := Fintype.card_le_of_injective g hg_inj
  simp only [Fintype.card_fin] at hcard
  omega

/-- **Good is symmetric.**  Under `Indistinguishable`, at every displacement `D` the
    a-side cell is "above threshold" (`c(a+D).val ≥ D`) iff the b-side cell is.

This follows from the signal-match at the minimal time `t = D`: the signal there is
exactly "the cell is below threshold", and `Indistinguishable` forces these to agree. -/
lemma good_symm {c : Perm} {a b : ℕ+}
    (h : Indistinguishable c a b) (D : ℕ) :
    (D ≤ (c (aD a D)).val) ↔ (D ≤ (c (aD b D)).val) := by
  have hsig : (c (aD a D)).val < D ↔ (c (aD b D)).val < D :=
    h D D (le_refl (D : ℤ)) (by simp)
  constructor
  · intro ha
    by_contra hb
    push_neg at hb
    exact absurd (hsig.mpr hb) (by omega)
  · intro hb
    by_contra ha
    push_neg at ha
    exact absurd (hsig.mp ha) (by omega)

/-- **Good is downward-closed (Δ = 1).**  For the pair `(a, a+1)`, if cell `a + (D+1)` is
    above threshold (`≥ D+1`), then cell `a + D` is above threshold (`≥ D`).

For `Δ = 1` the b-side at `D` is the a-side at `D+1`, so `good_symm` at `D` says
`c(a+D) ≥ D ⟺ c(a+(D+1)) ≥ D`; the hypothesis gives the right side. -/
lemma good_downward {c : Perm} {a b : ℕ+} (hb : b.val = a.val + 1)
    (h : Indistinguishable c a b) (D : ℕ)
    (hD : (D + 1) ≤ (c (aD a (D + 1))).val) : D ≤ (c (aD a D)).val := by
  have hbridge : aD b D = aD a (D + 1) := by
    apply Subtype.ext; show b.val + D = a.val + (D + 1); omega
  have hgs := good_symm h D
  rw [hbridge] at hgs
  rw [hgs]
  omega

/-- **Bad-D propagation.**  If at displacement `D` the cell `a + D` is "below the time
    threshold" (`c(a+D).val < D`), then so is `b + D`.

The signal from `a + D` is then `"Yes"` already at the minimal valid time `t = D`, and
`Indistinguishable` forces the signal from `b + D` to be `"Yes"` there too — which says
exactly `c(b+D).val < D`. -/
lemma bad_D_propagates {c : Perm} {a b : ℕ+}
    (h : Indistinguishable c a b) {D : ℕ}
    (h_bad : (c ⟨a.val + D, aD_pos a D⟩).val < D) :
    (c ⟨b.val + D, aD_pos b D⟩).val < D := by
  have h_t_ge : (D : ℤ) ≥ (D : ℤ) := le_refl _
  have h_t_par : ((D : ℤ) - (D : ℤ)) % 2 = 0 := by simp
  have h_iff := h D D h_t_ge h_t_par
  exact h_iff.mp h_bad

/-- **Δ = 1 ascending.**  For the pair `(a, a+1)` (so `b.val = a.val + 1`), if
    `Indistinguishable` holds and the first step ascends (`c(a) < c(a+1)`, i.e.
    `σ(0) = +1`), then the whole a-chain ascends: `c(a+D).val = c(a).val + D`.

`good_symm` keeps every `D` "good" (the ascending values stay above the time
threshold), so `indist_consec` applies at every `D`, and `sigma_no_flip` forbids the
chain from ever turning down. -/
lemma indist_ascending_Delta1 {c : Perm} {a b : ℕ+} (hb : b.val = a.val + 1)
    (hab : a < b) (h : Indistinguishable c a b)
    (hσ0 : (c (aD a 0)).val + 1 = (c (aD a 1)).val) :
    ∀ D : ℕ, (c (aD a D)).val = (c (aD a 0)).val + D := by
  have hbridge : ∀ D : ℕ, aD b D = aD a (D + 1) := by
    intro D
    apply Subtype.ext
    show b.val + D = a.val + (D + 1)
    omega
  suffices h2 : ∀ n : ℕ,
      (c (aD a n)).val = (c (aD a 0)).val + n ∧
      (c (aD a (n + 1))).val = (c (aD a 0)).val + (n + 1) by
    intro D; exact (h2 D).1
  intro n
  induction n with
  | zero =>
      refine ⟨by omega, ?_⟩
      rw [← hσ0]
  | succ m ih =>
      obtain ⟨hm, hm1⟩ := ih
      refine ⟨hm1, ?_⟩
      have h_a_ge : (m + 1) ≤ (c (aD a (m + 1))).val := by rw [hm1]; omega
      have h_b_ge : (m + 1) ≤ (c (aD b (m + 1))).val :=
        (good_symm h (m + 1)).mp h_a_ge
      have hcons := (indist_consec hab h h_a_ge h_b_ge).1
      rw [hbridge (m + 1)] at hcons
      rcases hcons with hasc | hdesc
      · rw [← hasc, hm1]; ring
      · exfalso
        have h_eq_val : (c (aD a (m + 1 + 1))).val = (c (aD a m)).val := by
          rw [hm]; omega
        have h_eq : c (aD a (m + 1 + 1)) = c (aD a m) := Subtype.ext h_eq_val
        have h_pos_eq : aD a (m + 1 + 1) = aD a m := c.injective h_eq
        have hcontra : a.val + (m + 1 + 1) = a.val + m := by
          have := congrArg (fun (p : ℕ+) => p.val) h_pos_eq
          simpa [aD_val] using this
        omega

/-- **Δ = 1, σ(0) = +1 ⇒ eventual identity.**  The ascending chain
    (`indist_ascending_Delta1`) is in particular everywhere-flat, so `flat_Delta_one`
    gives `c n = n` for `n ≥ a`. -/
lemma indist_Delta1_pos {c : Perm} {a b : ℕ+} (hb : b.val = a.val + 1)
    (hab : a < b) (h : Indistinguishable c a b)
    (hσ0 : (c (aD a 0)).val + 1 = (c (aD a 1)).val) :
    ∀ n : ℕ+, a ≤ n → c n = n := by
  have hasc := indist_ascending_Delta1 hb hab h hσ0
  apply flat_Delta_one (Q := a)
  intro q hq hqpos
  left
  set D := q.val - a.val with hD
  have hqval : q.val = a.val + D := by
    have : a.val ≤ q.val := hq
    omega
  have hq_eq : aD a D = q := by
    apply Subtype.ext; show a.val + D = q.val; omega
  have hq1_eq : aD a (D + 1) = ⟨q.val + 1, hqpos⟩ := by
    apply Subtype.ext; show a.val + (D + 1) = q.val + 1; omega
  have e1 := hasc D
  have e2 := hasc (D + 1)
  rw [hq_eq] at e1
  rw [hq1_eq] at e2
  rw [e2, e1]
  omega

/-- **Δ = 1, σ(0) = −1 is impossible.**  A descending start forces the a-chain to descend
    on its (downward-closed) good prefix, so every cell `a, …, a+M` (with `M = c(a).val`)
    lands in `{1, …, M}` — contradicting injectivity via `maps_into_contradiction`. -/
lemma indist_Delta1_neg {c : Perm} {a b : ℕ+} (hb : b.val = a.val + 1)
    (hab : a < b) (h : Indistinguishable c a b)
    (hσ0 : (c (aD a 1)).val + 1 = (c (aD a 0)).val) :
    False := by
  set M := (c (aD a 0)).val with hM
  have hbridge : ∀ D : ℕ, aD b D = aD a (D + 1) := by
    intro D; apply Subtype.ext; show b.val + D = a.val + (D + 1); omega
  -- Descending formula on the good prefix, carried two-step.
  have hP : ∀ n : ℕ,
      (n ≤ (c (aD a n)).val → (c (aD a n)).val + n = M) ∧
      ((n + 1) ≤ (c (aD a (n + 1))).val → (c (aD a (n + 1))).val + (n + 1) = M) := by
    intro n
    induction n with
    | zero =>
        refine ⟨fun _ => by omega, fun _ => ?_⟩
        show (c (aD a 1)).val + 1 = M
        omega
    | succ m ih =>
        obtain ⟨hPm, hPm1⟩ := ih
        refine ⟨hPm1, ?_⟩
        intro hgood2
        have hgood1 : (m + 1) ≤ (c (aD a (m + 1))).val :=
          good_downward hb h (m + 1) hgood2
        have hgood0 : m ≤ (c (aD a m)).val := good_downward hb h m hgood1
        have hvm1 : (c (aD a (m + 1))).val + (m + 1) = M := hPm1 hgood1
        have hvm : (c (aD a m)).val + m = M := hPm hgood0
        have hdesc_step : (c (aD a (m + 1))).val + 1 = (c (aD a m)).val := by omega
        have hb_ge : (m + 1) ≤ (c (aD b (m + 1))).val := by
          rw [hbridge (m + 1)]; omega
        have hcons := (indist_consec hab h hgood1 hb_ge).1
        rw [hbridge (m + 1)] at hcons
        have hnf := sigma_no_flip_desc (c := c) (p := aD a m) (q := aD a (m + 1))
          (r := aD a (m + 1 + 1)) (Δ := 1) (le_refl 1)
          (by show (aD a (m + 1)).val = (aD a m).val + 1; simp only [aD_val]; omega)
          (by show (aD a (m + 1 + 1)).val = (aD a (m + 1)).val + 1;
              simp only [aD_val]; omega)
          hdesc_step (Or.imp_left Eq.symm hcons)
        omega
  -- Every cell a..a+M maps into {1,..,M}; pigeonhole contradiction.
  apply maps_into_contradiction (a := a) (M := M)
  intro D hD
  show (c (aD a D)).val ≤ M
  by_cases hgood : D ≤ (c (aD a D)).val
  · have := (hP D).1 hgood
    omega
  · push_neg at hgood
    omega

/-- **Δ even, "good" sub-case.**  If `(a, b)` is indistinguishable with `Δ = b−a` even
    (`≥ 2`) and displacement `Δ` is itself "good" (`Δ ≤ c(b)`), we reach a contradiction.

`c(b)` is consecutive to both `c(a)` (displacement `0`) and `c(a+2Δ)` (displacement `Δ`),
and by injectivity `c(a) ≠ c(a+2Δ)`, so `{c(a), c(a+2Δ)} = {c(b)−1, c(b)+1}`.  Both
minima must be even (since `0` and `Δ` are even), which pins `c(b)` to both parities —
contradiction.  (Superseded by `indist_Delta_even_good_at` for general displacement;
kept as the `D = 0` instance.  The full Δ-even closure is `indist_Delta_even`.) -/
lemma indist_Delta_even_good {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) (Δ : ℕ) (hΔ : b.val = a.val + Δ)
    (hΔeven : Δ % 2 = 0) (hΔ2 : 2 ≤ Δ) (hgood : Δ ≤ (c b).val) : False := by
  have ea0 : aD a 0 = a := by apply Subtype.ext; show a.val + 0 = a.val; omega
  have eb0 : aD b 0 = b := by apply Subtype.ext; show b.val + 0 = b.val; omega
  have eaΔ : aD a Δ = b := by apply Subtype.ext; show a.val + Δ = b.val; omega
  have h0 := indist_consec hab h (D := 0) (Nat.zero_le _) (Nat.zero_le _)
  rw [ea0, eb0] at h0
  have h_aΔ : Δ ≤ (c (aD a Δ)).val := by rw [eaΔ]; exact hgood
  have h_bΔ : Δ ≤ (c (aD b Δ)).val := (good_symm h Δ).mp h_aΔ
  have hΔc := indist_consec hab h (D := Δ) h_aΔ h_bΔ
  rw [eaΔ] at hΔc
  set a2 := aD b Δ with ha2def
  have hca_ne : (c a).val ≠ (c a2).val := by
    intro heq
    have hpos : a = a2 := c.injective (Subtype.ext heq)
    have : a.val = b.val + Δ := by
      have := congrArg (fun p : ℕ+ => p.val) hpos
      rw [ha2def] at this; simpa [aD_val] using this
    omega
  obtain ⟨hcons0, hpar0⟩ := h0
  obtain ⟨hconsΔ, hparΔ⟩ := hΔc
  rcases hcons0 with h1 | h1 <;> rcases hconsΔ with h2 | h2 <;> omega

/-- **Δ even, general "good pair".**  If `Δ` is even and a good pair `(D₀, D₀+Δ)` exists
    (`c(a+D₀) ≥ D₀` and `c(a+D₀+Δ) ≥ D₀+Δ`), the same parity argument (now at displacement
    `D₀`) gives a contradiction.  The two minima are `≡ D₀` and `≡ D₀+Δ ≡ D₀` (Δ even). -/
lemma indist_Delta_even_good_at {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) (Δ : ℕ) (hΔ : b.val = a.val + Δ) (hΔeven : Δ % 2 = 0)
    (D₀ : ℕ) (hg1 : D₀ ≤ (c (aD a D₀)).val) (hg2 : D₀ + Δ ≤ (c (aD a (D₀ + Δ))).val) :
    False := by
  have hΔpos : 1 ≤ Δ := by have h' : a.val < b.val := hab; omega
  have br1 : aD b D₀ = aD a (D₀ + Δ) := by
    apply Subtype.ext; show b.val + D₀ = a.val + (D₀ + Δ); omega
  have br2 : aD b (D₀ + Δ) = aD a (D₀ + Δ + Δ) := by
    apply Subtype.ext; show b.val + (D₀ + Δ) = a.val + (D₀ + Δ + Δ); omega
  have hb1 : D₀ ≤ (c (aD b D₀)).val := by rw [br1]; omega
  have hc1 := indist_consec hab h (D := D₀) hg1 hb1
  rw [br1] at hc1
  have hb2 : D₀ + Δ ≤ (c (aD b (D₀ + Δ))).val := (good_symm h (D₀ + Δ)).mp hg2
  have hc2 := indist_consec hab h (D := D₀ + Δ) hg2 hb2
  rw [br2] at hc2
  have hne : (c (aD a D₀)).val ≠ (c (aD a (D₀ + Δ + Δ))).val := by
    intro heq
    have hpe : aD a D₀ = aD a (D₀ + Δ + Δ) := c.injective (Subtype.ext heq)
    have : a.val + D₀ = a.val + (D₀ + Δ + Δ) := by
      have := congrArg (fun p : ℕ+ => p.val) hpe; simpa [aD_val] using this
    omega
  obtain ⟨hcons1, hpar1⟩ := hc1
  obtain ⟨hcons2, hpar2⟩ := hc2
  rcases hcons1 with h1 | h1 <;> rcases hcons2 with h2 | h2 <;> omega

/-- **Counting / over-stuffing (pure pigeonhole).**  If `c(a+D) < D` for all `D ≥ T`
    (cofinitely many displacements "bad"), then `c` maps the initial segment `[1, N]` into the
    smaller set `[1, N − a − 1]` for large `N` — contradicting injectivity.  No
    `Indistinguishable` hypothesis is needed; this is the engine behind `regime2_impossible`
    and the `Δ ≥ 2` impossibility. -/
lemma cofinitely_bad_impossible {c : Perm} {a : ℕ+} {T : ℕ}
    (hbound : ∀ D : ℕ, T ≤ D → (c (aD a D)).val < D) : False := by
  set B : ℕ := (Finset.range (a.val + T)).sup (fun n => (c ⟨n + 1, Nat.succ_pos n⟩).val)
    with hBdef
  have hBbound : ∀ p : ℕ+, p.val < a.val + T → (c p).val ≤ B := by
    intro p hp
    have hp1 : 1 ≤ p.val := p.property
    have hmem : p.val - 1 ∈ Finset.range (a.val + T) := Finset.mem_range.mpr (by omega)
    have hval_eq : (c p).val = (c ⟨(p.val - 1) + 1, Nat.succ_pos _⟩).val := by
      have hpeq : (⟨(p.val - 1) + 1, Nat.succ_pos _⟩ : ℕ+) = p := by
        apply Subtype.ext; show (p.val - 1) + 1 = p.val; omega
      rw [hpeq]
    rw [hBdef, hval_eq]
    exact Finset.le_sup (f := fun n => (c ⟨n + 1, Nat.succ_pos n⟩).val) hmem
  set N : ℕ := B + a.val + T + 1 with hNdef
  have haval : 1 ≤ a.val := a.property
  have hval : ∀ i : Fin N, (c ⟨i.val + 1, Nat.succ_pos _⟩).val ≤ N - a.val - 1 := by
    intro i
    by_cases hge : a.val + T ≤ i.val + 1
    · have hposeq : (⟨i.val + 1, Nat.succ_pos _⟩ : ℕ+) = aD a (i.val + 1 - a.val) := by
        apply Subtype.ext; show i.val + 1 = a.val + (i.val + 1 - a.val); omega
      have hb := hbound (i.val + 1 - a.val) (by omega)
      rw [hposeq]
      have := i.isLt
      omega
    · have := hBbound ⟨i.val + 1, Nat.succ_pos _⟩ (by simp; omega)
      omega
  let g : Fin N → Fin (N - a.val - 1) := fun i =>
    ⟨(c ⟨i.val + 1, Nat.succ_pos _⟩).val - 1, by
      have h1 := hval i
      have h2 : 0 < (c ⟨i.val + 1, Nat.succ_pos _⟩).val := (c ⟨i.val + 1, Nat.succ_pos _⟩).2
      omega⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    have hval_eq : (c ⟨i.val + 1, Nat.succ_pos _⟩).val - 1
        = (c ⟨j.val + 1, Nat.succ_pos _⟩).val - 1 := by
      simpa only [g, Fin.mk.injEq] using hij
    have h2i : 0 < (c ⟨i.val + 1, Nat.succ_pos _⟩).val := (c ⟨i.val + 1, Nat.succ_pos _⟩).2
    have h2j : 0 < (c ⟨j.val + 1, Nat.succ_pos _⟩).val := (c ⟨j.val + 1, Nat.succ_pos _⟩).2
    have hcv : (c ⟨i.val + 1, Nat.succ_pos _⟩).val = (c ⟨j.val + 1, Nat.succ_pos _⟩).val := by
      omega
    have hc : c ⟨i.val + 1, Nat.succ_pos _⟩ = c ⟨j.val + 1, Nat.succ_pos _⟩ := Subtype.ext hcv
    have hpe := c.injective hc
    have : i.val + 1 = j.val + 1 := by
      have := congrArg (fun (p : ℕ+) => p.val) hpe; simpa using this
    exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective g hg_inj
  simp only [Fintype.card_fin] at hcard
  omega

/-- **One backward step on a residue.**  If displacement `D ≥ Δ` is *active* (`c(a+D) ≥ D`),
    then `D − Δ` is active too and `c(a+D) ≤ c(a+(D−Δ)) + 1` (consecutive values, via
    `good_symm` and `indist_consec`).  Key engine: "bad" is forward-closed, so active
    displacements form a prefix on each residue class. -/
lemma active_step {c : Perm} {a b : ℕ+} (hab : a < b) (h : Indistinguishable c a b)
    {Δ : ℕ} (hΔ : b.val = a.val + Δ) {D : ℕ} (hDΔ : Δ ≤ D)
    (hact : D ≤ (c (aD a D)).val) :
    (D - Δ ≤ (c (aD a (D - Δ))).val) ∧ (c (aD a D)).val ≤ (c (aD a (D - Δ))).val + 1 := by
  have hbridge : aD a D = aD b (D - Δ) := by
    apply Subtype.ext; show a.val + D = b.val + (D - Δ); omega
  have hb_ge : D - Δ ≤ (c (aD b (D - Δ))).val := by rw [← hbridge]; omega
  have ha_ge : D - Δ ≤ (c (aD a (D - Δ))).val := (good_symm h (D - Δ)).mpr hb_ge
  refine ⟨ha_ge, ?_⟩
  have hcons := (indist_consec hab h (D := D - Δ) ha_ge hb_ge).1
  rw [← hbridge] at hcons
  rcases hcons with h1 | h1 <;> omega

/-- **Chain bound.**  On the active prefix of a residue, c-values grow by at most `1` per
    `Δ`-step: if `r + kΔ` is active, then `c(a + r + kΔ) ≤ c(a + r) + k`. -/
lemma chain_bound {c : Perm} {a b : ℕ+} (hab : a < b) (h : Indistinguishable c a b)
    {Δ : ℕ} (hΔ : b.val = a.val + Δ) (hΔ1 : 1 ≤ Δ) (r : ℕ) :
    ∀ k : ℕ, (r + k * Δ ≤ (c (aD a (r + k * Δ))).val) →
      (c (aD a (r + k * Δ))).val ≤ (c (aD a r)).val + k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ n ih =>
      intro hact
      have hexp : (n + 1) * Δ = n * Δ + Δ := by ring
      have hDΔ : Δ ≤ r + (n + 1) * Δ := by omega
      have hstep := active_step hab h hΔ hDΔ hact
      have heq : r + (n + 1) * Δ - Δ = r + n * Δ := by omega
      rw [heq] at hstep
      obtain ⟨hact_prev, hbound_step⟩ := hstep
      have hih := ih hact_prev
      omega

/-- **Δ ≥ 2 is impossible.**  By `chain_bound`, an active displacement `D = r + kΔ` satisfies
    `D ≤ c(a+D) ≤ c(a+r) + k`, so `k(Δ−1) ≤ c(a+r) ≤ M := maxᵣ c(a+r)`; for `Δ ≥ 2` this
    bounds `k`, hence `D < (M+1)Δ`.  So all displacements past `(M+1)Δ` are bad, and
    `cofinitely_bad_impossible` finishes.  (Subsumes both the even and odd `Δ ≥ 2` cases, with
    no parity argument and no good-pair gap.) -/
lemma indist_Delta_ge_2_impossible {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) {Δ : ℕ} (hΔ : b.val = a.val + Δ) (hΔ2 : 2 ≤ Δ) : False := by
  set M : ℕ := (Finset.range Δ).sup (fun r => (c (aD a r)).val) with hMdef
  apply cofinitely_bad_impossible (a := a) (T := (M + 1) * Δ)
  intro D hD
  by_contra hcon
  push_neg at hcon
  have hΔpos : 0 < Δ := by omega
  set r := D % Δ with hrdef
  set k := D / Δ with hkdef
  have hDeq : D = r + k * Δ := by
    rw [hrdef, hkdef, Nat.mul_comm, Nat.add_comm]; exact (Nat.div_add_mod D Δ).symm
  have hrlt : r < Δ := Nat.mod_lt _ hΔpos
  have hact' : r + k * Δ ≤ (c (aD a (r + k * Δ))).val := by rw [← hDeq]; exact hcon
  have hcb := chain_bound hab h hΔ (by omega) r k hact'
  rw [← hDeq] at hcb
  have hM : (c (aD a r)).val ≤ M := by
    rw [hMdef]
    exact Finset.le_sup (f := fun r => (c (aD a r)).val) (Finset.mem_range.mpr hrlt)
  -- D ≤ c(a+D) ≤ c(a+r) + k ≤ M + k
  have hDMk : D ≤ M + k := le_trans hcon (le_trans hcb (by omega))
  -- k ≤ M  (since D = r + kΔ and Δ ≥ 2 ⇒ 2k ≤ kΔ ≤ M + k)
  have h2k : 2 * k ≤ k * Δ := by nlinarith [hΔ2, Nat.zero_le k]
  have hkM : k ≤ M := by
    have hkΔ : k * Δ ≤ M + k := by omega
    omega
  -- D = r + kΔ < (M+1)Δ = T ≤ D : contradiction
  have hkMΔ : k * Δ ≤ M * Δ := by
    have := Nat.mul_le_mul_right (k := Δ) hkM
    simpa using this
  have hTexp : (M + 1) * Δ = M * Δ + Δ := by ring
  omega

/-- **Regime-2 bound.**  If no "good pair" `(D, D+Δ)` exists (every `D` has `c(a+D) < D`
    or `c(a+D+Δ) < D+Δ`), then *every* displacement `≥ Δ` is bad: `c(a+D) < D` for `D ≥ Δ`.
    (Good `D` forces `D+Δ` bad by hypothesis; bad `D` forces `D+Δ` bad by `bad_D_propagates`.) -/
lemma regime2_bound {c : Perm} {a b : ℕ+} (h : Indistinguishable c a b) {Δ : ℕ}
    (hΔ : b.val = a.val + Δ)
    (hreg2 : ∀ D : ℕ, (c (aD a D)).val < D ∨ (c (aD a (D + Δ))).val < D + Δ) :
    ∀ D : ℕ, Δ ≤ D → (c (aD a D)).val < D := by
  intro D hD
  obtain ⟨D0, rfl⟩ : ∃ D0, D = D0 + Δ := ⟨D - Δ, by omega⟩
  rcases hreg2 D0 with hbad | hgood
  · have hbad' : (c ⟨a.val + D0, aD_pos a D0⟩).val < D0 := hbad
    have hbp := bad_D_propagates h hbad'
    have heq : (⟨b.val + D0, aD_pos b D0⟩ : ℕ+) = aD a (D0 + Δ) := by
      apply Subtype.ext; show b.val + D0 = a.val + (D0 + Δ); omega
    rw [heq] at hbp
    omega
  · exact hgood

/-- **Regime 2 is impossible.**  Under `regime2_bound`, `c` would map the initial segment
    `[1, N]` into the smaller set `[1, N − a − 1]` for large `N` — contradicting injectivity. -/
lemma regime2_impossible {c : Perm} {a b : ℕ+} (h : Indistinguishable c a b) {Δ : ℕ}
    (hΔ : b.val = a.val + Δ) (hΔ2 : 2 ≤ Δ)
    (hreg2 : ∀ D : ℕ, (c (aD a D)).val < D ∨ (c (aD a (D + Δ))).val < D + Δ) : False := by
  have hbound := regime2_bound h hΔ hreg2
  -- bound on `c` over the finitely many positions below `a + Δ`
  have hpos : 0 < a.val + Δ := by have := a.property; omega
  set B : ℕ := (Finset.range (a.val + Δ)).sup (fun n => (c ⟨n + 1, Nat.succ_pos n⟩).val)
    with hBdef
  have hBbound : ∀ p : ℕ+, p.val < a.val + Δ → (c p).val ≤ B := by
    intro p hp
    have hp1 : 1 ≤ p.val := p.property
    have hmem : p.val - 1 ∈ Finset.range (a.val + Δ) := Finset.mem_range.mpr (by omega)
    have hval_eq : (c p).val = (c ⟨(p.val - 1) + 1, Nat.succ_pos _⟩).val := by
      have hpeq : (⟨(p.val - 1) + 1, Nat.succ_pos _⟩ : ℕ+) = p := by
        apply Subtype.ext; show (p.val - 1) + 1 = p.val; omega
      rw [hpeq]
    rw [hBdef, hval_eq]
    exact Finset.le_sup (f := fun n => (c ⟨n + 1, Nat.succ_pos n⟩).val) hmem
  set N : ℕ := B + a.val + Δ + 1 with hNdef
  have haval : 1 ≤ a.val := a.property
  -- every position `i+1 ≤ N` has c-value `≤ N - a - 1`
  have hval : ∀ i : Fin N, (c ⟨i.val + 1, Nat.succ_pos _⟩).val ≤ N - a.val - 1 := by
    intro i
    by_cases hge : a.val + Δ ≤ i.val + 1
    · have hposeq : (⟨i.val + 1, Nat.succ_pos _⟩ : ℕ+) = aD a (i.val + 1 - a.val) := by
        apply Subtype.ext; show i.val + 1 = a.val + (i.val + 1 - a.val); omega
      have hb := hbound (i.val + 1 - a.val) (by omega)
      rw [hposeq]
      have := i.isLt
      omega
    · have := hBbound ⟨i.val + 1, Nat.succ_pos _⟩ (by simp; omega)
      omega
  -- inject Fin N into Fin (N - a - 1)
  let g : Fin N → Fin (N - a.val - 1) := fun i =>
    ⟨(c ⟨i.val + 1, Nat.succ_pos _⟩).val - 1, by
      have h1 := hval i
      have h2 : 0 < (c ⟨i.val + 1, Nat.succ_pos _⟩).val := (c ⟨i.val + 1, Nat.succ_pos _⟩).2
      omega⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    have hval_eq : (c ⟨i.val + 1, Nat.succ_pos _⟩).val - 1
        = (c ⟨j.val + 1, Nat.succ_pos _⟩).val - 1 := by
      simpa only [g, Fin.mk.injEq] using hij
    have h2i : 0 < (c ⟨i.val + 1, Nat.succ_pos _⟩).val := (c ⟨i.val + 1, Nat.succ_pos _⟩).2
    have h2j : 0 < (c ⟨j.val + 1, Nat.succ_pos _⟩).val := (c ⟨j.val + 1, Nat.succ_pos _⟩).2
    have hcv : (c ⟨i.val + 1, Nat.succ_pos _⟩).val = (c ⟨j.val + 1, Nat.succ_pos _⟩).val := by
      omega
    have hc : c ⟨i.val + 1, Nat.succ_pos _⟩ = c ⟨j.val + 1, Nat.succ_pos _⟩ := Subtype.ext hcv
    have hpe := c.injective hc
    have : i.val + 1 = j.val + 1 := by
      have := congrArg (fun (p : ℕ+) => p.val) hpe; simpa using this
    exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective g hg_inj
  simp only [Fintype.card_fin] at hcard
  omega

/-- **Δ even is fully impossible.**  Case on whether a good pair exists: if so, the parity
    kill (`indist_Delta_even_good_at`); if not, `regime2_impossible`.  No `sorry`. -/
lemma indist_Delta_even {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) {Δ : ℕ} (hΔ : b.val = a.val + Δ)
    (hΔeven : Δ % 2 = 0) (hΔ2 : 2 ≤ Δ) : False := by
  by_cases hge : ∃ D : ℕ, D ≤ (c (aD a D)).val ∧ D + Δ ≤ (c (aD a (D + Δ))).val
  · obtain ⟨D₀, hg1, hg2⟩ := hge
    exact indist_Delta_even_good_at hab h Δ hΔ hΔeven D₀ hg1 hg2
  · push_neg at hge
    apply regime2_impossible h hΔ hΔ2
    intro D
    by_cases hD : D ≤ (c (aD a D)).val
    · right; have := hge D hD; omega
    · left; omega

/-! ### Main statement -/

/-- **Lemma A (forward).**  If a pair `(a, b)` with `a < b` is indistinguishable, then
    `b = a + 1` and `c` is eventually identity from position `a`.

The proof case-splits on `Δ = b − a`:

* `Δ = 1`: the σ(0) case split (`indist_Delta1_pos` / `indist_Delta1_neg`) gives eventual
  identity.
* `Δ ≥ 2`: impossible.  Bad displacements are forward-closed (`bad_D_propagates`), so the
  active displacements form a finite prefix on each residue (chain bound + active lower
  bound); cofinitely many displacements are then bad, contradicting injectivity
  (`indist_Delta_ge_2_impossible`).  No parity split is needed. -/

theorem Indistinguishable_implies_eventually_identity
    {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) :
    (b = a + 1) ∧ (∀ n : ℕ+, a ≤ n → c n = n) := by
  set Δ : ℕ := b.val - a.val with hΔ_def
  have hΔ_pos : 1 ≤ Δ := by
    have h_ab_val : a.val < b.val := hab
    omega
  -- Case split: Δ = 1 vs Δ ≥ 2.
  rcases eq_or_lt_of_le hΔ_pos with hΔ_eq | hΔ_ge_2
  · -- **Δ = 1** (fully proven via the σ(0) case split, no `sorry`).
    have hΔ_eq_1 : Δ = 1 := hΔ_eq.symm
    have hab' : a.val < b.val := hab
    have hb1 : b.val = a.val + 1 := by omega
    have hb_eq : b = a + 1 := by
      apply Subtype.ext
      show b.val = (a + (1 : ℕ+)).val
      have h_pnat_add : (a + (1 : ℕ+)).val = a.val + 1 := rfl
      omega
    -- σ(0) at D = 0: c(a), c(b) are consecutive (b = a+1 so c(aD b 0) = c(aD a 1)).
    have hbridge0 : aD b 0 = aD a 1 := by
      apply Subtype.ext; show b.val + 0 = a.val + 1; omega
    have hsig0 := (indist_consec hab h (Nat.zero_le _) (Nat.zero_le _)).1
    rw [hbridge0] at hsig0
    have h_id : ∀ n : ℕ+, a ≤ n → c n = n := by
      rcases hsig0 with hpos | hneg
      · exact indist_Delta1_pos hb1 hab h hpos
      · exact (indist_Delta1_neg hb1 hab h hneg).elim
    exact ⟨hb_eq, h_id⟩
  · -- **Δ ≥ 2**: impossible.  `bad` is forward-closed (`bad_D_propagates`), so active
    -- displacements form a finite prefix on each residue (chain bound + active lower bound);
    -- hence cofinitely many displacements are bad, contradicting injectivity
    -- (`indist_Delta_ge_2_impossible`).  No parity split, no good-pair gap.
    exfalso
    have hΔ_ge_2' : 2 ≤ Δ := hΔ_ge_2
    have hab' : a.val < b.val := hab
    have hbΔ : b.val = a.val + Δ := by omega
    exact indist_Delta_ge_2_impossible hab h hbΔ hΔ_ge_2'

/-- **Lemma A (corollary used by the winning direction).**  If `c` is not eventually
    identity, then *no* pair of starting cells is indistinguishable. -/
theorem not_eventually_identity_implies_distinguishable
    {c : Perm} (h : ¬ EventuallyIdentity c) :
    ∀ a b : ℕ+, a < b → ¬ Indistinguishable c a b := by
  intro a b hab h_indist
  obtain ⟨_, h_ei⟩ := Indistinguishable_implies_eventually_identity hab h_indist
  exact h ⟨a, h_ei⟩

/-! ## Threshold-floored indistinguishability

`IndistFrom c a b D₀` is the threshold-floored variant of `Indistinguishable`: the signals
of the two trajectories agree at every displacement `D ≥ D₀` and every valid time `t ≥ D`
with `t ≡ D (mod 2)`.  This is exactly the negation of "a separator exists at displacement
`≥ D₀`".

The point of this section is to re-run the Lemma A engine *with a floor*: every engine helper
(`indist_consec`, `good_symm`, `bad_D_propagates`, `active_step`, `chain_bound`) only ever
applies the signal-agreement hypothesis at a *single* displacement `D` (or `D ± Δ`), with
times naturally `≥ D`.  Provided every such displacement is `≥ D₀`, the agreement floor is
respected, so the helpers carry over verbatim.  The conclusion is the same kill — either a
pigeonhole/cofinitely-bad contradiction, or (in the `Δ = 1` ascending branch) eventual
identity from the cell `a + D₀`. -/

/-- Threshold-floored indistinguishability: signal-agreement at every displacement `D ≥ D₀`. -/
def IndistFrom (c : Perm) (a b : ℕ+) (D₀ : ℕ) : Prop :=
  ∀ D : ℕ, D₀ ≤ D → ∀ t : ℕ, (t : ℤ) ≥ D → ((t : ℤ) - D) % 2 = 0 →
    ((c (aD a D)).val < t ↔ (c (aD b D)).val < t)

/-- **Threshold `indist_consec`.**  Same conclusion as `indist_consec` but using only the
    floored hypothesis `IndistFrom`, valid at displacements `D ≥ D₀`. -/
lemma indist_consec_from {c : Perm} {a b : ℕ+} (hab : a < b) {D₀ : ℕ}
    (h : IndistFrom c a b D₀) {D : ℕ} (hD₀ : D₀ ≤ D)
    (h_a_ge : D ≤ (c (aD a D)).val) (h_b_ge : D ≤ (c (aD b D)).val) :
    ((c (aD a D)).val + 1 = (c (aD b D)).val ∨
     (c (aD b D)).val + 1 = (c (aD a D)).val) ∧
    min (c (aD a D)).val (c (aD b D)).val % 2 = D % 2 := by
  set X := (c (aD a D)).val with hX_def
  set Y := (c (aD b D)).val with hY_def
  have h_sig : ∀ t : ℕ, (t : ℤ) ≥ D → ((t : ℤ) - D) % 2 = 0 → (X < t ↔ Y < t) := by
    intro t ht_ge ht_par
    exact h D hD₀ t ht_ge ht_par
  -- X ≠ Y by bijectivity.
  have h_X_ne_Y : X ≠ Y := by
    intro h_eq
    have h_pnat_eq : c (aD a D) = c (aD b D) := Subtype.ext h_eq
    have h_arg_eq : aD a D = aD b D := c.injective h_pnat_eq
    have h_val_eq : a.val + D = b.val + D := by
      have := congrArg (fun (n : ℕ+) => n.val) h_arg_eq
      simpa [aD_val] using this
    have hab_val : a.val < b.val := hab
    omega
  rcases lt_or_gt_of_ne h_X_ne_Y with h_X_lt_Y | h_X_gt_Y
  · -- X < Y.  Show Y = X + 1.
    have h_Y_eq_X1 : Y = X + 1 := by
      by_contra h_ne
      have h_Y_ge_X2 : X + 2 ≤ Y := by omega
      by_cases h_par : (X + 1 - D) % 2 = 0
      · have h_t_ge : ((↑(X + 1) : ℤ)) ≥ D := by push_cast; omega
        have h_t_par : ((↑(X + 1) : ℤ) - D) % 2 = 0 := by
          have h_le : D ≤ X + 1 := by omega
          have h_cast : (((X + 1) - D : ℕ) : ℤ) = (↑(X + 1) - ↑D : ℤ) :=
            Nat.cast_sub h_le
          rw [← h_cast]; exact_mod_cast h_par
        have h_iff := h_sig (X + 1) h_t_ge h_t_par
        have : X < X + 1 := by omega
        have h_Y_lt : Y < X + 1 := h_iff.mp this
        omega
      · have h_X2_par : (X + 2 - D) % 2 = 0 := by omega
        have h_t_ge : ((↑(X + 2) : ℤ)) ≥ D := by push_cast; omega
        have h_t_par : ((↑(X + 2) : ℤ) - D) % 2 = 0 := by
          have h_le : D ≤ X + 2 := by omega
          have h_cast : (((X + 2) - D : ℕ) : ℤ) = (↑(X + 2) - ↑D : ℤ) :=
            Nat.cast_sub h_le
          rw [← h_cast]; exact_mod_cast h_X2_par
        have h_iff := h_sig (X + 2) h_t_ge h_t_par
        have : X < X + 2 := by omega
        have h_Y_lt : Y < X + 2 := h_iff.mp this
        omega
    have h_par_diff : ((↑Y : ℤ) - D) % 2 ≠ 0 := by
      intro h_par
      have h_t_ge : ((↑Y : ℤ)) ≥ D := by exact_mod_cast h_b_ge
      have h_iff := h_sig Y h_t_ge h_par
      have hX : X < Y := h_X_lt_Y
      have hY : ¬ (Y < Y) := lt_irrefl Y
      exact hY (h_iff.mp hX)
    refine ⟨Or.inl h_Y_eq_X1.symm, ?_⟩
    rw [min_eq_left (by omega : X ≤ Y)]
    have h_Y_ne_D_par : (Y - D) % 2 ≠ 0 := by
      intro h
      apply h_par_diff
      have h_nat : ((Y - D : ℕ) : ℤ) % 2 = 0 := by exact_mod_cast h
      have : ((Y - D : ℕ) : ℤ) = ((Y : ℤ) - D) := by
        have : D ≤ Y := h_b_ge
        push_cast; omega
      rw [← this]; exact h_nat
    omega
  · -- X > Y.  Symmetric.
    have h_X_eq_Y1 : X = Y + 1 := by
      by_contra h_ne
      have h_X_ge_Y2 : Y + 2 ≤ X := by omega
      by_cases h_par : (Y + 1 - D) % 2 = 0
      · have h_t_ge : ((↑(Y + 1) : ℤ)) ≥ D := by push_cast; omega
        have h_t_par : ((↑(Y + 1) : ℤ) - D) % 2 = 0 := by
          have h_le : D ≤ Y + 1 := by omega
          have h_cast : (((Y + 1) - D : ℕ) : ℤ) = (↑(Y + 1) - ↑D : ℤ) :=
            Nat.cast_sub h_le
          rw [← h_cast]; exact_mod_cast h_par
        have h_iff := h_sig (Y + 1) h_t_ge h_t_par
        have : Y < Y + 1 := by omega
        have h_X_lt : X < Y + 1 := h_iff.mpr this
        omega
      · have h_Y2_par : (Y + 2 - D) % 2 = 0 := by omega
        have h_t_ge : ((↑(Y + 2) : ℤ)) ≥ D := by push_cast; omega
        have h_t_par : ((↑(Y + 2) : ℤ) - D) % 2 = 0 := by
          have h_le : D ≤ Y + 2 := by omega
          have h_cast : (((Y + 2) - D : ℕ) : ℤ) = (↑(Y + 2) - ↑D : ℤ) :=
            Nat.cast_sub h_le
          rw [← h_cast]; exact_mod_cast h_Y2_par
        have h_iff := h_sig (Y + 2) h_t_ge h_t_par
        have : Y < Y + 2 := by omega
        have h_X_lt : X < Y + 2 := h_iff.mpr this
        omega
    have h_par_diff : ((↑X : ℤ) - D) % 2 ≠ 0 := by
      intro h_par
      have h_t_ge : ((↑X : ℤ)) ≥ D := by exact_mod_cast h_a_ge
      have h_iff := h_sig X h_t_ge h_par
      have hY : Y < X := h_X_gt_Y
      have hX : ¬ (X < X) := lt_irrefl X
      exact hX (h_iff.mpr hY)
    refine ⟨Or.inr h_X_eq_Y1.symm, ?_⟩
    rw [min_eq_right (by omega : Y ≤ X)]
    have h_X_ne_D_par : (X - D) % 2 ≠ 0 := by
      intro h
      apply h_par_diff
      have h_nat : ((X - D : ℕ) : ℤ) % 2 = 0 := by exact_mod_cast h
      have : ((X - D : ℕ) : ℤ) = ((X : ℤ) - D) := by
        have : D ≤ X := h_a_ge
        push_cast; omega
      rw [← this]; exact h_nat
    omega

/-- **Threshold `good_symm`.**  At any displacement `D ≥ D₀`, the a-side is above threshold
    iff the b-side is.  (Uses the signal at the minimal valid time `t = D`, which is `≥ D₀`.) -/
lemma good_symm_from {c : Perm} {a b : ℕ+} {D₀ : ℕ}
    (h : IndistFrom c a b D₀) {D : ℕ} (hD₀ : D₀ ≤ D) :
    (D ≤ (c (aD a D)).val) ↔ (D ≤ (c (aD b D)).val) := by
  have hsig : (c (aD a D)).val < D ↔ (c (aD b D)).val < D :=
    h D hD₀ D (le_refl (D : ℤ)) (by simp)
  constructor
  · intro ha
    by_contra hb
    push_neg at hb
    exact absurd (hsig.mpr hb) (by omega)
  · intro hb
    by_contra ha
    push_neg at ha
    exact absurd (hsig.mp ha) (by omega)

/-- **Threshold `bad_D_propagates`.**  At displacement `D ≥ D₀`, a "below threshold" a-side
    forces a "below threshold" b-side. -/
lemma bad_D_propagates_from {c : Perm} {a b : ℕ+} {D₀ : ℕ}
    (h : IndistFrom c a b D₀) {D : ℕ} (hD₀ : D₀ ≤ D)
    (h_bad : (c (aD a D)).val < D) :
    (c (aD b D)).val < D := by
  have h_t_ge : (D : ℤ) ≥ (D : ℤ) := le_refl _
  have h_t_par : ((D : ℤ) - (D : ℤ)) % 2 = 0 := by simp
  have h_iff := h D hD₀ D h_t_ge h_t_par
  exact h_iff.mp h_bad

/-- **Threshold `active_step`.**  If `D ≥ D₀ + Δ` is active, then `D − Δ` (which is `≥ D₀`)
    is active too and the a-values are consecutive-bounded. -/
lemma active_step_from {c : Perm} {a b : ℕ+} (hab : a < b) {D₀ : ℕ}
    (h : IndistFrom c a b D₀) {Δ : ℕ} (hΔ : b.val = a.val + Δ) {D : ℕ}
    (hDΔ : D₀ + Δ ≤ D) (hact : D ≤ (c (aD a D)).val) :
    (D - Δ ≤ (c (aD a (D - Δ))).val) ∧ (c (aD a D)).val ≤ (c (aD a (D - Δ))).val + 1 := by
  have hbridge : aD a D = aD b (D - Δ) := by
    apply Subtype.ext; show a.val + D = b.val + (D - Δ); omega
  have hb_ge : D - Δ ≤ (c (aD b (D - Δ))).val := by rw [← hbridge]; omega
  have hDmΔ_D₀ : D₀ ≤ D - Δ := by omega
  have ha_ge : D - Δ ≤ (c (aD a (D - Δ))).val := (good_symm_from h hDmΔ_D₀).mpr hb_ge
  refine ⟨ha_ge, ?_⟩
  have hcons := (indist_consec_from hab h hDmΔ_D₀ ha_ge hb_ge).1
  rw [← hbridge] at hcons
  rcases hcons with h1 | h1 <;> omega

/-- **Threshold `chain_bound`.**  On the active prefix of a residue starting at `r ≥ D₀`,
    c-values grow by at most `1` per `Δ`-step. -/
lemma chain_bound_from {c : Perm} {a b : ℕ+} (hab : a < b) {D₀ : ℕ}
    (h : IndistFrom c a b D₀) {Δ : ℕ} (hΔ : b.val = a.val + Δ) (hΔ1 : 1 ≤ Δ)
    {r : ℕ} (hr : D₀ ≤ r) :
    ∀ k : ℕ, (r + k * Δ ≤ (c (aD a (r + k * Δ))).val) →
      (c (aD a (r + k * Δ))).val ≤ (c (aD a r)).val + k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ n ih =>
      intro hact
      have hDΔ : D₀ + Δ ≤ r + (n + 1) * Δ := by
        have : Δ ≤ (n + 1) * Δ := by nlinarith [Nat.zero_le n]
        omega
      have hstep := active_step_from hab h hΔ hDΔ hact
      have heq : r + (n + 1) * Δ - Δ = r + n * Δ := by
        have hexp : (n + 1) * Δ = n * Δ + Δ := by ring
        omega
      rw [heq] at hstep
      obtain ⟨hact_prev, hbound_step⟩ := hstep
      have hih := ih hact_prev
      omega

/-- **Threshold `cofinitely_bad_impossible`.**  Same statement and proof as
    `cofinitely_bad_impossible`; included here only to mirror the floored naming (it does not
    use any indistinguishability hypothesis, so it is literally the original lemma). -/
lemma cofinitely_bad_impossible_from {c : Perm} {a : ℕ+} {T : ℕ}
    (hbound : ∀ D : ℕ, T ≤ D → (c (aD a D)).val < D) : False :=
  cofinitely_bad_impossible hbound

/-- **Threshold `good_downward` (Δ = 1).**  For the pair `(a, a+1)`, at displacement `D ≥ D₀`,
    if `a + (D+1)` is above threshold then so is `a + D`. -/
lemma good_downward_from {c : Perm} {a b : ℕ+} (hb : b.val = a.val + 1) {D₀ : ℕ}
    (h : IndistFrom c a b D₀) {D : ℕ} (hD₀ : D₀ ≤ D)
    (hD : (D + 1) ≤ (c (aD a (D + 1))).val) : D ≤ (c (aD a D)).val := by
  have hbridge : aD b D = aD a (D + 1) := by
    apply Subtype.ext; show b.val + D = a.val + (D + 1); omega
  have hgs := good_symm_from h hD₀ (D := D)
  rw [hbridge] at hgs
  rw [hgs]
  omega

/-! ### Δ ≥ 2 floored impossibility -/

/-- **Threshold `indist_Delta_ge_2_impossible`.**  Floored re-run of the `Δ ≥ 2` kill: active
    displacements `D ≥ D₀` are bounded via `chain_bound_from` on residues `r ∈ [D₀, D₀+Δ)`, so
    cofinitely many displacements are bad. -/
lemma indistFrom_Delta_ge_2_impossible {c : Perm} {a b : ℕ+} (hab : a < b) {D₀ : ℕ}
    (h : IndistFrom c a b D₀) {Δ : ℕ} (hΔ : b.val = a.val + Δ) (hΔ2 : 2 ≤ Δ) : False := by
  -- Max c-value over the Δ residues based at D₀.
  set M : ℕ := (Finset.range Δ).sup (fun r => (c (aD a (D₀ + r))).val) with hMdef
  apply cofinitely_bad_impossible_from (a := a) (T := D₀ + (M + 1) * Δ)
  intro D hD
  by_contra hcon
  push_neg at hcon
  have hΔpos : 0 < Δ := by omega
  -- Decompose `D = D₀ + q`, `q = (D - D₀)`; residue `q % Δ`, quotient `q / Δ`.
  set q := D - D₀ with hqdef
  have hDeq0 : D = D₀ + q := by omega
  set r0 := q % Δ with hr0def
  set k := q / Δ with hkdef
  have hqeq : q = r0 + k * Δ := by
    rw [hr0def, hkdef, Nat.mul_comm, Nat.add_comm]; exact (Nat.div_add_mod q Δ).symm
  have hr0lt : r0 < Δ := Nat.mod_lt _ hΔpos
  -- The residue base `r = D₀ + r0`.
  set r := D₀ + r0 with hrdef
  have hr_ge : D₀ ≤ r := by omega
  have hDeq : D = r + k * Δ := by omega
  have hact' : r + k * Δ ≤ (c (aD a (r + k * Δ))).val := by rw [← hDeq]; exact hcon
  have hcb := chain_bound_from hab h hΔ (by omega) hr_ge k hact'
  rw [← hDeq] at hcb
  have hM : (c (aD a r)).val ≤ M := by
    rw [hMdef, hrdef]
    exact Finset.le_sup (f := fun r => (c (aD a (D₀ + r))).val) (Finset.mem_range.mpr hr0lt)
  have hDMk : D ≤ M + k := le_trans hcon (le_trans hcb (by omega))
  have h2k : 2 * k ≤ k * Δ := by nlinarith [hΔ2, Nat.zero_le k]
  have hkM : k ≤ M := by
    have hkΔ : k * Δ ≤ M + k := by omega
    omega
  have hkMΔ : k * Δ ≤ M * Δ := by
    have := Nat.mul_le_mul_right (k := Δ) hkM
    simpa using this
  have hTexp : (M + 1) * Δ = M * Δ + Δ := by ring
  -- D = r + kΔ = D₀ + r0 + kΔ ≤ D₀ + (Δ-1) + MΔ < D₀ + (M+1)Δ = T ≤ D.
  omega

/-! ### Δ = 1 floored ascending branch -/

/-- **Threshold `indist_ascending_Delta1`.**  For `(a, a+1)`, if `IndistFrom` holds with floor
    `D₀`, displacement `D₀` is active, and the first step at `D₀` ascends, then the a-chain
    ascends from `D₀`: `c(a + D₀ + k).val = c(a + D₀).val + k`. -/
lemma indistFrom_ascending_Delta1 {c : Perm} {a b : ℕ+} (hb : b.val = a.val + 1)
    (hab : a < b) {D₀ : ℕ} (h : IndistFrom c a b D₀)
    (hact0 : D₀ ≤ (c (aD a D₀)).val)
    (hσ0 : (c (aD a D₀)).val + 1 = (c (aD a (D₀ + 1))).val) :
    ∀ k : ℕ, (c (aD a (D₀ + k))).val = (c (aD a D₀)).val + k := by
  have hbridge : ∀ D : ℕ, aD b D = aD a (D + 1) := by
    intro D; apply Subtype.ext; show b.val + D = a.val + (D + 1); omega
  suffices h2 : ∀ k : ℕ,
      (c (aD a (D₀ + k))).val = (c (aD a D₀)).val + k ∧
      (c (aD a (D₀ + (k + 1)))).val = (c (aD a D₀)).val + (k + 1) by
    intro k; exact (h2 k).1
  intro k
  induction k with
  | zero =>
      refine ⟨by simp, ?_⟩
      have : D₀ + (0 + 1) = D₀ + 1 := by omega
      rw [this, ← hσ0]
  | succ m ih =>
      obtain ⟨hm, hm1⟩ := ih
      refine ⟨hm1, ?_⟩
      -- Activity of displacement D₀ + (m+1).
      have h_a_ge : (D₀ + (m + 1)) ≤ (c (aD a (D₀ + (m + 1)))).val := by rw [hm1]; omega
      have hD₀le : D₀ ≤ D₀ + (m + 1) := by omega
      have h_b_ge : (D₀ + (m + 1)) ≤ (c (aD b (D₀ + (m + 1)))).val :=
        (good_symm_from h hD₀le).mp h_a_ge
      have hcons := (indist_consec_from hab h hD₀le h_a_ge h_b_ge).1
      rw [hbridge (D₀ + (m + 1))] at hcons
      have hstep_eq : D₀ + (m + 1) + 1 = D₀ + (m + 1 + 1) := by omega
      rw [hstep_eq] at hcons
      rcases hcons with hasc | hdesc
      · rw [← hasc, hm1]; ring
      · exfalso
        -- descending here would give c(a + D₀ + (m+2)) = c(a + D₀ + m), contradicting injectivity
        have h_eq_val : (c (aD a (D₀ + (m + 1 + 1)))).val = (c (aD a (D₀ + m))).val := by
          rw [hm]; omega
        have h_eq : c (aD a (D₀ + (m + 1 + 1))) = c (aD a (D₀ + m)) := Subtype.ext h_eq_val
        have h_pos_eq : aD a (D₀ + (m + 1 + 1)) = aD a (D₀ + m) := c.injective h_eq
        have hcontra : a.val + (D₀ + (m + 1 + 1)) = a.val + (D₀ + m) := by
          have := congrArg (fun (p : ℕ+) => p.val) h_pos_eq
          simpa [aD_val] using this
        omega

/-- **Threshold `indist_Delta1_pos`.**  Ascending Δ=1 from floor `D₀` gives eventual identity
    from cell `a + D₀`. -/
lemma indistFrom_Delta1_pos {c : Perm} {a b : ℕ+} (hb : b.val = a.val + 1)
    (hab : a < b) {D₀ : ℕ} (h : IndistFrom c a b D₀)
    (hact0 : D₀ ≤ (c (aD a D₀)).val)
    (hσ0 : (c (aD a D₀)).val + 1 = (c (aD a (D₀ + 1))).val) :
    ∀ n : ℕ+, (aD a D₀) ≤ n → c n = n := by
  have hasc := indistFrom_ascending_Delta1 hb hab h hact0 hσ0
  apply flat_Delta_one (Q := aD a D₀)
  intro q hq hqpos
  left
  -- displacement of q relative to a, written as D₀ + (q - (a+D₀))
  set D := q.val - a.val with hD
  have hqge : a.val + D₀ ≤ q.val := hq
  have hqval : q.val = a.val + D := by omega
  have hDge : D₀ ≤ D := by omega
  set kk := D - D₀ with hkk
  have hDeq : D = D₀ + kk := by omega
  have hq_eq : aD a D = q := by
    apply Subtype.ext; show a.val + D = q.val; omega
  have hq1_eq : aD a (D + 1) = ⟨q.val + 1, hqpos⟩ := by
    apply Subtype.ext; show a.val + (D + 1) = q.val + 1; omega
  have e1 := hasc kk
  have e2 := hasc (kk + 1)
  rw [← hDeq] at e1
  have hDeq1 : D₀ + (kk + 1) = D + 1 := by omega
  rw [hDeq1] at e2
  rw [hq_eq] at e1
  rw [hq1_eq] at e2
  rw [e2, e1]
  omega

/-! ### Δ = 1 floored descending branch -/

/-- **Threshold `indist_Delta1_neg`.**  For `(a, a+1)`, a descending start at an active floor
    `D₀` is impossible.

If *every* displacement `≥ D₀` were active, the a-chain `f k = c(a + D₀ + k).val` would be an
injective ±1 walk (`indist_consec_from` + `good_symm_from`), hence ascending
(`pm1_injective_ascending`) — contradicting the descending start `hσ0`.  So some displacement
`≥ D₀` is bad; bad propagates forward (Δ = 1), so cofinitely many displacements are bad and
`cofinitely_bad_impossible_from` closes it. -/
lemma indistFrom_Delta1_neg {c : Perm} {a b : ℕ+} (hb : b.val = a.val + 1)
    (hab : a < b) {D₀ : ℕ} (h : IndistFrom c a b D₀)
    (hact0 : D₀ ≤ (c (aD a D₀)).val)
    (hσ0 : (c (aD a (D₀ + 1))).val + 1 = (c (aD a D₀)).val) :
    False := by
  have hbridge : ∀ D : ℕ, aD b D = aD a (D + 1) := by
    intro D; apply Subtype.ext; show b.val + D = a.val + (D + 1); omega
  -- **Forward bad propagation (Δ = 1).**
  have hbad_fwd : ∀ k j : ℕ, (c (aD a (D₀ + k))).val < D₀ + k →
      (c (aD a (D₀ + k + j))).val < D₀ + k + j := by
    intro k j
    induction j with
    | zero => simpa using id
    | succ m ih =>
        intro hk
        have ihm := ih hk
        have hD₀le : D₀ ≤ D₀ + k + m := by omega
        have hbp := bad_D_propagates_from h hD₀le ihm
        rw [hbridge (D₀ + k + m)] at hbp
        have he : D₀ + k + m + 1 = D₀ + k + (m + 1) := by omega
        rw [he] at hbp
        omega
  -- **Existence of a bad displacement ≥ D₀** (else the ascending walk contradicts `hσ0`).
  have hexbad : ∃ k : ℕ, (c (aD a (D₀ + k))).val < D₀ + k := by
    by_contra hall
    push_neg at hall
    -- All displacements ≥ D₀ are active; build the ±1 walk and show it ascends.
    set f : ℕ → ℕ := fun k => (c (aD a (D₀ + k))).val with hf
    have hf_inj : Function.Injective f := by
      intro k1 k2 hk
      simp only [hf] at hk
      have hc : c (aD a (D₀ + k1)) = c (aD a (D₀ + k2)) := Subtype.ext hk
      have hpe := c.injective hc
      have : a.val + (D₀ + k1) = a.val + (D₀ + k2) := by
        have := congrArg (fun (m : ℕ+) => m.val) hpe; simpa [aD_val] using this
      omega
    have hf_step : ∀ k, f (k + 1) = f k + 1 ∨ f (k + 1) + 1 = f k := by
      intro k
      have hD₀le : D₀ ≤ D₀ + k := by omega
      have h_a_ge : (D₀ + k) ≤ (c (aD a (D₀ + k))).val := hall k
      have h_b_ge : (D₀ + k) ≤ (c (aD b (D₀ + k))).val := (good_symm_from h hD₀le).mp h_a_ge
      have hcons := (indist_consec_from hab h hD₀le h_a_ge h_b_ge).1
      rw [hbridge (D₀ + k)] at hcons
      have he : D₀ + k + 1 = D₀ + (k + 1) := by omega
      rw [he] at hcons
      simp only [hf]
      rcases hcons with h1 | h1
      · left; omega
      · right; omega
    have hasc := pm1_injective_ascending f hf_inj hf_step 0
    -- f 1 = f 0 + 1 ascending, but hσ0 says descending.
    have hf0 : f 0 = (c (aD a D₀)).val := by simp only [hf]; congr 1
    have hf1 : f 1 = (c (aD a (D₀ + 1))).val := by simp only [hf]
    rw [hf0, hf1] at hasc
    -- hasc : c(a+D₀+1).val = c(a+D₀).val + 1, but hσ0 : c(a+D₀+1)+1 = c(a+D₀)
    omega
  -- **Finish via cofinitely-bad.**
  obtain ⟨k, hk⟩ := hexbad
  apply cofinitely_bad_impossible_from (a := a) (T := D₀ + k)
  intro D hD
  obtain ⟨j, rfl⟩ : ∃ j, D = D₀ + k + j := ⟨D - (D₀ + k), by omega⟩
  exact hbad_fwd k j hk

/-! ### Δ = 1 floored bad branch -/

/-- **Threshold `Δ = 1` bad start.**  For `(a, a+1)`, if displacement `D₀` is *below threshold*
    (`c(a+D₀) < D₀`), then every `D ≥ D₀` is bad, contradicting injectivity. -/
lemma indistFrom_Delta1_bad {c : Perm} {a b : ℕ+} (hb : b.val = a.val + 1)
    (hab : a < b) {D₀ : ℕ} (h : IndistFrom c a b D₀)
    (hbad0 : (c (aD a D₀)).val < D₀) : False := by
  have hbridge : ∀ D : ℕ, aD b D = aD a (D + 1) := by
    intro D; apply Subtype.ext; show b.val + D = a.val + (D + 1); omega
  -- All displacements `D ≥ D₀` are bad, by induction on `D - D₀`.
  have hallbad : ∀ k : ℕ, (c (aD a (D₀ + k))).val < D₀ + k := by
    intro k
    induction k with
    | zero => simpa using hbad0
    | succ m ih =>
        have hD₀le : D₀ ≤ D₀ + m := by omega
        have hbp := bad_D_propagates_from h hD₀le ih
        -- hbp : c(b + (D₀+m)) < D₀+m, and b+(D₀+m) = a+(D₀+m+1)
        rw [hbridge (D₀ + m)] at hbp
        have he : D₀ + m + 1 = D₀ + (m + 1) := by omega
        rw [he] at hbp
        omega
  apply cofinitely_bad_impossible_from (a := a) (T := D₀)
  intro D hD
  obtain ⟨k, rfl⟩ : ∃ k, D = D₀ + k := ⟨D - D₀, by omega⟩
  exact hallbad k

/-! ### Master floored Lemma A -/

/-- **Threshold Lemma A.**  `IndistFrom c a b D₀` (signal-agreement at every displacement
    `≥ D₀`) for a pair `a < b` forces `c` to be eventually identity.

The case split mirrors `Indistinguishable_implies_eventually_identity`, run with the floor:

* `Δ ≥ 2`: `indistFrom_Delta_ge_2_impossible` (cofinitely-bad kill) ⇒ `False` ⇒ EI vacuously.
* `Δ = 1`, displacement `D₀` *bad*: `indistFrom_Delta1_bad` ⇒ `False` ⇒ EI vacuously.
* `Δ = 1`, `D₀` active, descending start: `indistFrom_Delta1_neg` ⇒ `False` ⇒ EI vacuously.
* `Δ = 1`, `D₀` active, ascending start: `indistFrom_Delta1_pos` ⇒ EI from cell `a + D₀`. -/
theorem IndistFrom_implies_EventuallyIdentity {c : Perm} {a b : ℕ+} (hab : a < b) {D₀ : ℕ}
    (h : IndistFrom c a b D₀) : EventuallyIdentity c := by
  set Δ : ℕ := b.val - a.val with hΔ_def
  have hΔ_pos : 1 ≤ Δ := by
    have h_ab_val : a.val < b.val := hab
    omega
  have hab' : a.val < b.val := hab
  have hbΔ : b.val = a.val + Δ := by omega
  rcases eq_or_lt_of_le hΔ_pos with hΔ_eq | hΔ_ge_2
  · -- Δ = 1.
    have hΔ_eq_1 : Δ = 1 := hΔ_eq.symm
    have hb1 : b.val = a.val + 1 := by omega
    by_cases hbad0 : (c (aD a D₀)).val < D₀
    · -- bad start ⇒ False ⇒ EI vacuously.
      exact (indistFrom_Delta1_bad hb1 hab h hbad0).elim
    · push_neg at hbad0
      -- active start: split on σ(D₀).
      have hD₀le : D₀ ≤ D₀ := le_refl _
      have hbridge0 : aD b D₀ = aD a (D₀ + 1) := by
        apply Subtype.ext; show b.val + D₀ = a.val + (D₀ + 1); omega
      have hb_ge0 : D₀ ≤ (c (aD b D₀)).val := (good_symm_from h hD₀le).mp hbad0
      have hsig0 := (indist_consec_from hab h hD₀le hbad0 hb_ge0).1
      rw [hbridge0] at hsig0
      rcases hsig0 with hpos | hneg
      · -- ascending ⇒ EI from a + D₀.
        exact ⟨aD a D₀, indistFrom_Delta1_pos hb1 hab h hbad0 hpos⟩
      · -- descending ⇒ False ⇒ EI vacuously.
        exact (indistFrom_Delta1_neg hb1 hab h hbad0 hneg).elim
  · -- Δ ≥ 2 ⇒ False ⇒ EI vacuously.
    have hΔ_ge_2' : 2 ≤ Δ := hΔ_ge_2
    exact (indistFrom_Delta_ge_2_impossible hab h hbΔ hΔ_ge_2').elim

end TrolleyRetrieval
