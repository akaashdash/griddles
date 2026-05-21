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

/-- **Auxiliary sub-claim**: σ(D) is always `+1` (i.e. `c(b+D).val = c(a+D).val + 1`).

This is the crux of LemmaA.  The full argument (verified by hand on multiple examples,
e.g. `a=5, b=6, c(5)=7` forcing the descending chain `7,6,5,4,3,2,1` then a pigeonhole
collapse) runs as follows.

**Step 1 — σ propagates.**  By `indist_consec` at every *good* `D` (where both c-values
are `≥ D`), the values `c(a+D)` and `c(b+D) = c(a+D+Δ)` are consecutive, so
`σ(D) := c(a+D+Δ).val − c(a+D).val ∈ {−1, +1}`.  If `σ(D) = −1` at a good `D`, then at
the next good step `σ(D+Δ) = −1` too: otherwise `c(a+D+2Δ).val = c(a+D).val`, and by
injectivity `a+D+2Δ = a+D`, impossible (`Δ ≥ 1`).

**Step 2 — σ(0) = −1 is impossible.**  Suppose `σ(0) = −1`.  By Step 1 the chain
`c(a+kΔ).val = c(a).val − k` descends through `c(a).val, c(a).val−1, …` while `D = kΔ`
stays good (i.e. while `c(a).val − k ≥ kΔ`).  These positions use up the value-block
`{c(a).val − k_max, …, c(a).val}`.  Once `D` becomes *bad* (c-value `< D`), the signal
from `a+D` is permanently "Yes" at every valid time, so `Indistinguishable` forces the
signal from `b+D = a+D+Δ` to be "Yes" too, giving `c(a+D+Δ).val < D`.  Iterating this
bad-`D` constraint forces *infinitely many* positions into the finite value-set below
the chain's floor, contradicting injectivity (pigeonhole).

**Step 3 — extend to all D.**  By Step 2, `σ(0) = +1`.  The same argument applied with
basepoint `a + D` (rather than `a`) gives `σ(D) = +1` for every `D` — equivalently, the
configuration is forced into the ascending regime everywhere.

A full Lean formalization needs: (i) a descending-chain iterate analogous to
`c_iter_Delta`, and (ii) the pigeonhole step bounding how many positions can map into
a fixed finite value-set.  Both are routine but lengthy; left as the final gap. -/
private lemma sigma_eq_pos_one {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) (D : ℕ) :
    (c ⟨a.val + D, aD_pos a D⟩).val + 1 = (c ⟨b.val + D, aD_pos b D⟩).val := by
  sorry

/-- **Auxiliary**: the key combinatorial content of LemmaA — under `Indistinguishable`,
    the shift relation `c (n + Δ) = c n + 1` holds from position `a` onward (with
    `Δ := b.val − a.val`).

The proof reduces to `sigma_eq_pos_one`: for every `D`, σ at D is `+1`, i.e.
`(c (b + D)).val = (c (a + D)).val + 1`. -/
lemma shift_relation_of_indist {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) :
    ∀ n : ℕ+, a ≤ n →
      ∀ (h_pos : 0 < n.val + (b.val - a.val)),
        (c ⟨n.val + (b.val - a.val), h_pos⟩).val = (c n).val + 1 := by
  intro n han h_pos
  set D : ℕ := n.val - a.val with hD_def
  have hD : n.val = a.val + D := by
    have : a.val ≤ n.val := han
    omega
  have h_pos_b : 0 < b.val + D := aD_pos b D
  -- Identify n with ⟨a.val + D, _⟩ and the target with ⟨b.val + D, _⟩.
  have h_n_pnat_eq : n = ⟨a.val + D, aD_pos a D⟩ := Subtype.ext hD
  have h_target_pnat_eq :
      (⟨n.val + (b.val - a.val), h_pos⟩ : ℕ+) = ⟨b.val + D, h_pos_b⟩ := by
    apply Subtype.ext
    show n.val + (b.val - a.val) = b.val + D
    have h_ab_val : a.val ≤ b.val := le_of_lt hab
    omega
  -- Conclude using sigma_eq_pos_one.
  have h_sigma := sigma_eq_pos_one hab h D
  -- h_sigma : (c ⟨a.val + D, _⟩).val + 1 = (c ⟨b.val + D, _⟩).val
  have h_c_n : (c n).val = (c ⟨a.val + D, aD_pos a D⟩).val := by
    rw [h_n_pnat_eq]
  have h_c_target : (c ⟨n.val + (b.val - a.val), h_pos⟩).val =
                    (c ⟨b.val + D, h_pos_b⟩).val := by
    rw [h_target_pnat_eq]
  rw [h_c_n, h_c_target, ← h_sigma]

/-! ### Main statement -/

/-- **Lemma A (forward).**  If a pair `(a, b)` with `a < b` is indistinguishable, then
    `b = a + 1` and `c` is eventually identity from position `a`.

The proof combines:

* `indist_consec` — for `D` such that both c-values are `≥ D`, the values are
  consecutive integers with the parity condition.
* `shift_relation_of_indist` — for sufficiently large `n`, `c (n + Δ) = c n + 1`.
* If `Δ ≥ 2`, `shift_Delta_ge_2_contradiction` derives False.
* If `Δ = 1`, `shift_one_implies_eventually_identity` finishes. -/

theorem Indistinguishable_implies_eventually_identity
    {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) :
    (b = a + 1) ∧ (∀ n : ℕ+, a ≤ n → c n = n) := by
  set Δ : ℕ := b.val - a.val with hΔ_def
  have hΔ_pos : 1 ≤ Δ := by
    have h_ab_val : a.val < b.val := hab
    omega
  -- The shift relation `c(n+Δ) = c(n)+1` holds for n ≥ a.
  have h_shift_rel := shift_relation_of_indist hab h
  set N : ℕ+ := a with hN_def
  -- Case split: Δ = 1 vs Δ ≥ 2.
  rcases eq_or_lt_of_le hΔ_pos with hΔ_eq | hΔ_ge_2
  · -- Δ = 1.  We have c(n + 1) = c n + 1 for n ≥ N (via the shift relation), so
    -- `shift_one_implies_eventually_identity` gives c n = n for n ≥ N.
    have hΔ_eq_1 : Δ = 1 := hΔ_eq.symm
    -- First, the shift relation at "+ Δ" is "+ 1" since Δ = 1.
    have h_shift_one : ∀ n : ℕ+, N ≤ n → c (n + 1) = c n + 1 := by
      intro n hN_le_n
      have h_pos : 0 < n.val + Δ := by
        have := n.property
        omega
      have h_rel := h_shift_rel n hN_le_n h_pos
      -- (c ⟨n.val + Δ, _⟩).val = (c n).val + 1 ; with Δ = 1, this position is `n + 1`.
      have h_eq_pnat : (⟨n.val + Δ, h_pos⟩ : ℕ+) = n + (1 : ℕ+) := by
        apply Subtype.ext
        show n.val + Δ = (n + (1 : ℕ+)).val
        have h_pnat_add : (n + (1 : ℕ+)).val = n.val + 1 := rfl
        rw [h_pnat_add, hΔ_eq_1]
      rw [h_eq_pnat] at h_rel
      -- h_rel : (c (n + 1)).val = (c n).val + 1
      apply Subtype.ext
      show (c (n + (1 : ℕ+))).val = (c n + (1 : ℕ+)).val
      have h_plus : ((c n + (1 : ℕ+))).val = (c n).val + 1 := rfl
      rw [h_plus]
      exact h_rel
    -- Apply shift_one_implies_eventually_identity.  Since N = a, this gives c n = n
    -- for all n ≥ a.
    have h_id : ∀ n : ℕ+, N ≤ n → c n = n := shift_one_implies_eventually_identity h_shift_one
    -- Conclude b = a + 1.
    have h_b_eq : b = a + 1 := by
      apply Subtype.ext
      show b.val = (a + (1 : ℕ+)).val
      have h_pnat_add : (a + (1 : ℕ+)).val = a.val + 1 := rfl
      rw [h_pnat_add]
      omega
    exact ⟨h_b_eq, h_id⟩
  · -- Δ ≥ 2.  Apply shift_Delta_ge_2_contradiction with threshold N = a.
    have hΔ_ge_2' : 2 ≤ Δ := hΔ_ge_2
    have h_for_lemma : ∀ n : ℕ+, N ≤ n → ∀ (h_pos : 0 < n.val + Δ),
        (c ⟨n.val + Δ, h_pos⟩).val = (c n).val + 1 :=
      fun n hN_le_n h_pos => h_shift_rel n hN_le_n h_pos
    exact (shift_Delta_ge_2_contradiction hΔ_ge_2' h_for_lemma).elim

/-- **Lemma A (corollary used by the winning direction).**  If `c` is not eventually
    identity, then *no* pair of starting cells is indistinguishable. -/
theorem not_eventually_identity_implies_distinguishable
    {c : Perm} (h : ¬ EventuallyIdentity c) :
    ∀ a b : ℕ+, a < b → ¬ Indistinguishable c a b := by
  intro a b hab h_indist
  obtain ⟨_, h_ei⟩ := Indistinguishable_implies_eventually_identity hab h_indist
  exact h ⟨a, h_ei⟩

end TrolleyRetrieval
