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

/-! ### Main statement -/

/-- **Lemma A (forward).**  If a pair `(a, b)` with `a < b` is indistinguishable, then
    `b = a + 1` and `c` is eventually identity from position `a`. -/
theorem Indistinguishable_implies_eventually_identity
    {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) :
    (b = a + 1) ∧ (∀ n : ℕ+, a ≤ n → c n = n) := by
  sorry

/-- **Lemma A (corollary used by the winning direction).**  If `c` is not eventually
    identity, then *no* pair of starting cells is indistinguishable. -/
theorem not_eventually_identity_implies_distinguishable
    {c : Perm} (h : ¬ EventuallyIdentity c) :
    ∀ a b : ℕ+, a < b → ¬ Indistinguishable c a b := by
  intro a b hab h_indist
  obtain ⟨_, h_ei⟩ := Indistinguishable_implies_eventually_identity hab h_indist
  exact h ⟨a, h_ei⟩

end TrolleyRetrieval
