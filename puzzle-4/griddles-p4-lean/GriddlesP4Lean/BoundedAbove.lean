import GriddlesP4Lean.Defs
import Mathlib.Data.PNat.Interval

/-!
# Descent-cofinite (and ascent-cofinite) permutations are eventually identity

This file proves the "cut" lemma needed by the bounded-above ⟹ band-recurrence argument:

* `descent_cofinite_imp_EI` — if `(c n).val ≤ n.val` for all `n ≥ N`, then `c`
  is eventually the identity.
* `ascent_cofinite_imp_EI` — the mirror image (`(c n).val ≥ n.val` cofinitely ⟹ EI),
  obtained by applying the first lemma to `c.symm`.

**Proof idea (the cut argument).**  Let `B` bound `(c n).val` over the finite initial
segment `n < N`.  For any `M ≥ max(N, B)`, the permutation `c` maps the finite set
`{1,…,M}` into itself (descents past `N`; the bound `B` below `N`).  Being injective on a
finite set of equal cardinality it is *onto* `{1,…,M}`.  Hence `c (M+1)` cannot land inside
`{1,…,M}` (those values are already images of `{1,…,M}` and `M+1 ∉ {1,…,M}`), so
`(c (M+1)).val > M`; together with the descent bound `(c (M+1)).val ≤ M+1` this forces
`c (M+1) = M+1`.  Applying this with `M = n-1` for every `n` past the threshold gives EI.
-/

namespace TrolleyRetrieval

variable {c : Perm}

/-- A finite upper bound for `(c n).val` over the initial segment `1 ≤ n ≤ N`. -/
private def initBound (c : Perm) (N : ℕ+) : ℕ :=
  (Finset.Icc (1 : ℕ+) N).sup (fun n => (c n).val)

private lemma le_initBound (c : Perm) (N : ℕ+) {n : ℕ+} (hn : n ≤ N) :
    (c n).val ≤ initBound c N := by
  apply Finset.le_sup (f := fun n => (c n).val)
  simp only [Finset.mem_Icc]
  exact ⟨n.one_le, hn⟩

/-- **Core cut step.**  Under the descent hypothesis past `N`, if `M` is at least `N` and
    at least the initial-segment bound `B`, then `c` fixes `M+1`. -/
private lemma cut_fixes_succ (N : ℕ+)
    (h : ∀ n : ℕ+, N ≤ n → (c n).val ≤ n.val)
    (M : ℕ+) (hMN : N ≤ M) (hMB : initBound c N ≤ M.val) :
    c (M + 1) = M + 1 := by
  classical
  set s : Finset ℕ+ := Finset.Icc (1 : ℕ+) M with hs
  -- `c` maps `s` into `s`.
  have hmaps : Set.MapsTo (fun n => c n) (↑s) (↑s) := by
    intro n hn
    simp only [hs, Finset.coe_Icc, Set.mem_Icc] at hn ⊢
    refine ⟨(c n).one_le, ?_⟩
    -- `(c n).val ≤ M.val`, hence `c n ≤ M`.
    have hval : (c n).val ≤ M.val := by
      by_cases hNn : N ≤ n
      · exact le_trans (h n hNn) (by exact_mod_cast hn.2)
      · -- `n < N`
        have : n ≤ N := le_of_lt (not_le.mp hNn)
        exact le_trans (le_initBound c N this) hMB
    exact_mod_cast hval
  -- `c` is injective on `s`.
  have hinj : Set.InjOn (fun n => c n) (↑s) := fun a _ b _ hab => c.injective hab
  -- equal cardinalities (`s = s`).
  have hcard : s.card ≤ s.card := le_refl _
  -- hence `c` is surjective onto `s`.
  have hsurj : Set.SurjOn (fun n => c n) (↑s) (↑s) :=
    Finset.surjOn_of_injOn_of_card_le (fun n => c n) hmaps hinj hcard
  -- Now show `c (M+1) = M+1`.
  have hMN' : N ≤ M + 1 := le_trans hMN (by exact_mod_cast Nat.le_succ M.val)
  have hle : (c (M + 1)).val ≤ (M + 1).val := h (M + 1) hMN'
  -- `c (M+1) ∉ s`, otherwise injectivity gives a preimage `≤ M = M+1`, contradiction.
  have hnotmem : c (M + 1) ∉ s := by
    intro hmem
    have : c (M + 1) ∈ Set.image (fun n => c n) (↑s) := hsurj hmem
    obtain ⟨a, ha, hca⟩ := this
    have : a = M + 1 := c.injective hca
    rw [this] at ha
    simp only [hs, Finset.coe_Icc, Set.mem_Icc] at ha
    exact absurd ha.2 (by exact_mod_cast Nat.not_succ_le_self M.val)
  -- `c (M+1) ∉ s` means `(c (M+1)).val > M.val`.
  have hgt : M.val < (c (M + 1)).val := by
    by_contra hcon
    push_neg at hcon
    apply hnotmem
    simp only [hs, Finset.mem_Icc]
    exact ⟨(c (M + 1)).one_le, by
      have : (c (M + 1)).val ≤ M.val := hcon
      exact_mod_cast this⟩
  -- combine: `M < c(M+1) ≤ M+1` forces equality.
  have : (c (M + 1)).val = (M + 1).val := by
    have hsucc : (M + 1).val = M.val + 1 := by rfl
    omega
  exact PNat.coe_injective this

/-- **Lemma 1 (descent-cofinite ⟹ eventually identity).**  If `(c n).val ≤ n.val` for
    all `n ≥ N`, then `c` is eventually the identity. -/
theorem descent_cofinite_imp_EI (c : Perm) (N : ℕ+)
    (h : ∀ n : ℕ+, N ≤ n → (c n).val ≤ n.val) :
    EventuallyIdentity c := by
  classical
  -- threshold: one past `max N B`.
  set B : ℕ := initBound c N with hB
  set Mbase : ℕ+ := max N ⟨B + 1, Nat.succ_pos B⟩ with hMbase
  refine ⟨Mbase + 1, ?_⟩
  intro n hn
  -- `n ≥ Mbase + 1`, so `M := n - 1` satisfies `M ≥ Mbase`, and `n = M + 1`.
  -- Build `M` as a `ℕ+`.
  have hn2 : 2 ≤ n.val := by
    have h1 : (Mbase + 1).val = Mbase.val + 1 := rfl
    have : (Mbase + 1) ≤ n := hn
    have hMb : 1 ≤ Mbase.val := Mbase.one_le
    have := (PNat.coe_le_coe (Mbase + 1) n).2 this
    omega
  set M : ℕ+ := ⟨n.val - 1, by omega⟩ with hM
  have hMsucc : M + 1 = n := by
    apply PNat.coe_injective
    show (M + 1).val = n.val
    have : (M + 1).val = M.val + 1 := rfl
    rw [this]
    show (n.val - 1) + 1 = n.val
    omega
  -- `M ≥ Mbase ≥ N` and `M.val ≥ B`.
  have hMge : Mbase ≤ M := by
    have hbig : (Mbase + 1) ≤ n := hn
    have := (PNat.coe_le_coe (Mbase + 1) n).2 hbig
    apply (PNat.coe_le_coe Mbase M).1
    show Mbase.val ≤ M.val
    show Mbase.val ≤ n.val - 1
    have : (Mbase + 1).val = Mbase.val + 1 := rfl
    omega
  have hMN : N ≤ M := le_trans (le_max_left _ _) hMge
  have hMB : B ≤ M.val := by
    have hBle : (⟨B + 1, Nat.succ_pos B⟩ : ℕ+) ≤ Mbase := le_max_right _ _
    have h1 : (⟨B + 1, Nat.succ_pos B⟩ : ℕ+).val ≤ Mbase.val :=
      (PNat.coe_le_coe _ _).2 hBle
    have h2 : Mbase.val ≤ M.val := (PNat.coe_le_coe _ _).2 hMge
    simp only at h1
    omega
  -- apply the cut step.
  have := cut_fixes_succ N h M hMN hMB
  rw [hMsucc] at this
  exact this

/-- **Lemma 1, mirror (ascent-cofinite ⟹ eventually identity).**  If `(c n).val ≥ n.val`
    for all `n ≥ N`, then `c` is eventually the identity.  Proved by applying the descent
    version to `c.symm`. -/
theorem ascent_cofinite_imp_EI (c : Perm) (N : ℕ+)
    (h : ∀ n : ℕ+, N ≤ n → n.val ≤ (c n).val) :
    EventuallyIdentity c := by
  classical
  -- `c.symm` is descent-cofinite past `N`.
  have hdesc : ∀ m : ℕ+, N ≤ m → (c.symm m).val ≤ m.val := by
    intro m hm
    -- want `(c.symm m).val ≤ m.val`.  By contradiction, if `m.val < (c.symm m).val`,
    -- let `n := c.symm m`; then `N ≤ m ≤ ... `.  Use the ascent hypothesis at `n`.
    by_contra hcon
    push_neg at hcon
    set n : ℕ+ := c.symm m with hn
    have hcn : c n = m := by rw [hn]; exact c.apply_symm_apply m
    -- `m.val < n.val`, so `N ≤ m ≤ n`, hence `N ≤ n`.
    have hmn : m.val < n.val := hcon
    have hNn : N ≤ n := by
      have : m ≤ n := by
        apply (PNat.coe_le_coe m n).1; omega
      exact le_trans hm this
    have := h n hNn
    rw [hcn] at this
    -- `n.val ≤ m.val` contradicts `m.val < n.val`.
    omega
  obtain ⟨N', hN'⟩ := descent_cofinite_imp_EI c.symm N hdesc
  -- `c.symm` is EI past `N'`; hence so is `c`.
  refine ⟨N', ?_⟩
  intro n hn
  have hsymm : c.symm n = n := hN' n hn
  -- apply `c` to both sides.
  have : c (c.symm n) = c n := by rw [hsymm]
  rw [c.apply_symm_apply] at this
  exact this.symm

end TrolleyRetrieval
