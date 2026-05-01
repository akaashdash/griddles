import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import GriddlesP1Lean.Defs
import GriddlesP1Lean.Separability
import GriddlesP1Lean.Slopes

/-!
# Bijections for Fixed-Point Counting

This file proves the two key bijections needed for Burnside's lemma:

## 180°-fixed colorings (`equiv_fixed180`)

For odd n = 2m+1, there is a bijection:
  { f : proper coloring | f is 180°-fixed }  ≃  ZMod 3 × (Fin m → NZMod3) × (Fin m → NZMod3)

**Forward map**: extract base = f(0,0), h-slopes h_j = f(0,j+1)−f(0,j) for j<m,
v-slopes v_k = f(k+1,0)−f(k,0) for k<m.

**Backward map**: given (base, hs, vs), set f(r,c) = base + mkCumSum(hs)(c) + mkCumSum(vs)(r).
- AdjOk: differences are ext_slope values, which are nonzero.
- RichOk: 2×2 blocks have all 3 colors (by `richness_from_slopes`).
- FixedBy180: palindromicity of mkCumSum gives f(n−1−r, n−1−c) = f(r,c).

**Left inverse** (invFun ∘ toFun = id): the key insight is that mkCumSum of the extracted
slopes equals the telescoping sum f(0,c)−f(0,0). The proof uses:
- separability of f (from `vOffset_col_independent`)
- the 180° condition to derive that f(0, n−1−c) = f(0,c) (row-0 palindrome)
- the 180° condition to derive that f(n−1−r, 0) = f(r, 0) (column-0 palindrome)
- induction on c (for c ≤ m) and palindrome symmetry (for c > m)

**Right inverse** (toFun ∘ invFun = id): mkCumSum(j+1) − mkCumSum(j) = ext_slope(j) = hs(j).

## 90°-fixed colorings (`equiv_fixed90`)

For odd n = 2m+1 with 4∣(n−1), there is a bijection:
  { f : proper coloring | f is 90°-fixed }  ≃  ZMod 3 × (Fin m → NZMod3)

The 90° condition f(r,c) = f(n−1−c, r) forces D = R (same offsets for rows and columns),
so only one sequence of m free slopes is needed.

The proof reuses all the 180° machinery after observing that 90°-fixed ⟹ 180°-fixed.
Additionally, f(r,0) = f(0,r) follows from the 90° condition at c=0.
-/

namespace ChromaticRotations

/-! ### Simple cumulative sum (for unrestricted proper colorings)

For the bijection on *all* proper colorings, the n−1 slopes are fully free
(no palindrome constraint). We use a plain cumulative sum instead of the
palindrome-extending `mkCumSum`. -/

/-- Cumulative sum of unrestricted slopes: simpleCumSum hs c = Σ_{j < c} hs(j). -/
private noncomputable def simpleCumSum (n : ℕ) (hs : Fin (n - 1) → NZMod3) (c : Fin n) : ZMod 3 :=
  ∑ j : Fin c.val, (hs ⟨j.val, by have := j.isLt; have := c.isLt; omega⟩).val

private lemma simpleCumSum_zero (n : ℕ) (hn : 1 ≤ n) (hs : Fin (n - 1) → NZMod3) :
    simpleCumSum n hs ⟨0, hn⟩ = 0 := by
  simp [simpleCumSum]

private lemma simpleCumSum_succ (n : ℕ) (hs : Fin (n - 1) → NZMod3) (j : ℕ) (hj : j + 1 < n) :
    simpleCumSum n hs ⟨j + 1, hj⟩ =
    simpleCumSum n hs ⟨j, by omega⟩ + (hs ⟨j, by omega⟩).val := by
  simp only [simpleCumSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

/-- All proper colorings biject with (base, h-slopes, v-slopes) where the n−1 slopes
    per direction are all freely chosen from NZMod3 = {1, 2}.

    Unlike `equiv_fixed180`, there is no palindrome constraint here: every combination
    of nonzero slopes yields a valid proper coloring. The count is therefore
    3 × 2^(n−1) × 2^(n−1) = 3 × 2^(2(n−1)).

    Forward map: extract base = f(0,0), h-slopes from row 0, v-slopes from column 0.
    Backward map: f(r,c) = base + simpleCumSum(hs)(c) + simpleCumSum(vs)(r). -/
noncomputable def equiv_proper (n : ℕ) (hn : 1 ≤ n) :
    { f : Coloring n // AdjOk f ∧ RichOk f } ≃
    ZMod 3 × (Fin (n - 1) → NZMod3) × (Fin (n - 1) → NZMod3) :=
  let hn0 : 0 < n := hn
  { toFun := fun ⟨f, hadj, _⟩ =>
      (f ⟨0, hn0⟩ ⟨0, hn0⟩,
       fun j =>
        have hj_lt : j.val + 1 < n := by have := j.isLt; omega
        ⟨f ⟨0, hn0⟩ ⟨j.val + 1, hj_lt⟩ - f ⟨0, hn0⟩ ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩,
         sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩ ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ hj_lt))⟩,
       fun k =>
        have hk_lt : k.val + 1 < n := by have := k.isLt; omega
        ⟨f ⟨k.val + 1, hk_lt⟩ ⟨0, hn0⟩ - f ⟨k.val, Nat.lt_of_lt_pred k.isLt⟩ ⟨0, hn0⟩,
         sub_ne_zero.mpr (Ne.symm (hadj.2 ⟨k.val, Nat.lt_of_lt_pred k.isLt⟩ ⟨0, hn0⟩ hk_lt))⟩)
    invFun := fun (base, hs, vs) =>
      ⟨fun r c => base + simpleCumSum n hs c + simpleCumSum n vs r,
       -- AdjOk: horizontal difference = (hs c).val ≠ 0
       ⟨fun r c hc => by
          intro heq
          have hstep := simpleCumSum_succ n hs c.val hc
          have h1 := add_right_cancel heq
          have h2 := add_left_cancel h1
          have hne : (hs ⟨c.val, by omega⟩).val ≠ 0 := (hs ⟨c.val, by omega⟩).prop
          exact hne (by linear_combination -(h2.trans hstep)),
        -- AdjOk: vertical difference = (vs r).val ≠ 0
        fun r c hr => by
          intro heq
          have hstep := simpleCumSum_succ n vs r.val hr
          have h1 := add_left_cancel heq
          have hne : (vs ⟨r.val, by omega⟩).val ≠ 0 := (vs ⟨r.val, by omega⟩).prop
          exact hne (by linear_combination -(h1.trans hstep))⟩,
       -- RichOk: 2×2 block has all 3 colours (slopes are nonzero)
       fun r c hr hc => by
         have hh : (hs ⟨c.val, by omega⟩).val ≠ 0 := (hs ⟨c.val, by omega⟩).prop
         have hv : (vs ⟨r.val, by omega⟩).val ≠ 0 := (vs ⟨r.val, by omega⟩).prop
         have h1 : base + simpleCumSum n hs ⟨c.val + 1, hc⟩ + simpleCumSum n vs r =
             base + simpleCumSum n hs c + simpleCumSum n vs r +
             (hs ⟨c.val, by omega⟩).val := by
           rw [simpleCumSum_succ n hs c.val hc]; ring
         have h2 : base + simpleCumSum n hs c + simpleCumSum n vs ⟨r.val + 1, hr⟩ =
             base + simpleCumSum n hs c + simpleCumSum n vs r +
             (vs ⟨r.val, by omega⟩).val := by
           rw [simpleCumSum_succ n vs r.val hr]; ring
         have h3 : base + simpleCumSum n hs ⟨c.val + 1, hc⟩ +
             simpleCumSum n vs ⟨r.val + 1, hr⟩ =
             base + simpleCumSum n hs c + simpleCumSum n vs r +
             (hs ⟨c.val, by omega⟩).val + (vs ⟨r.val, by omega⟩).val := by
           rw [simpleCumSum_succ n hs c.val hc, simpleCumSum_succ n vs r.val hr]; ring
         show ({base + simpleCumSum n hs c + simpleCumSum n vs r,
                base + simpleCumSum n hs ⟨c.val + 1, hc⟩ + simpleCumSum n vs r,
                base + simpleCumSum n hs c + simpleCumSum n vs ⟨r.val + 1, hr⟩,
                base + simpleCumSum n hs ⟨c.val + 1, hc⟩ +
                  simpleCumSum n vs ⟨r.val + 1, hr⟩} : Finset (ZMod 3)).card = 3
         rw [h1, h2, h3]
         exact richness_from_slopes _ _ _ hh hv⟩
    left_inv := fun ⟨f, hadj, hrich⟩ => by
      -- Strategy: show simpleCumSum(extracted h-slopes)(c) = f(0,c) − f(0,0) by induction,
      -- then conclude via separability (vOffset_col_independent).
      simp only [Subtype.mk.injEq]
      let pc : ProperColoring n := ⟨f, hadj, hrich⟩
      -- sep: f(r,c) − f(0,c) = f(r,0) − f(0,0)  [separability]
      have sep : ∀ (r c : Fin n), f r c - f ⟨0, hn0⟩ c = f r ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ :=
        fun r c => vOffset_col_independent pc hn0 r c
      -- hcumR: the cumsum of extracted h-slopes equals f(0,c) − f(0,0), by induction
      have hcumR : ∀ (k : ℕ) (hk : k < n),
          simpleCumSum n (fun j =>
            have hj_lt : j.val + 1 < n := by have := j.isLt; omega
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, hj_lt⟩ -
             f ⟨0, hn0⟩ ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩
               hj_lt))⟩) ⟨k, hk⟩ =
          f ⟨0, hn0⟩ ⟨k, hk⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        intro k hk
        induction k with
        | zero => simp [simpleCumSum]
        | succ k ihk =>
          have hk' : k < n := by omega
          rw [simpleCumSum_succ n _ k hk]
          have heqk1 : (⟨k + 1, hk⟩ : Fin n) = ⟨k + 1, by omega⟩ := Fin.ext rfl
          rw [heqk1]
          linear_combination ihk hk'
      -- hcumD: the cumsum of extracted v-slopes equals f(r,0) − f(0,0), by induction
      have hcumD : ∀ (k : ℕ) (hk : k < n),
          simpleCumSum n (fun j =>
            have hj_lt : j.val + 1 < n := by have := j.isLt; omega
            ⟨f ⟨j.val + 1, hj_lt⟩ ⟨0, hn0⟩ -
             f ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ ⟨0, hn0⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.2
               ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ ⟨0, hn0⟩
               hj_lt))⟩) ⟨k, hk⟩ =
          f ⟨k, hk⟩ ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        intro k hk
        induction k with
        | zero => simp [simpleCumSum]
        | succ k ihk =>
          have hk' : k < n := by omega
          rw [simpleCumSum_succ n _ k hk]
          have heqk1 : (⟨k + 1, hk⟩ : Fin n) = ⟨k + 1, by omega⟩ := Fin.ext rfl
          rw [heqk1]
          linear_combination ihk hk'
      funext r c
      have hR := hcumR c.val c.isLt
      have hD := hcumD r.val r.isLt
      rw [hR, hD]
      linear_combination -(sep r c)
    right_inv := fun (base, hs, vs) => by
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · -- base: base + simpleCumSum hs ⟨0,_⟩ + simpleCumSum vs ⟨0,_⟩ = base
        rw [simpleCumSum_zero n hn hs, simpleCumSum_zero n hn vs]
        ring
      · -- h-slopes: the extracted slope at j equals hs j
        funext j
        apply Subtype.ext
        dsimp only
        rw [simpleCumSum_zero n hn vs]
        rw [simpleCumSum_succ n hs j.val (by have := j.isLt; omega)]
        have hfin : (⟨j.val, by have := j.isLt; omega⟩ : Fin (n - 1)) = j := Fin.ext rfl
        rw [hfin]; ring
      · -- v-slopes: the extracted slope at k equals vs k
        funext k
        apply Subtype.ext
        dsimp only
        rw [simpleCumSum_zero n hn hs]
        rw [simpleCumSum_succ n vs k.val (by have := k.isLt; omega)]
        have hfin : (⟨k.val, by have := k.isLt; omega⟩ : Fin (n - 1)) = k := Fin.ext rfl
        rw [hfin]; ring }

/-- 180°-fixed proper colorings biject with (base, m h-slopes, m v-slopes)
    where m = (n−1)/2 and each slope is nonzero. -/
noncomputable def equiv_fixed180 (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n) :
    { f : Coloring n // AdjOk f ∧ RichOk f ∧ FixedBy180 n f } ≃
    ZMod 3 × (Fin ((n - 1) / 2) → NZMod3) × (Fin ((n - 1) / 2) → NZMod3) :=
  let hn0 : 0 < n := by omega
  let m := (n - 1) / 2
  have hm : 2 * m + 1 = n := by obtain ⟨k, hk⟩ := hn; omega
  have hm_bound : m ≤ n - 1 := by omega
  { toFun := fun ⟨f, hadj, _, _⟩ =>
      (f ⟨0, hn0⟩ ⟨0, hn0⟩,
       fun j =>
        have hj_lt_n : j.val + 1 < n := by have := j.isLt; have := hm; omega
        ⟨f ⟨0, hn0⟩ ⟨j.val + 1, hj_lt_n⟩ -
         f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; have := hm; omega⟩,
         sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; have := hm; omega⟩
           hj_lt_n))⟩,
       fun k =>
        have hk_lt_n : k.val + 1 < n := by have := k.isLt; have := hm; omega
        ⟨f ⟨k.val + 1, hk_lt_n⟩ ⟨0, hn0⟩ -
         f ⟨k.val, by have := k.isLt; have := hm; omega⟩ ⟨0, hn0⟩,
         sub_ne_zero.mpr (Ne.symm (hadj.2 ⟨k.val, by have := k.isLt; have := hm; omega⟩ ⟨0, hn0⟩
           hk_lt_n))⟩)
    invFun := fun (base, hs, vs) =>
      ⟨fun r c => base + mkCumSum n m hm hs c + mkCumSum n m hm vs r,
       -- AdjOk: differences are ext_slope values, which are nonzero
       ⟨fun r c hc => by
          intro heq
          exact ext_slope_ne_zero n m hm hs ⟨c.val, by omega⟩ (by
            have hstep := mkCumSum_succ n m hm hs c.val hc
            have h1 := add_right_cancel heq
            have h2 := add_left_cancel h1
            linear_combination -(h2.trans hstep)),
        fun r c hr => by
          intro heq
          exact ext_slope_ne_zero n m hm vs ⟨r.val, by omega⟩ (by
            have hstep := mkCumSum_succ n m hm vs r.val hr
            have h1 := add_left_cancel heq
            linear_combination -(h1.trans hstep))⟩,
       -- RichOk: 2×2 block has all 3 colours because slopes are nonzero
       fun r c hr hc => by
         -- g(r,c) = a, g(r,c+1) = a+h, g(r+1,c) = a+v, g(r+1,c+1) = a+h+v
         -- where h = ext_slope hs c ≠ 0, v = ext_slope vs r ≠ 0
         have hh : ext_slope n m hm hs ⟨c.val, by omega⟩ ≠ 0 :=
           ext_slope_ne_zero n m hm hs ⟨c.val, by omega⟩
         have hv : ext_slope n m hm vs ⟨r.val, by omega⟩ ≠ 0 :=
           ext_slope_ne_zero n m hm vs ⟨r.val, by omega⟩
         have h1 : base + mkCumSum n m hm hs ⟨c.val + 1, hc⟩ + mkCumSum n m hm vs r =
             base + mkCumSum n m hm hs c + mkCumSum n m hm vs r +
             ext_slope n m hm hs ⟨c.val, by omega⟩ := by
           rw [mkCumSum_succ n m hm hs c.val hc]; ring
         have h2 : base + mkCumSum n m hm hs c + mkCumSum n m hm vs ⟨r.val + 1, hr⟩ =
             base + mkCumSum n m hm hs c + mkCumSum n m hm vs r +
             ext_slope n m hm vs ⟨r.val, by omega⟩ := by
           rw [mkCumSum_succ n m hm vs r.val hr]; ring
         have h3 : base + mkCumSum n m hm hs ⟨c.val + 1, hc⟩ +
             mkCumSum n m hm vs ⟨r.val + 1, hr⟩ =
             base + mkCumSum n m hm hs c + mkCumSum n m hm vs r +
             ext_slope n m hm hs ⟨c.val, by omega⟩ +
             ext_slope n m hm vs ⟨r.val, by omega⟩ := by
           rw [mkCumSum_succ n m hm hs c.val hc, mkCumSum_succ n m hm vs r.val hr]; ring
         -- Beta-reduce the lambda applications in the RichOk goal
         show ({base + mkCumSum n m hm hs c + mkCumSum n m hm vs r,
                base + mkCumSum n m hm hs ⟨c.val + 1, hc⟩ + mkCumSum n m hm vs r,
                base + mkCumSum n m hm hs c + mkCumSum n m hm vs ⟨r.val + 1, hr⟩,
                base + mkCumSum n m hm hs ⟨c.val + 1, hc⟩ +
                  mkCumSum n m hm vs ⟨r.val + 1, hr⟩} : Finset (ZMod 3)).card = 3
         rw [h1, h2, h3]
         exact richness_from_slopes _ _ _ hh hv,
       -- FixedBy180: f(n-1-r, n-1-c) = f(r,c) follows from palindrome R(c)=R(n-1-c)
       by
         unfold FixedBy180
         funext r c
         simp only [rotate90]
         rw [← mkCumSum_palindrome n m hm hs c, ← mkCumSum_palindrome n m hm vs r]⟩
    left_inv := fun ⟨f, hadj, hrich, hfixed⟩ => by
      -- We need to show that the reconstructed g r c = base + mkCumSum(hs)(c) + mkCumSum(vs)(r)
      -- equals f r c, where base = f(0,0), hs j = f(0,j+1)-f(0,j), vs k = f(k+1,0)-f(k,0).
      -- Strategy: show mkCumSum(hs)(c) = f(0,c)-f(0,0) and mkCumSum(vs)(r) = f(r,0)-f(0,0),
      -- then use separability.
      simp only [Subtype.mk.injEq]
      -- Build the ProperColoring for access to vOffset_col_independent
      let pc : ProperColoring n := ⟨f, hadj, hrich⟩
      -- sep: f r c - f(0,c) = f(r,0) - f(0,0)
      have sep : ∀ (r c : Fin n), f r c - f ⟨0, hn0⟩ c = f r ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ :=
        fun r c => vOffset_col_independent pc hn0 r c
      -- hfix_pw: the 180° fixed-point condition, extracted from hfixed pointwise
      -- FixedBy180 n f : rotate90 n (rotate90 n f) = f
      -- which unfolds to: ∀ r c, f ⟨n-1-r, _⟩ ⟨n-1-c, _⟩ = f r c
      have hfix_pw : ∀ (p q : Fin n),
          f ⟨n - 1 - p.val, by omega⟩ ⟨n - 1 - q.val, by omega⟩ = f p q := by
        intro p q
        have h := congr_fun (congr_fun hfixed p) q
        simp only [FixedBy180, rotate90] at h
        exact h
      -- hfn10: f(n-1, 0) = f(0, 0)
      have hfn10 : f ⟨n - 1, by omega⟩ ⟨0, hn0⟩ = f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        -- e1: f(n-1,0) = f(0,n-1) from hfix_pw with p=⟨0,_⟩, q=⟨n-1,_⟩
        have e1 : f ⟨n - 1, by omega⟩ ⟨0, hn0⟩ =
            f ⟨0, hn0⟩ ⟨n - 1, by omega⟩ := by
          have h := hfix_pw ⟨0, hn0⟩ ⟨n - 1, by omega⟩
          simp only [Fin.val_zero] at h
          have ha : (⟨n - 1 - 0, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
            Fin.ext (Nat.sub_zero _)
          have hb : (⟨n - 1 - (n - 1), by omega⟩ : Fin n) = ⟨0, hn0⟩ :=
            Fin.ext (Nat.sub_self _)
          rw [ha, hb] at h; exact h
        -- e3: f(n-1,n-1) = f(0,0) from hfix_pw with p=q=⟨0,_⟩
        have e3 : f ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ =
            f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
          have h := hfix_pw ⟨0, hn0⟩ ⟨0, hn0⟩
          simp only [Fin.val_zero] at h
          have ha : (⟨n - 1 - 0, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
            Fin.ext (Nat.sub_zero _)
          simp only [ha] at h; exact h
        -- e2: sep at r=n-1, c=n-1: f(n-1,n-1)-f(0,n-1) = f(n-1,0)-f(0,0)
        have e2 : f ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ -
            f ⟨0, hn0⟩ ⟨n - 1, by omega⟩ =
            f ⟨n - 1, by omega⟩ ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ :=
          sep ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
        -- 2*(f(n-1,0)-f(0,0)) = 0, and 2 ≠ 0 in ZMod 3
        have h2 : (2 : ZMod 3) * (f ⟨n - 1, by omega⟩ ⟨0, hn0⟩ -
            f ⟨0, hn0⟩ ⟨0, hn0⟩) = 0 := by linear_combination e1 - e2 + e3
        exact sub_eq_zero.mp (by
          have h2ne : (2 : ZMod 3) ≠ 0 := by decide
          have := mul_eq_zero.mp h2
          tauto)
      -- hfn1c: f(n-1, c) = f(0, c) for all c
      have hfn1c : ∀ (c : Fin n), f ⟨n - 1, by omega⟩ c = f ⟨0, hn0⟩ c := by
        intro c
        have hsep_n1 := sep ⟨n - 1, by omega⟩ c
        have hsep_0 := sep ⟨0, hn0⟩ c
        linear_combination hsep_n1 - hsep_0 + hfn10
      -- hpal_row: f(0, n-1-c) = f(0, c) for all c
      have hpal_row : ∀ (c : Fin n),
          f ⟨0, hn0⟩ ⟨n - 1 - c.val, by omega⟩ = f ⟨0, hn0⟩ c := by
        intro c
        -- From hfix_pw ⟨0,_⟩ c: f ⟨n-1-0,_⟩ ⟨n-1-c,_⟩ = f ⟨0,_⟩ c
        -- i.e. f ⟨n-1,_⟩ ⟨n-1-c,_⟩ = f ⟨0,_⟩ c
        have h := hfix_pw ⟨0, hn0⟩ c
        simp only [Fin.val_zero] at h
        have ha : (⟨n - 1 - 0, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
          Fin.ext (Nat.sub_zero _)
        rw [ha] at h
        -- h : f ⟨n-1,_⟩ ⟨n-1-c.val,_⟩ = f ⟨0,hn0⟩ c
        -- goal: f ⟨0,hn0⟩ ⟨n-1-c.val,_⟩ = f ⟨0,hn0⟩ c
        exact (hfn1c ⟨n - 1 - c.val, by omega⟩).symm.trans h
      -- hf0n1: f(0, n-1) = f(0, 0)
      have hf0n1 : f ⟨0, hn0⟩ ⟨n - 1, by omega⟩ = f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        have h := hpal_row ⟨0, hn0⟩
        simp only [Fin.val_zero, Nat.sub_zero] at h
        exact h
      -- hfrn1: f(r, n-1) = f(r, 0) for all r
      have hfrn1 : ∀ (r : Fin n), f r ⟨n - 1, by omega⟩ = f r ⟨0, hn0⟩ := by
        intro r
        have hsep_n1 := sep r ⟨n - 1, by omega⟩
        have hsep_0 := sep r ⟨0, hn0⟩
        linear_combination hsep_n1 - hsep_0 + hf0n1
      -- hpal_col: f(n-1-r, 0) = f(r, 0) for all r
      have hpal_col : ∀ (r : Fin n),
          f ⟨n - 1 - r.val, by omega⟩ ⟨0, hn0⟩ = f r ⟨0, hn0⟩ := by
        intro r
        -- From hfix_pw r ⟨n-1,_⟩: f ⟨n-1-r,_⟩ ⟨n-1-(n-1),_⟩ = f r ⟨n-1,_⟩
        -- i.e. f ⟨n-1-r,_⟩ ⟨0,_⟩ = f r ⟨n-1,_⟩
        have h := hfix_pw r ⟨n - 1, by omega⟩
        have hb : (⟨n - 1 - (n - 1), by omega⟩ : Fin n) = ⟨0, hn0⟩ :=
          Fin.ext (Nat.sub_self _)
        rw [hb] at h
        -- h : f ⟨n-1-r,_⟩ ⟨0,_⟩ = f r ⟨n-1,_⟩
        rw [hfrn1 r] at h
        exact h
      -- hcumR: mkCumSum(hs_f)(c) = f(0,c)-f(0,0)
      -- The key point: mkCumSum n m hm hs_f c computes the telescoping sum
      -- We prove this by showing mkCumSum equals the direct sum above
      -- using ext_slope for j < m and palindrome for j ≥ m
      have hcumR_lt_m : ∀ (k : ℕ) (hk : k < n) (hkm : k ≤ m),
          mkCumSum n m hm (fun j =>
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ -
             f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; linarith [hm]⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, by have := j.isLt; linarith [hm]⟩
               (by have := j.isLt; linarith [hm])))⟩) ⟨k, hk⟩ =
          f ⟨0, hn0⟩ ⟨k, hk⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        intro k hk hkm
        induction k with
        | zero =>
          simp only [mkCumSum_zero n m hm, sub_self]
        | succ k ihk =>
          have hk' : k < n := by omega
          have hkm' : k ≤ m := by omega
          rw [mkCumSum_succ n m hm _ k hk]
          simp only [ext_slope, dif_pos (show k < m by omega), Subtype.coe_mk]
          have heqk1 : (⟨k + 1, hk⟩ : Fin n) = ⟨k + 1, by omega⟩ := Fin.ext rfl
          rw [heqk1]
          linear_combination ihk hk' hkm'
      -- For k > m, use palindrome
      have hcumR_full : ∀ (k : ℕ) (hk : k < n),
          mkCumSum n m hm (fun j =>
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ -
             f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; linarith [hm]⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, by have := j.isLt; linarith [hm]⟩
               (by have := j.isLt; linarith [hm])))⟩) ⟨k, hk⟩ =
          f ⟨0, hn0⟩ ⟨k, hk⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        intro k hk
        -- Use palindrome: mkCumSum c = mkCumSum (n-1-c)
        -- and hcumR_lt_m for the reflected index when k > m
        by_cases hkm : k ≤ m
        · exact hcumR_lt_m k hk hkm
        · -- k > m: use palindrome
          push_neg at hkm
          have hk_refl : n - 1 - k ≤ m := by omega
          have hk_refl_lt : n - 1 - k < n := by omega
          have hpal := hcumR_lt_m (n - 1 - k) hk_refl_lt (by omega)
          -- mkCumSum(k) = mkCumSum(n-1-k) by palindrome
          have hpal_sym := mkCumSum_palindrome n m hm (fun j =>
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ -
             f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; linarith [hm]⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, by have := j.isLt; linarith [hm]⟩
               (by have := j.isLt; linarith [hm])))⟩) ⟨k, hk⟩
          -- mkCumSum ⟨k,_⟩ = mkCumSum ⟨n-1-k,_⟩
          rw [hpal_sym, hpal]
          -- now: f(0,n-1-k)-f(0,0) = f(0,k)-f(0,0)
          -- from hpal_row applied at c = ⟨k, hk⟩
          congr 1
          exact hpal_row ⟨k, hk⟩
      -- hcumD_full: mkCumSum(vs_f)(r) = f(r,0) - f(0,0)
      have hcumD_lt_m : ∀ (k : ℕ) (hk : k < n) (hkm : k ≤ m),
          mkCumSum n m hm (fun j =>
            ⟨f ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩ -
             f ⟨j.val, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.2
               ⟨j.val, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩
               (by have := j.isLt; linarith [hm])))⟩) ⟨k, hk⟩ =
          f ⟨k, hk⟩ ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        intro k hk hkm
        induction k with
        | zero =>
          simp only [mkCumSum_zero n m hm, sub_self]
        | succ k ihk =>
          have hk' : k < n := by omega
          have hkm' : k ≤ m := by omega
          rw [mkCumSum_succ n m hm _ k hk]
          simp only [ext_slope, dif_pos (show k < m by omega), Subtype.coe_mk]
          have heqk1 : (⟨k + 1, hk⟩ : Fin n) = ⟨k + 1, by omega⟩ := Fin.ext rfl
          rw [heqk1]
          linear_combination ihk hk' hkm'
      have hcumD_full : ∀ (k : ℕ) (hk : k < n),
          mkCumSum n m hm (fun j =>
            ⟨f ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩ -
             f ⟨j.val, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.2
               ⟨j.val, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩
               (by have := j.isLt; linarith [hm])))⟩) ⟨k, hk⟩ =
          f ⟨k, hk⟩ ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        intro k hk
        by_cases hkm : k ≤ m
        · exact hcumD_lt_m k hk hkm
        · push_neg at hkm
          have hk_refl_lt : n - 1 - k < n := by omega
          have hpal := hcumD_lt_m (n - 1 - k) hk_refl_lt (by omega)
          have hpal_sym := mkCumSum_palindrome n m hm (fun j =>
            ⟨f ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩ -
             f ⟨j.val, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.2
               ⟨j.val, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩
               (by have := j.isLt; linarith [hm])))⟩) ⟨k, hk⟩
          rw [hpal_sym, hpal]
          congr 1
          exact hpal_col ⟨k, hk⟩
      -- Now conclude: the goal after funext involves mkCumSum applied to
      -- the lambda extracted from toFun. These are definitionally equal
      -- to the lambdas in hcumR_full/hcumD_full (by proof irrelevance on the bound proofs).
      funext r c
      -- The goal is: f(0,0) + mkCumSum(hs_toFun) c + mkCumSum(vs_toFun) r = f r c
      -- We convert the mkCumSum terms using hcumR_full and hcumD_full
      have hR : mkCumSum n m hm (fun j =>
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ -
             f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; linarith [hm]⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, by have := j.isLt; linarith [hm]⟩
               (by have := j.isLt; linarith [hm])))⟩) c =
          f ⟨0, hn0⟩ c - f ⟨0, hn0⟩ ⟨0, hn0⟩ := hcumR_full c.val c.isLt
      have hD : mkCumSum n m hm (fun j =>
            ⟨f ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩ -
             f ⟨j.val, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.2
               ⟨j.val, by have := j.isLt; linarith [hm]⟩ ⟨0, hn0⟩
               (by have := j.isLt; linarith [hm])))⟩) r =
          f r ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := hcumD_full r.val r.isLt
      -- The actual mkCumSum in the goal uses toFun's lambda, which is definitionally
      -- equal to the one in hR/hD (same value, different proof term, proof-irrelevant)
      rw [hR, hD]
      linear_combination -(sep r c)
    right_inv := fun (base, hs, vs) => by
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · -- base component: base + mkCumSum(0) + mkCumSum(0) = base
        simp [mkCumSum_zero n m hm]
      · -- h-slopes: hs'(j) = difference = ext_slope hs j = hs(j)
        funext j
        apply Subtype.ext
        simp only [mkCumSum_zero n m hm, add_zero]
        rw [mkCumSum_succ n m hm hs j.val (by have := j.isLt; have := hm; omega)]
        simp only [ext_slope, dif_pos (show j.val < m from j.isLt), Fin.eta]
        ring
      · -- v-slopes: vs'(k) = ext_slope vs k = vs(k)
        funext k
        apply Subtype.ext
        simp only [mkCumSum_zero n m hm, add_zero]
        rw [mkCumSum_succ n m hm vs k.val (by have := k.isLt; have := hm; omega)]
        simp only [ext_slope, dif_pos (show k.val < m from k.isLt), Fin.eta]
        ring }

/-- 90°-fixed proper colorings biject with (base, m h-slopes)
    where m = (n−1)/2 (v-slopes equal h-slopes by the 90° condition). -/
noncomputable def equiv_fixed90 (n : ℕ) (hn : Odd n) (hn3 : 5 ≤ n)
    (h4 : 4 ∣ (n - 1)) :
    { f : Coloring n // AdjOk f ∧ RichOk f ∧ FixedBy90 n f } ≃
    ZMod 3 × (Fin ((n - 1) / 2) → NZMod3) :=
  -- FixedBy90 forces D(r) = R(r) (same slopes for rows and columns) and R palindromic.
  -- Forward: f ↦ (f(0,0), j ↦ f(0,j+1)−f(0,j) for j < m)
  -- Backward: (base, hs) ↦ g(r,c) = base + R(c) + R(r) where R uses palindrome extension.
  let hn0 : 0 < n := by omega
  let m := (n - 1) / 2
  have hm : 2 * m + 1 = n := by obtain ⟨k, hk⟩ := hn; omega
  { toFun := fun ⟨f, hadj, _, _⟩ =>
      (f ⟨0, hn0⟩ ⟨0, hn0⟩,
       fun j =>
        have hj_lt_n : j.val + 1 < n := by have := j.isLt; have := hm; omega
        ⟨f ⟨0, hn0⟩ ⟨j.val + 1, hj_lt_n⟩ -
         f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; have := hm; omega⟩,
         sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; have := hm; omega⟩
           hj_lt_n))⟩)
    invFun := fun (base, hs) =>
      ⟨fun r c => base + mkCumSum n m hm hs c + mkCumSum n m hm hs r,
       -- AdjOk: horizontal difference is ext_slope hs c ≠ 0
       ⟨fun r c hc => by
          intro heq
          exact ext_slope_ne_zero n m hm hs ⟨c.val, by omega⟩ (by
            have hstep := mkCumSum_succ n m hm hs c.val hc
            have h1 := add_right_cancel heq
            have h2 := add_left_cancel h1
            linear_combination -(h2.trans hstep)),
        -- AdjOk: vertical difference is ext_slope hs r ≠ 0
        fun r c hr => by
          intro heq
          exact ext_slope_ne_zero n m hm hs ⟨r.val, by omega⟩ (by
            have hstep := mkCumSum_succ n m hm hs r.val hr
            have h1 := add_left_cancel heq
            linear_combination -(h1.trans hstep))⟩,
       -- RichOk: 2×2 block has all 3 colours
       fun r c hr hc => by
         have hh : ext_slope n m hm hs ⟨c.val, by omega⟩ ≠ 0 :=
           ext_slope_ne_zero n m hm hs ⟨c.val, by omega⟩
         have hv : ext_slope n m hm hs ⟨r.val, by omega⟩ ≠ 0 :=
           ext_slope_ne_zero n m hm hs ⟨r.val, by omega⟩
         have h1 : base + mkCumSum n m hm hs ⟨c.val + 1, hc⟩ + mkCumSum n m hm hs r =
             base + mkCumSum n m hm hs c + mkCumSum n m hm hs r +
             ext_slope n m hm hs ⟨c.val, by omega⟩ := by
           rw [mkCumSum_succ n m hm hs c.val hc]; ring
         have h2 : base + mkCumSum n m hm hs c + mkCumSum n m hm hs ⟨r.val + 1, hr⟩ =
             base + mkCumSum n m hm hs c + mkCumSum n m hm hs r +
             ext_slope n m hm hs ⟨r.val, by omega⟩ := by
           rw [mkCumSum_succ n m hm hs r.val hr]; ring
         have h3 : base + mkCumSum n m hm hs ⟨c.val + 1, hc⟩ +
             mkCumSum n m hm hs ⟨r.val + 1, hr⟩ =
             base + mkCumSum n m hm hs c + mkCumSum n m hm hs r +
             ext_slope n m hm hs ⟨c.val, by omega⟩ +
             ext_slope n m hm hs ⟨r.val, by omega⟩ := by
           rw [mkCumSum_succ n m hm hs c.val hc, mkCumSum_succ n m hm hs r.val hr]; ring
         show ({base + mkCumSum n m hm hs c + mkCumSum n m hm hs r,
                base + mkCumSum n m hm hs ⟨c.val + 1, hc⟩ + mkCumSum n m hm hs r,
                base + mkCumSum n m hm hs c + mkCumSum n m hm hs ⟨r.val + 1, hr⟩,
                base + mkCumSum n m hm hs ⟨c.val + 1, hc⟩ +
                  mkCumSum n m hm hs ⟨r.val + 1, hr⟩} : Finset (ZMod 3)).card = 3
         rw [h1, h2, h3]
         exact richness_from_slopes _ _ _ hh hv,
       -- FixedBy90: g(n-1-c, r) = g(r, c) follows from R palindromic (D = R)
       by
         unfold FixedBy90
         funext r c
         simp only [rotate90]
         rw [← mkCumSum_palindrome n m hm hs c]
         ring⟩
    left_inv := fun ⟨f, hadj, hrich, hfixed90⟩ => by
      -- FixedBy90 implies FixedBy180
      have hfixed180 : FixedBy180 n f := by
        unfold FixedBy180
        have h := congr_arg (rotate90 n) hfixed90
        exact h.trans hfixed90
      simp only [Subtype.mk.injEq]
      let pc : ProperColoring n := ⟨f, hadj, hrich⟩
      have sep : ∀ (r c : Fin n), f r c - f ⟨0, hn0⟩ c = f r ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ :=
        fun r c => vOffset_col_independent pc hn0 r c
      -- hfix_pw: pointwise 180° condition from hfixed180
      have hfix_pw : ∀ (p q : Fin n),
          f ⟨n - 1 - p.val, by omega⟩ ⟨n - 1 - q.val, by omega⟩ = f p q := by
        intro p q
        have h := congr_fun (congr_fun hfixed180 p) q
        simp only [FixedBy180, rotate90] at h
        exact h
      -- hfix90_pw: pointwise 90° condition: f(n-1-c, r) = f r c
      have hfix90_pw : ∀ (r c : Fin n),
          f ⟨n - 1 - c.val, by omega⟩ r = f r c := by
        intro r c
        have h := congr_fun (congr_fun hfixed90 r) c
        simp only [FixedBy90, rotate90] at h
        exact h
      -- hfn10: f(n-1, 0) = f(0, 0)
      have hfn10 : f ⟨n - 1, by omega⟩ ⟨0, hn0⟩ = f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        have e1 : f ⟨n - 1, by omega⟩ ⟨0, hn0⟩ =
            f ⟨0, hn0⟩ ⟨n - 1, by omega⟩ := by
          have h := hfix_pw ⟨0, hn0⟩ ⟨n - 1, by omega⟩
          simp only [Fin.val_zero] at h
          have ha : (⟨n - 1 - 0, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
            Fin.ext (Nat.sub_zero _)
          have hb : (⟨n - 1 - (n - 1), by omega⟩ : Fin n) = ⟨0, hn0⟩ :=
            Fin.ext (Nat.sub_self _)
          rw [ha, hb] at h; exact h
        have e3 : f ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ =
            f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
          have h := hfix_pw ⟨0, hn0⟩ ⟨0, hn0⟩
          simp only [Fin.val_zero] at h
          have ha : (⟨n - 1 - 0, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
            Fin.ext (Nat.sub_zero _)
          simp only [ha] at h; exact h
        have e2 : f ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ -
            f ⟨0, hn0⟩ ⟨n - 1, by omega⟩ =
            f ⟨n - 1, by omega⟩ ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ :=
          sep ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
        have h2 : (2 : ZMod 3) * (f ⟨n - 1, by omega⟩ ⟨0, hn0⟩ -
            f ⟨0, hn0⟩ ⟨0, hn0⟩) = 0 := by linear_combination e1 - e2 + e3
        exact sub_eq_zero.mp (by
          have h2ne : (2 : ZMod 3) ≠ 0 := by decide
          have := mul_eq_zero.mp h2
          tauto)
      -- hfn1c: f(n-1, c) = f(0, c) for all c
      have hfn1c : ∀ (c : Fin n), f ⟨n - 1, by omega⟩ c = f ⟨0, hn0⟩ c := by
        intro c
        have hsep_n1 := sep ⟨n - 1, by omega⟩ c
        have hsep_0 := sep ⟨0, hn0⟩ c
        linear_combination hsep_n1 - hsep_0 + hfn10
      -- hpal_row: f(0, n-1-c) = f(0, c)
      have hpal_row : ∀ (c : Fin n),
          f ⟨0, hn0⟩ ⟨n - 1 - c.val, by omega⟩ = f ⟨0, hn0⟩ c := by
        intro c
        have h := hfix_pw ⟨0, hn0⟩ c
        simp only [Fin.val_zero] at h
        have ha : (⟨n - 1 - 0, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
          Fin.ext (Nat.sub_zero _)
        rw [ha] at h
        exact (hfn1c ⟨n - 1 - c.val, by omega⟩).symm.trans h
      -- hfr0_eq_f0r: f(r, 0) = f(0, r) from FixedBy90
      -- hfix90_pw at c=⟨0,_⟩: f(n-1, r) = f(r, 0); combined with hfn1c: f(0,r) = f(r,0)
      have hfr0_eq_f0r : ∀ (r : Fin n), f r ⟨0, hn0⟩ = f ⟨0, hn0⟩ r := by
        intro r
        -- hfix90_pw r ⟨0,_⟩: f ⟨n-1-0,_⟩ r = f r ⟨0,_⟩
        have h90 := hfix90_pw r ⟨0, hn0⟩
        simp only [Fin.val_zero, Nat.sub_zero] at h90
        -- h90 : f ⟨n-1,_⟩ r = f r ⟨0,_⟩
        -- but ⟨n-1-0,_⟩ = ⟨n-1,_⟩ so h90 : f ⟨n-1,_⟩ r = f r ⟨0, hn0⟩
        rw [← hfn1c r, h90]
      -- hcumR_full: mkCumSum(hs_f)(c) = f(0,c) - f(0,0) for all c
      -- (proven without omega in the lambda type, using linarith)
      have hcumR_lt : ∀ (k : ℕ) (hk : k < n) (hkm : k ≤ m),
          mkCumSum n m hm (fun j =>
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ -
             f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; linarith [hm]⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, by have := j.isLt; linarith [hm]⟩
               (by have := j.isLt; linarith [hm])))⟩) ⟨k, hk⟩ =
          f ⟨0, hn0⟩ ⟨k, hk⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        intro k hk hkm
        induction k with
        | zero =>
          simp only [mkCumSum_zero n m hm, sub_self]
        | succ k ihk =>
          have hk' : k < n := by omega
          have hkm' : k ≤ m := by omega
          rw [mkCumSum_succ n m hm _ k hk]
          simp only [ext_slope, dif_pos (show k < m by omega), Subtype.coe_mk]
          have heqk1 : (⟨k + 1, hk⟩ : Fin n) = ⟨k + 1, by omega⟩ := Fin.ext rfl
          rw [heqk1]
          linear_combination ihk hk' hkm'
      have hcumR_full : ∀ (k : ℕ) (hk : k < n),
          mkCumSum n m hm (fun j =>
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ -
             f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; linarith [hm]⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, by have := j.isLt; linarith [hm]⟩
               (by have := j.isLt; linarith [hm])))⟩) ⟨k, hk⟩ =
          f ⟨0, hn0⟩ ⟨k, hk⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        intro k hk
        by_cases hkm : k ≤ m
        · exact hcumR_lt k hk hkm
        · push_neg at hkm
          have hk_refl_lt : n - 1 - k < n := by omega
          have hpal := hcumR_lt (n - 1 - k) hk_refl_lt (by omega)
          have hpal_sym := mkCumSum_palindrome n m hm (fun j =>
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ -
             f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; linarith [hm]⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, by have := j.isLt; linarith [hm]⟩
               (by have := j.isLt; linarith [hm])))⟩) ⟨k, hk⟩
          rw [hpal_sym, hpal]
          congr 1
          exact hpal_row ⟨k, hk⟩
      -- Now conclude
      funext r c
      have hR : mkCumSum n m hm (fun j =>
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ -
             f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; linarith [hm]⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, by have := j.isLt; linarith [hm]⟩
               (by have := j.isLt; linarith [hm])))⟩) c =
          f ⟨0, hn0⟩ c - f ⟨0, hn0⟩ ⟨0, hn0⟩ := hcumR_full c.val c.isLt
      have hRowR : mkCumSum n m hm (fun j =>
            ⟨f ⟨0, hn0⟩ ⟨j.val + 1, by have := j.isLt; linarith [hm]⟩ -
             f ⟨0, hn0⟩ ⟨j.val, by have := j.isLt; linarith [hm]⟩,
             sub_ne_zero.mpr (Ne.symm (hadj.1 ⟨0, hn0⟩
               ⟨j.val, by have := j.isLt; linarith [hm]⟩
               (by have := j.isLt; linarith [hm])))⟩) r =
          f r ⟨0, hn0⟩ - f ⟨0, hn0⟩ ⟨0, hn0⟩ := by
        rw [hcumR_full r.val r.isLt, hfr0_eq_f0r r]
      rw [hR, hRowR]
      linear_combination -(sep r c)
    right_inv := fun (base, hs) => by
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · simp [mkCumSum_zero n m hm]
      · funext j
        apply Subtype.ext
        simp only [mkCumSum_zero n m hm, add_zero]
        rw [mkCumSum_succ n m hm hs j.val (by have := j.isLt; have := hm; omega)]
        simp only [ext_slope, dif_pos (show j.val < m from j.isLt), Fin.eta]
        ring }

end ChromaticRotations
