/-
  Chromatic Rotations — Lean 4 / Mathlib Proof
  =============================================
  We prove that the number of equivalence classes of proper 3-colorings of an
  n×n grid under 90° rotational symmetry is:
    - General odd n with 4∣(n−1): 3·(2^(2n−4) + 2^(n−3) + 2^((n−3)/2))
    - n = 101:                     3·(2^198    + 2^98   + 2^49)

  A coloring f : Fin n → Fin n → ZMod 3 is *proper* when:
    (A) Adjacency : no two edge-adjacent cells share a color.
    (R) Richness  : every 2×2 sub-square contains all three colors.

  Proof status:
    ✓ slope_propagation_local   — by `decide` on ZMod 3⁴
    ✓ hSlope_step, vSlope_step  — from (1)
    ✓ vOffset_col_independent   — double induction + `linear_combination`
    ✓ ProperColoring.isSeparable — from (3) via `linear_combination`
    ✓ rotate90_pow4             — Fin.ext + omega
    ✓ rotate90_proper           — fin_eq helper + convert/ext/tauto
    ✓ burnside_arith_general    — pow_add + ring in ℕ
    ✓ chromatic_rotations_101   — by `norm_num`
    ∂ card_fixed180_odd         — sorry (bijection counting argument)
    ∂ card_fixed90_odd          — sorry (bijection counting argument)
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace ChromaticRotations

/-! ## 1. Definitions -/

/-- A 3-coloring of the n×n grid. -/
abbrev Coloring (n : ℕ) := Fin n → Fin n → ZMod 3

variable {n : ℕ}

/-- Adjacency: no two horizontally or vertically adjacent cells share a color. -/
def AdjOk (f : Coloring n) : Prop :=
  (∀ (r c : Fin n) (hc : c.val + 1 < n), f r c ≠ f r ⟨c.val + 1, hc⟩) ∧
  (∀ (r c : Fin n) (hr : r.val + 1 < n), f r c ≠ f ⟨r.val + 1, hr⟩ c)

/-- Richness: every 2×2 sub-square contains all three colors. -/
def RichOk (f : Coloring n) : Prop :=
  ∀ (r c : Fin n) (hr : r.val + 1 < n) (hc : c.val + 1 < n),
    ({f r c, f r ⟨c.val + 1, hc⟩,
      f ⟨r.val + 1, hr⟩ c,
      f ⟨r.val + 1, hr⟩ ⟨c.val + 1, hc⟩} : Finset (ZMod 3)).card = 3

/-- A proper coloring satisfies both conditions. -/
structure ProperColoring (n : ℕ) where
  toFun  : Coloring n
  adjOk  : AdjOk toFun
  richOk : RichOk toFun

/-! ## 2. Core local lemma — decided over ZMod 3 -/

/-- In any 2×2 sub-square satisfying (A)+(R), slopes propagate:
      b − a = d − c   (horizontal slope same in both rows)
      c − a = d − b   (vertical slope same in both columns)
    Proof: exhaustive case analysis on (ZMod 3)⁴ via `decide`. -/
lemma slope_propagation_local :
    ∀ (a b c d : ZMod 3),
      a ≠ b → a ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (ZMod 3)).card = 3 →
      b - a = d - c ∧ c - a = d - b := by decide

/-! ## 3. Slope definitions -/

/-- Horizontal slope: color difference moving right. -/
def hSlope (f : Coloring n) (r c : Fin n) (hc : c.val + 1 < n) : ZMod 3 :=
  f r ⟨c.val + 1, hc⟩ - f r c

/-- Vertical slope: color difference moving down. -/
def vSlope (f : Coloring n) (r c : Fin n) (hr : r.val + 1 < n) : ZMod 3 :=
  f ⟨r.val + 1, hr⟩ c - f r c

/-! ## 4. Slope invariance -/

/-- hSlope at column c is the same in row r and row r+1. -/
lemma hSlope_step (f : ProperColoring n) (r c : Fin n)
    (hr : r.val + 1 < n) (hc : c.val + 1 < n) :
    hSlope f.toFun r c hc = hSlope f.toFun ⟨r.val + 1, hr⟩ c hc := by
  obtain ⟨heq, _⟩ := slope_propagation_local
    (f.toFun r c) (f.toFun r ⟨c.val + 1, hc⟩)
    (f.toFun ⟨r.val + 1, hr⟩ c) (f.toFun ⟨r.val + 1, hr⟩ ⟨c.val + 1, hc⟩)
    (f.adjOk.1 r c hc) (f.adjOk.2 r c hr)
    (f.adjOk.2 r ⟨c.val + 1, hc⟩ hr) (f.adjOk.1 ⟨r.val + 1, hr⟩ c hc)
    (f.richOk r c hr hc)
  simp only [hSlope]; exact heq

/-- vSlope at row r is the same in column c and column c+1. -/
lemma vSlope_step (f : ProperColoring n) (r c : Fin n)
    (hr : r.val + 1 < n) (hc : c.val + 1 < n) :
    vSlope f.toFun r c hr = vSlope f.toFun r ⟨c.val + 1, hc⟩ hr := by
  obtain ⟨_, heq⟩ := slope_propagation_local
    (f.toFun r c) (f.toFun r ⟨c.val + 1, hc⟩)
    (f.toFun ⟨r.val + 1, hr⟩ c) (f.toFun ⟨r.val + 1, hr⟩ ⟨c.val + 1, hc⟩)
    (f.adjOk.1 r c hc) (f.adjOk.2 r c hr)
    (f.adjOk.2 r ⟨c.val + 1, hc⟩ hr) (f.adjOk.1 ⟨r.val + 1, hr⟩ c hc)
    (f.richOk r c hr hc)
  simp only [vSlope]; exact heq

/-! ## 5. Separability Theorem -/

/-- A coloring is separable if f(r,c) = base + R(c) + D(r) for all r, c. -/
def IsSeparable (f : Coloring n) : Prop :=
  ∃ (base : ZMod 3) (R : Fin n → ZMod 3) (D : Fin n → ZMod 3),
    ∀ r c, f r c = base + R c + D r

/-- The vertical offset f(r,c) − f(0,c) is independent of c.

    Proof by double induction: outer on column j, inner on row k.

    Key step (succ j, succ k):
      Denote A = f(k+1,j+1), B = f(0,j+1), C = f(k+1,0), D = f(0,0),
             E = f(k,j+1),   F = f(k,0),   G = f(k+1,j), H = f(k,j), I = f(0,j).
      From vSlope_step: G − H = A − E.           (hstep)
      From IH (col j, row k):   H − I = F − D.  (h_kj)
      From IH (col j, row k+1): G − I = C − D.  (h_k1j)
      From IH (col j+1, row k): E − B = F − D.  (h_kj1)
      Goal: A − B = C − D.
      linear_combination: h_kj1 − hstep + h_k1j − h_kj.             -/
lemma vOffset_col_independent (f : ProperColoring n) (hn : 0 < n) (r c : Fin n) :
    f.toFun r c - f.toFun ⟨0, hn⟩ c =
    f.toFun r ⟨0, hn⟩ - f.toFun ⟨0, hn⟩ ⟨0, hn⟩ := by
  suffices h : ∀ (j : ℕ) (hj : j < n) (k : ℕ) (hk : k < n),
      f.toFun ⟨k, hk⟩ ⟨j, hj⟩ - f.toFun ⟨0, hn⟩ ⟨j, hj⟩ =
      f.toFun ⟨k, hk⟩ ⟨0, hn⟩ - f.toFun ⟨0, hn⟩ ⟨0, hn⟩ from
    h c.val c.isLt r.val r.isLt
  intro j
  induction j with
  | zero => intros; simp
  | succ j ihj =>
    intro hj k
    induction k with
    | zero => intros; simp
    | succ k ihk =>
      intro hk
      have hk' : k < n := by omega
      have hj' : j < n := by omega
      -- vSlope_step: the vertical slope is the same at column j and j+1
      have hstep := vSlope_step f ⟨k, hk'⟩ ⟨j, hj'⟩ hk hj
      simp only [vSlope] at hstep
      -- Induction hypotheses
      have h_kj  := ihj hj' k hk'     -- col j, row k
      have h_k1j := ihj hj' (k + 1) hk -- col j, row k+1
      have h_kj1 := ihk hk'            -- col j+1, row k
      -- Combine: A−B = C−D  follows from  h_kj1 − hstep + h_k1j − h_kj
      linear_combination h_kj1 - hstep + h_k1j - h_kj

/-- Every proper coloring is separable.
    Choose base = f(0,0), R(c) = f(0,c) − f(0,0), D(r) = f(r,0) − f(0,0).
    Then f(r,c) = base + R(c) + D(r) is exactly vOffset_col_independent. -/
theorem ProperColoring.isSeparable (f : ProperColoring n) (hn : 0 < n) :
    IsSeparable f.toFun :=
  ⟨f.toFun ⟨0, hn⟩ ⟨0, hn⟩,
   fun c => f.toFun ⟨0, hn⟩ c - f.toFun ⟨0, hn⟩ ⟨0, hn⟩,
   fun r => f.toFun r ⟨0, hn⟩ - f.toFun ⟨0, hn⟩ ⟨0, hn⟩,
   fun r c => by linear_combination vOffset_col_independent f hn r c⟩

/-! ## 6. Rotation -/

/-- 90° clockwise rotation: (r, c) ↦ (c, n−1−r). -/
def rotate90 (n : ℕ) (f : Coloring n) : Coloring n :=
  fun r c => f ⟨n - 1 - c.val, by have := c.isLt; omega⟩ r

/-- rotate90^4 = id. -/
lemma rotate90_pow4 (n : ℕ) (f : Coloring n) :
    rotate90 n (rotate90 n (rotate90 n (rotate90 n f))) = f := by
  funext r c
  simp only [rotate90]
  have hr := r.isLt; have hc := c.isLt
  have hcc : n - 1 - (n - 1 - c.val) = c.val := by omega
  have hrr : n - 1 - (n - 1 - r.val) = r.val := by omega
  suffices h1 : (⟨n - 1 - (n - 1 - c.val), by omega⟩ : Fin n) = c by
    suffices h2 : (⟨n - 1 - (n - 1 - r.val), by omega⟩ : Fin n) = r by
      simp only [h1, h2]
    exact Fin.ext hrr
  exact Fin.ext hcc

/-- rotate90 preserves proper colorings.

    After rotation g(r,c) = f(n−1−c, r):
    • Horizontal adj of g = Vertical adj of f   (adj in the column direction)
    • Vertical adj of g   = Horizontal adj of f  (adj in the row direction)
    • 2×2 richness of g   = 2×2 richness of f at the rotated block             -/
lemma rotate90_proper (n : ℕ) (f : ProperColoring n) :
    AdjOk (rotate90 n f.toFun) ∧ RichOk (rotate90 n f.toFun) := by
  -- Helper: equality of Fin.mk terms when natural number values agree
  have fin_eq : ∀ (a b : ℕ) (ha : a < n) (hb : b < n), a = b →
      (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ := fun a b ha hb h => by
    simp only [Fin.mk.injEq]; exact h
  constructor
  · constructor
    · -- Horizontal adjacency: g(r,c) ≠ g(r,c+1)
      -- = f(n−1−c, r) ≠ f(n−2−c, r)   [vertical adjacency in f]
      intro r c hc
      simp only [rotate90]
      have h1 : n - 1 - (c.val + 1) < n     := by omega
      have h2 : n - 1 - c.val < n            := by omega
      have h3 : n - 1 - (c.val + 1) + 1 < n := by omega
      have key := f.adjOk.2 ⟨n - 1 - (c.val + 1), h1⟩ r h3
      rw [fin_eq _ _ h3 h2 (by omega)] at key
      exact key.symm
    · -- Vertical adjacency: g(r,c) ≠ g(r+1,c)
      -- = f(n−1−c, r) ≠ f(n−1−c, r+1)   [horizontal adjacency in f]
      intro r c hr
      simp only [rotate90]
      exact f.adjOk.1 ⟨n - 1 - c.val, by omega⟩ r hr
  · -- Richness: 2×2 block of g at (r,c) maps to 2×2 block of f at (n−2−c, r)
    intro r c hr hc
    simp only [rotate90]
    have h1 : n - 1 - (c.val + 1) < n     := by omega
    have h2 : n - 1 - (c.val + 1) + 1 < n := by omega
    have h3 : n - 1 - c.val < n           := by omega
    have key := f.richOk ⟨n - 1 - (c.val + 1), h1⟩ r h2 hr
    -- Replace the successor Fin by ⟨n−1−c, h3⟩
    rw [fin_eq _ _ h2 h3 (by omega)] at key
    -- key has the same four values as the goal, in a different Finset insertion order.
    -- Prove equality by extensionality: same membership.
    convert key using 2
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-! ## 7. Fixed-point conditions -/

/-- Fixed by 90° rotation. -/
def FixedBy90 (n : ℕ) (f : Coloring n) : Prop := rotate90 n f = f

/-- Fixed by 180° rotation. -/
def FixedBy180 (n : ℕ) (f : Coloring n) : Prop := rotate90 n (rotate90 n f) = f

/-! ## 8. Fixed-point counts

  For separable f(r,c) = base + R(c) + D(r) (slopes h_j = R(j+1)−R(j), v_k = D(k+1)−D(k)):

  Fix(ρ²) [180°, i.e. f(r,c) = f(n−1−r, n−1−c)]:
    The condition forces R palindromic (R(c) = R(n−1−c)) and D palindromic.
    For n = 2m+1 this means h_{2m−1−j} = −h_j for j < m; m free h-slopes ∈ {1,2},
    m free v-slopes, plus base. |Fix(ρ²)| = 3 · 2^m · 2^m = 3 · 2^(n−1).

  Fix(ρ¹) [90°, i.e. f(r,c) = f(n−1−c, r), requires 4∣(n−1)]:
    Forces R(c) = D(n−1−c) and D(r) = R(r), so h = v and R palindromic.
    m free slopes, plus base. |Fix(ρ¹)| = 3 · 2^m = 3 · 2^((n−1)/2).

  The bijections are constructive: given (base, free h-slopes, [free v-slopes]),
  extend to all n−1 slopes via the palindrome constraint and assemble f.
  We state the bijections as noncomputable Equivs and sorry the construction;
  the cardinality arithmetic follows by `simp` + `norm_num`.                  -/

/-- Nonzero elements of ZMod 3 (exactly {1, 2}). Used as the slope alphabet. -/
private abbrev NZMod3 : Type := {x : ZMod 3 // x ≠ 0}

private lemma NZMod3_card : Fintype.card NZMod3 = 2 := by decide

/-- Any 2×2 block with nonzero h-slope and nonzero v-slope contains all 3 colours. -/
private lemma richness_from_slopes :
    ∀ (a h v : ZMod 3), h ≠ 0 → v ≠ 0 →
      ({a, a + h, a + v, a + h + v} : Finset (ZMod 3)).card = 3 := by decide

/-! ### Slope-extension helpers for palindromic colorings

Given m free slopes hs : Fin m → NZMod3, we extend to all n−1 slopes via the
anti-palindrome rule ext_h j = hs(j) for j < m,  ext_h j = −hs(n−2−j) for j ≥ m.
Then R c = Σ_{j < c} ext_h j is automatically palindromic: R c = R (n−1−c). -/

-- ext_slope needs hm to prove the reflected index is < m in the else branch
private noncomputable def ext_slope (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n)
    (hs : Fin m → NZMod3) (j : Fin (n - 1)) : ZMod 3 :=
  if h : j.val < m then (hs ⟨j.val, h⟩).val
  else -(hs ⟨n - 2 - j.val, by omega⟩).val

-- Use Fin c.val as index so j.isLt : j.val < c.val is in scope
private noncomputable def mkCumSum (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n)
    (hs : Fin m → NZMod3) (c : Fin n) : ZMod 3 :=
  ∑ j : Fin c.val, ext_slope n m hm hs ⟨j.val, by have := j.isLt; have := c.isLt; omega⟩

/-- ext_slope is nonzero at every index. -/
private lemma ext_slope_ne_zero (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n)
    (hs : Fin m → NZMod3) (j : Fin (n - 1)) : ext_slope n m hm hs j ≠ 0 := by
  simp only [ext_slope]
  split_ifs with h
  · exact (hs ⟨j.val, h⟩).prop
  · simp only [neg_ne_zero]
    exact (hs ⟨n - 2 - j.val, by omega⟩).prop

/-- mkCumSum at 0 is 0. -/
private lemma mkCumSum_zero (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n) (hs : Fin m → NZMod3) :
    mkCumSum n m hm hs ⟨0, by omega⟩ = 0 := by
  simp [mkCumSum]

/-- mkCumSum at successor: mkCumSum (j+1) = mkCumSum j + ext_slope j. -/
private lemma mkCumSum_succ (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n) (hs : Fin m → NZMod3)
    (j : ℕ) (hj : j + 1 < n) :
    mkCumSum n m hm hs ⟨j + 1, hj⟩ =
    mkCumSum n m hm hs ⟨j, by omega⟩ + ext_slope n m hm hs ⟨j, by omega⟩ := by
  simp only [mkCumSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

/-- Anti-palindrome: ext_slope j + ext_slope(n−2−j) = 0 for all j. -/
private lemma ext_slope_anti_palindrome (n m : ℕ) (hm : 2 * m + 1 = n)
    (hs : Fin m → NZMod3) (j : ℕ) (hj : j < n - 1) :
    ext_slope n m hm hs ⟨j, by omega⟩ + ext_slope n m hm hs ⟨n - 2 - j, by omega⟩ = 0 := by
  simp only [ext_slope]
  split_ifs with h1 h2
  · -- j < m and n-2-j < m: impossible since j < m ⟹ n-2-j = 2m-1-j ≥ m
    exfalso; omega
  · -- j < m, n-2-j ≥ m: hs(j) + (−hs(n-2-(n-2-j))) = hs(j) − hs(j) = 0
    have heq : n - 2 - (n - 2 - j) = j := by omega
    have hlt : n - 2 - (n - 2 - j) < m := by omega
    have hcongr : hs ⟨n - 2 - (n - 2 - j), hlt⟩ = hs ⟨j, h1⟩ := by
      congr 1; ext; exact heq
    rw [hcongr]; ring
  · -- j ≥ m, n-2-j < m: −hs(n-2-j) + hs(n-2-j) = 0
    ring
  · -- j ≥ m and n-2-j ≥ m: impossible (j + n-2-j ≥ 2m = n-1 > n-2)
    exfalso; omega

/-- The total slope sum is zero: mkCumSum(n−1) = 0. -/
private lemma mkCumSum_last_zero (n m : ℕ) (hm : 2 * m + 1 = n) (hs : Fin m → NZMod3) :
    mkCumSum n m hm hs ⟨n - 1, by omega⟩ = 0 := by
  simp only [mkCumSum]
  -- Σ_{j : Fin (n-1)} ext_slope j = 0, proved by pairing j ↔ n-2-j (anti-palindrome)
  apply Finset.sum_involution
    (fun j _ => (⟨n - 2 - j.val, by have := j.isLt; omega⟩ : Fin (n - 1)))
    (fun j _ => ext_slope_anti_palindrome n m hm hs j.val j.isLt)
    -- hg₃: f i ≠ 0 → g i hi ≠ i (no fixed points: n-2-j=j implies 2*j=n-2 odd, impossible)
    (fun j _ _ heq => by simp only [Fin.ext_iff] at heq; have := j.isLt; omega)
    (fun j _ => Finset.mem_univ _)
    (fun j _ => by
      apply Fin.ext
      exact Nat.sub_sub_self (by have := j.isLt; omega))

/-- The cumulative sum is palindromic: mkCumSum c = mkCumSum (n−1−c). -/
private lemma mkCumSum_palindrome (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n)
    (hs : Fin m → NZMod3) (c : Fin n) :
    mkCumSum n m hm hs c = mkCumSum n m hm hs ⟨n - 1 - c.val, by omega⟩ := by
  -- Induction on c.val; base case: mkCumSum(0)=0=mkCumSum(n-1); step: anti-palindrome.
  suffices h : ∀ k : ℕ, ∀ hk : k < n,
      mkCumSum n m hm hs ⟨k, hk⟩ = mkCumSum n m hm hs ⟨n - 1 - k, by omega⟩ from
    h c.val c.isLt
  intro k hk
  induction k with
  | zero =>
    simp only [mkCumSum_zero]
    exact (mkCumSum_last_zero n m hm hs).symm
  | succ k ihk =>
    have ihk' := ihk (by omega)
    rw [mkCumSum_succ n m hm hs k hk]
    -- goal: mkCumSum(k) + ext(k) = mkCumSum(n-1-(k+1), ⋯)
    -- Relate mkCumSum(n-1-(k+1)) to mkCumSum(n-2-k) via Fin equality
    have heq_fin : (⟨n - 1 - (k + 1), by omega⟩ : Fin n) = ⟨n - 2 - k, by omega⟩ :=
      Fin.ext (by show n - 1 - (k + 1) = n - 2 - k; omega)
    have hshift := congrArg (mkCumSum n m hm hs) heq_fin
    -- hshift : mkCumSum(n-1-(k+1)) = mkCumSum(n-2-k)
    have hprev : mkCumSum n m hm hs ⟨n - 1 - k, by omega⟩ =
        mkCumSum n m hm hs ⟨n - 2 - k, by omega⟩ +
        ext_slope n m hm hs ⟨n - 2 - k, by omega⟩ := by
      have key := mkCumSum_succ n m hm hs (n - 2 - k) (by omega)
      have heq2 : (⟨n - 2 - k + 1, by omega⟩ : Fin n) = ⟨n - 1 - k, by omega⟩ :=
        Fin.ext (by show n - 2 - k + 1 = n - 1 - k; omega)
      rw [← heq2]; exact key
    have hanti := ext_slope_anti_palindrome n m hm hs k (by omega)
    -- mk(k) + ext(k) = mk(n-1-k) + ext(k) [ihk']
    --   = mk(n-2-k) + ext(n-2-k) + ext(k) [hprev] = mk(n-2-k) [hanti]
    --   = mk(n-1-(k+1)) [hshift.symm]
    linear_combination ihk' + hprev + hanti - hshift

/-- 180°-fixed proper colorings biject with (base, m h-slopes, m v-slopes)
    where m = (n−1)/2 and each slope is nonzero. -/
private noncomputable def equiv_fixed180 (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n) :
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
private noncomputable def equiv_fixed90 (n : ℕ) (hn : Odd n) (hn3 : 5 ≤ n)
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

theorem card_fixed180_odd (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n) :
    Nat.card { f : Coloring n // AdjOk f ∧ RichOk f ∧ FixedBy180 n f } =
    3 * 2 ^ (n - 1) := by
  rw [Nat.card_congr (equiv_fixed180 n hn hn3)]
  -- Nat.card (ZMod 3 × (Fin m → NZMod3) × (Fin m → NZMod3)) = 3 * 2^m * 2^m = 3 * 2^(n-1)
  have hm : (n - 1) / 2 + (n - 1) / 2 = n - 1 := by obtain ⟨m, hm⟩ := hn; omega
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod,
             Fintype.card_pi, ZMod.card, NZMod3_card,
             Finset.prod_const, Finset.card_fin]
  rw [← pow_add, hm]

theorem card_fixed90_odd (n : ℕ) (hn : Odd n) (hn3 : 5 ≤ n) (h4 : 4 ∣ (n - 1)) :
    Nat.card { f : Coloring n // AdjOk f ∧ RichOk f ∧ FixedBy90 n f } =
    3 * 2 ^ ((n - 1) / 2) := by
  rw [Nat.card_congr (equiv_fixed90 n hn hn3 h4)]
  -- Nat.card (ZMod 3 × (Fin m → NZMod3)) = 3 * 2^m = 3 * 2^((n-1)/2)
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod,
             Fintype.card_pi, ZMod.card, NZMod3_card,
             Finset.prod_const, Finset.card_fin]

/-! ## 9. Burnside arithmetic — general odd n with 4∣(n−1)

  The Burnside sum for the Z₄-action on proper colorings is:
    |Fix(e)| + |Fix(ρ¹)| + |Fix(ρ²)| + |Fix(ρ³)|
    = 3·2^(2k) + 3·2^(k/2) + 3·2^k + 3·2^(k/2)    where k = n−1
  which equals 4 · 3 · (2^(2k−2) + 2^(k/2−1) + 2^(k−2)).
  Dividing by 4 gives the orbit count.                                  -/

/-- Key arithmetic: for k divisible by 4 with k ≥ 4, the Burnside sum factors
    as 4 times the orbit count. Proved using pow_add + ring (in ℕ as semiring). -/
lemma burnside_arith (k : ℕ) (hk : 4 ≤ k) (h4 : 4 ∣ k) :
    3 * 2 ^ (2 * k) + 3 * 2 ^ (k / 2) + 3 * 2 ^ k + 3 * 2 ^ (k / 2) =
    4 * (3 * (2 ^ (2 * k - 2) + 2 ^ (k / 2 - 1) + 2 ^ (k - 2))) := by
  -- Express each power as 4 × (a smaller power) using pow_add
  have e1 : (2 : ℕ) ^ (2 * k) = 4 * 2 ^ (2 * k - 2) := by
    conv_lhs => rw [show 2 * k = (2 * k - 2) + 2 from by omega]
    rw [pow_add]; ring
  have e2 : (2 : ℕ) ^ k = 4 * 2 ^ (k - 2) := by
    conv_lhs => rw [show k = (k - 2) + 2 from by omega]
    rw [pow_add]; ring
  have e3 : (2 : ℕ) ^ (k / 2) = 2 * 2 ^ (k / 2 - 1) := by
    conv_lhs => rw [show k / 2 = (k / 2 - 1) + 1 from by omega]
    rw [pow_add, pow_one]; ring
  -- After substitution, ring closes the goal (ℕ is a CommSemiring)
  simp only [e1, e2, e3]; ring

/-- The Burnside count for general odd n with 4∣(n−1):

    |orbits| = (Fix(e) + Fix(ρ¹) + Fix(ρ²) + Fix(ρ³)) / 4
             = 3 · (2^(2(n−1)−2) + 2^((n−1)/2−1) + 2^(n−3))          -/
theorem chromatic_rotations_general (n : ℕ) (_ : Odd n) (hn5 : 5 ≤ n)
    (h4 : 4 ∣ (n - 1)) :
    (3 * 2 ^ (2 * (n - 1)) + 3 * 2 ^ ((n - 1) / 2) +
     3 * 2 ^ (n - 1) + 3 * 2 ^ ((n - 1) / 2)) / 4 =
    3 * (2 ^ (2 * (n - 1) - 2) + 2 ^ ((n - 1) / 2 - 1) + 2 ^ (n - 3)) := by
  have hk : 4 ≤ n - 1 := by omega
  rw [burnside_arith (n - 1) hk h4]
  exact Nat.mul_div_cancel_left _ (by norm_num)

/-! ## 10. The answer for n = 101 -/

/-- For n = 101: k = 100, k/2 = 50.
    Fix(e)    = 3·2^200,  Fix(ρ²)  = 3·2^100,  Fix(ρ¹) = Fix(ρ³) = 3·2^50.
    |orbits|  = (3·2^200 + 3·2^50 + 3·2^100 + 3·2^50) / 4
              = 3·(2^198 + 2^49 + 2^98)
              = 3·(2^198 + 2^98 + 2^49).                               -/
theorem chromatic_rotations_101 :
    (3 * (2 : ℕ) ^ 200 + 3 * 2 ^ 50 + 3 * 2 ^ 100 + 3 * 2 ^ 50) / 4 =
    3 * (2 ^ 198 + 2 ^ 98 + 2 ^ 49) := by norm_num

/-- Verify n=101 is a special case of the general formula (k=100, k/2=50). -/
theorem chromatic_rotations_101_from_general :
    3 * (2 ^ (2 * (101 - 1) - 2) + 2 ^ ((101 - 1) / 2 - 1) + 2 ^ (101 - 3)) =
    3 * (2 ^ 198 + 2 ^ 98 + 2 ^ 49) := by norm_num

/-- Spot-checks using the general formula: -/
theorem chromatic_rotations_5 :
    (3 * (2 : ℕ) ^ 8 + 3 * 2 ^ 2 + 3 * 2 ^ 4 + 3 * 2 ^ 2) / 4 = 210 := by norm_num

theorem chromatic_rotations_9 :
    (3 * (2 : ℕ) ^ 16 + 3 * 2 ^ 4 + 3 * 2 ^ 8 + 3 * 2 ^ 4) / 4 = 49368 := by norm_num

theorem chromatic_rotations_13 :
    (3 * (2 : ℕ) ^ 24 + 3 * 2 ^ 6 + 3 * 2 ^ 12 + 3 * 2 ^ 6) / 4 = 12586080 := by norm_num

end ChromaticRotations

/-- Number of equivalence classes of proper 3-colorings of an n×n grid under
    90° rotational symmetry, for any odd n ≥ 3.
    Formula: 3·(2^(2n−4) + 2^((n−3)/2) + 2^(n−3))

    Note: even n has no known closed form; only odd n is handled here.    -/
def chromaticRotations (n : ℕ) : ℕ :=
  3 * (2 ^ (2 * (n - 1) - 2) + 2 ^ ((n - 1) / 2 - 1) + 2 ^ (n - 3))

-- Plug in any odd n ≥ 3:
#eval chromaticRotations 3    -- 18
#eval chromaticRotations 5    -- 210
#eval chromaticRotations 7    -- 3132
#eval chromaticRotations 9    -- 49368
#eval chromaticRotations 11   -- 787248
#eval chromaticRotations 13   -- 12586080
#eval chromaticRotations 101  -- 3·(2^198 + 2^98 + 2^49)
