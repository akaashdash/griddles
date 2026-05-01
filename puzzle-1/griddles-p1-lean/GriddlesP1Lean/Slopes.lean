import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import GriddlesP1Lean.Defs
import GriddlesP1Lean.Separability

/-!
# Slope Extension and Cumulative Sums

This file develops the machinery for constructing palindromic colorings from
free slope parameters.

## Setting

For odd n = 2m+1, a 180°-fixed separable coloring f(r,c) = base + R(c) + D(r) must
satisfy R(c) = R(n−1−c) and D(r) = D(n−1−r) (the palindrome conditions). In terms of
slopes h_j = R(j+1) − R(j), the palindrome condition becomes:
  h_{n−2−j} = −h_j   (anti-palindrome on slopes)

So the n−1 slopes are determined by the m = (n−1)/2 free slopes h_0, ..., h_{m−1}.

## Construction

Given `hs : Fin m → NZMod3` (m nonzero slopes), we define:
- `ext_slope n m hm hs j` = hs(j)         for j < m
                           = −hs(n−2−j)   for j ≥ m   (the reflection)
- `mkCumSum n m hm hs c`  = Σ_{j<c} ext_slope j   (running total = R(c) − R(0))

Key properties proved here:
- `ext_slope_ne_zero`: every extended slope is nonzero (in {1, 2})
- `mkCumSum_succ`: mkCumSum(c+1) = mkCumSum(c) + ext_slope(c)
- `ext_slope_anti_palindrome`: ext_slope(j) + ext_slope(n−2−j) = 0
- `mkCumSum_last_zero`: the full sum Σ_{j<n−1} ext_slope(j) = 0 (total sum is 0)
- `mkCumSum_palindrome`: mkCumSum(c) = mkCumSum(n−1−c)   ← the key palindrome
-/

namespace ChromaticRotations

/-- Nonzero elements of ZMod 3. Since ZMod 3 = {0,1,2}, we have NZMod3 = {1,2}. These
    are exactly the valid slope values: a slope of 0 would mean two adjacent cells have
    the same color. -/
abbrev NZMod3 : Type := {x : ZMod 3 // x ≠ 0}

/-- NZMod3 has exactly 2 elements: {1, 2}. -/
lemma NZMod3_card : Fintype.card NZMod3 = 2 := by decide

/-- A 2×2 block whose horizontal slope h and vertical slope v are both nonzero contains
    all 3 colors. The four cells are a, a+h, a+v, a+h+v; when h≠0 and v≠0, these are all
    distinct mod 3. Proved by `decide` (exhaustive check on ZMod 3³). -/
lemma richness_from_slopes :
    ∀ (a h v : ZMod 3), h ≠ 0 → v ≠ 0 →
      ({a, a + h, a + v, a + h + v} : Finset (ZMod 3)).card = 3 := by decide

-- ext_slope needs hm to prove the reflected index is < m in the else branch
/-- Extend m free slopes to all n−1 slopes via the anti-palindrome reflection rule:
    ext_slope j = hs(j) for j < m, and ext_slope j = −hs(n−2−j) for j ≥ m. -/
noncomputable def ext_slope (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n)
    (hs : Fin m → NZMod3) (j : Fin (n - 1)) : ZMod 3 :=
  if h : j.val < m then (hs ⟨j.val, h⟩).val
  else -(hs ⟨n - 2 - j.val, by omega⟩).val

-- Use Fin c.val as index so j.isLt : j.val < c.val is in scope
/-- Cumulative sum of ext_slope up to (but not including) column c.
    This equals R(c) − R(0) in the palindromic coloring. -/
noncomputable def mkCumSum (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n)
    (hs : Fin m → NZMod3) (c : Fin n) : ZMod 3 :=
  ∑ j : Fin c.val, ext_slope n m hm hs ⟨j.val, by have := j.isLt; have := c.isLt; omega⟩

/-- ext_slope is nonzero at every index. -/
lemma ext_slope_ne_zero (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n)
    (hs : Fin m → NZMod3) (j : Fin (n - 1)) : ext_slope n m hm hs j ≠ 0 := by
  simp only [ext_slope]
  split_ifs with h
  · exact (hs ⟨j.val, h⟩).prop
  · simp only [neg_ne_zero]
    exact (hs ⟨n - 2 - j.val, by omega⟩).prop

/-- mkCumSum at 0 is 0. -/
lemma mkCumSum_zero (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n) (hs : Fin m → NZMod3) :
    mkCumSum n m hm hs ⟨0, by omega⟩ = 0 := by
  simp [mkCumSum]

/-- mkCumSum at successor: mkCumSum (j+1) = mkCumSum j + ext_slope j. -/
lemma mkCumSum_succ (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n) (hs : Fin m → NZMod3)
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
lemma mkCumSum_palindrome (n : ℕ) (m : ℕ) (hm : 2 * m + 1 = n)
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

end ChromaticRotations
