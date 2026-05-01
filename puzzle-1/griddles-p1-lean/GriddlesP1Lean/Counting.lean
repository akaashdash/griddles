import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import GriddlesP1Lean.Defs
import GriddlesP1Lean.Separability
import GriddlesP1Lean.Slopes
import GriddlesP1Lean.Bijections

/-!
# Cardinality Counts and Burnside's Lemma

This file computes the sizes of the fixed-point sets and applies Burnside's lemma
to obtain the orbit count.

## Fixed-point sizes

- `card_fixed180_odd`: |Fix(ρ²)| = 3 · 2^(n−1)
  Follows from `equiv_fixed180`: the parameter space ZMod 3 × (Fin m → NZMod3)² has
  cardinality 3 × 2^m × 2^m = 3 × 2^(2m) = 3 × 2^(n−1).

- `card_fixed90_odd`: |Fix(ρ¹)| = 3 · 2^((n−1)/2)
  Follows from `equiv_fixed90`: the parameter space ZMod 3 × (Fin m → NZMod3) has
  cardinality 3 × 2^m = 3 × 2^((n−1)/2).
  By symmetry |Fix(ρ³)| = |Fix(ρ¹)|.

- The total proper colorings = |Fix(identity)| = 3 · 2^(2(n−1)).

## Burnside's lemma

For the cyclic group Z₄ = {e, ρ, ρ², ρ³} acting on proper colorings:

  |orbits| = (|Fix(e)| + |Fix(ρ)| + |Fix(ρ²)| + |Fix(ρ³)|) / 4
           = (3·2^(2k) + 3·2^(k/2) + 3·2^k + 3·2^(k/2)) / 4    where k = n−1
           = 3 · (2^(2k−2) + 2^(k/2−1) + 2^(k−2))

The arithmetic simplification is `burnside_arith`, and the final formula is
`chromatic_rotations_general`.
-/

namespace ChromaticRotations

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

/-- Total number of proper 3-colorings of an n×n grid (for n ≥ 1).

    Every proper coloring is uniquely determined by:
    - a base color f(0,0) ∈ ZMod 3        (3 choices)
    - n−1 horizontal slopes ∈ NZMod3      (2^(n−1) choices each)
    - n−1 vertical slopes ∈ NZMod3        (2^(n−1) choices each)

    Total: 3 · 2^(n−1) · 2^(n−1) = 3 · 2^(2(n−1)).
    No oddness constraint is needed — this holds for all n ≥ 1. -/
theorem card_proper (n : ℕ) (hn : 1 ≤ n) :
    Nat.card { f : Coloring n // AdjOk f ∧ RichOk f } = 3 * 2 ^ (2 * (n - 1)) := by
  rw [Nat.card_congr (equiv_proper n hn)]
  have hm : (n - 1) + (n - 1) = 2 * (n - 1) := by omega
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod,
             Fintype.card_pi, ZMod.card, NZMod3_card,
             Finset.prod_const, Finset.card_fin]
  rw [← pow_add, hm]

/-- Key arithmetic: for k divisible by 4 with k ≥ 4, the Burnside sum factors
    as 4 times the orbit count. Proved using pow_add + ring (in ℕ as semiring).

    The three helper equalities e1, e2, e3 pull out a factor of 4 from each
    power-of-2 term: 2^(2k) = 4·2^(2k−2), 2^k = 4·2^(k−2), 2^(k/2) = 2·2^(k/2−1). -/
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

end ChromaticRotations
