import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import GriddlesP1Lean.Counting

/-!
# The Answer: n = 101

This file specializes the general formula to n = 101 and provides a computable
function for evaluating the answer at any odd n.

## n = 101

For n = 101: k = n−1 = 100, k/2 = 50, 2k = 200.

The fixed-point counts are:
- |Fix(identity)|  = 3 · 2^200   (all proper colorings)
- |Fix(ρ¹)|        = 3 · 2^50    (90°-fixed)
- |Fix(ρ²)|        = 3 · 2^100   (180°-fixed)
- |Fix(ρ³)|        = 3 · 2^50    (270°-fixed = same as 90°-fixed by symmetry)

Burnside gives:
  |orbits| = (3·2^200 + 3·2^50 + 3·2^100 + 3·2^50) / 4
           = 3 · (2^198 + 2^49 + 2^98)
           = **3 · (2^198 + 2^98 + 2^49)**

Numerically: 1205203533194242706656471569256822689841823419077067014144000

## General formula

For any odd n ≥ 3, the answer is 3·(2^(2n−4) + 2^((n−3)/2) + 2^(n−3)).
(Note: even n has no known closed form.)
-/

namespace ChromaticRotations

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

/-- The answer for n = 101, derived by connecting all four proved cardinalities
    via Burnside's lemma: |orbits| = (|Fix(e)| + |Fix(ρ)| + |Fix(ρ²)| + |Fix(ρ³)|) / 4.

    This is the formal bridge between the structural proofs and the final answer:
    - |Fix(e)|  = card_proper 101           = 3 · 2^200  (all proper colorings)
    - |Fix(ρ)|  = card_fixed90_odd 101      = 3 · 2^50   (90°-fixed)
    - |Fix(ρ²)| = card_fixed180_odd 101     = 3 · 2^100  (180°-fixed)
    - |Fix(ρ³)| = card_fixed90_odd 101      = 3 · 2^50   (270°-fixed = 90°-fixed by symmetry)

    Together: (3·2^200 + 3·2^50 + 3·2^100 + 3·2^50) / 4 = 3·(2^198 + 2^98 + 2^49). -/
theorem chromatic_rotations_101_from_burnside :
    (Nat.card { f : Coloring 101 // AdjOk f ∧ RichOk f } +
     Nat.card { f : Coloring 101 // AdjOk f ∧ RichOk f ∧ FixedBy90 101 f } +
     Nat.card { f : Coloring 101 // AdjOk f ∧ RichOk f ∧ FixedBy180 101 f } +
     Nat.card { f : Coloring 101 // AdjOk f ∧ RichOk f ∧ FixedBy90 101 f }) / 4 =
    3 * (2 ^ 198 + 2 ^ 98 + 2 ^ 49) := by
  rw [card_proper 101 (by norm_num),
      card_fixed180_odd 101 (by decide) (by norm_num),
      card_fixed90_odd 101 (by decide) (by norm_num) (by norm_num)]
  norm_num

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
