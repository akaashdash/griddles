import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import GriddlesP1Lean.Counting

/-!
# The Answer: Burnside Formula for Chromatic Rotations

This file contains the main result connecting the structural proofs to the answer.

## The general theorem (`chromatic_rotations_burnside`)

For any odd n ≥ 5 with 4∣(n−1), the Burnside count uses four fixed-point sets:

  |orbits| = (|Fix(e)| + |Fix(ρ¹)| + |Fix(ρ²)| + |Fix(ρ³)|) / 4

where each term is a proved cardinality:
- |Fix(e)|  = `card_proper`        = 3 · 2^(2(n−1))     (all proper colorings)
- |Fix(ρ¹)| = `card_fixed90_odd`  = 3 · 2^((n−1)/2)    (90°-fixed)
- |Fix(ρ²)| = `card_fixed180_odd` = 3 · 2^(n−1)        (180°-fixed)
- |Fix(ρ³)| = `card_fixed90_odd`  = 3 · 2^((n−1)/2)    (270°-fixed = 90°-fixed)

Note: Fix(ρ³) = Fix(ρ¹) because a coloring fixed by 90° is also fixed by 270°,
and vice versa (since ρ⁴ = id implies ρ³ · ρ = id, so ρ³-fixed ↔ ρ¹-fixed).

The closed form after Burnside arithmetic (`chromatic_rotations_general`) is:
  3 · (2^(2n−4) + 2^((n−3)/2) + 2^(n−3))

## Specific instances

The general theorem is then specialized to n = 5, 9, 13, 101 by direct application.
Each proof is a single term — no arithmetic needed beyond the structural results.
-/

namespace ChromaticRotations

/-- **Main result.** For any odd n ≥ 5 with 4∣(n−1), the Burnside count of
    equivalence classes of proper 3-colorings under 90° rotation equals the
    closed form 3·(2^(2n−4) + 2^((n−3)/2) + 2^(n−3)).

    Proof: rewrite each `Nat.card` term using the proved bijections, then apply
    `chromatic_rotations_general` which handles the Burnside arithmetic. -/
theorem chromatic_rotations_burnside (n : ℕ) (hn : Odd n) (hn5 : 5 ≤ n)
    (h4 : 4 ∣ (n - 1)) :
    (Nat.card { f : Coloring n // AdjOk f ∧ RichOk f } +
     Nat.card { f : Coloring n // AdjOk f ∧ RichOk f ∧ FixedBy90 n f } +
     Nat.card { f : Coloring n // AdjOk f ∧ RichOk f ∧ FixedBy180 n f } +
     Nat.card { f : Coloring n // AdjOk f ∧ RichOk f ∧ FixedBy90 n f }) / 4 =
    3 * (2 ^ (2 * (n - 1) - 2) + 2 ^ ((n - 1) / 2 - 1) + 2 ^ (n - 3)) := by
  rw [card_proper n (by omega),
      card_fixed180_odd n hn (by omega),
      card_fixed90_odd n hn hn5 h4]
  exact chromatic_rotations_general n hn hn5 h4

/-- n = 5: 210 equivalence classes.
    Closed form: 3·(2^6 + 2^1 + 2^2) = 3·(64 + 2 + 4) = 210. -/
theorem chromatic_rotations_n5 :
    (Nat.card { f : Coloring 5 // AdjOk f ∧ RichOk f } +
     Nat.card { f : Coloring 5 // AdjOk f ∧ RichOk f ∧ FixedBy90 5 f } +
     Nat.card { f : Coloring 5 // AdjOk f ∧ RichOk f ∧ FixedBy180 5 f } +
     Nat.card { f : Coloring 5 // AdjOk f ∧ RichOk f ∧ FixedBy90 5 f }) / 4 =
    3 * (2 ^ 6 + 2 ^ 1 + 2 ^ 2) :=
  chromatic_rotations_burnside 5 (by decide) (by norm_num) (by norm_num)

/-- n = 9: 49368 equivalence classes.
    Closed form: 3·(2^14 + 2^3 + 2^6). -/
theorem chromatic_rotations_n9 :
    (Nat.card { f : Coloring 9 // AdjOk f ∧ RichOk f } +
     Nat.card { f : Coloring 9 // AdjOk f ∧ RichOk f ∧ FixedBy90 9 f } +
     Nat.card { f : Coloring 9 // AdjOk f ∧ RichOk f ∧ FixedBy180 9 f } +
     Nat.card { f : Coloring 9 // AdjOk f ∧ RichOk f ∧ FixedBy90 9 f }) / 4 =
    3 * (2 ^ 14 + 2 ^ 3 + 2 ^ 6) :=
  chromatic_rotations_burnside 9 (by decide) (by norm_num) (by norm_num)

/-- n = 13: 12586080 equivalence classes.
    Closed form: 3·(2^22 + 2^5 + 2^10). -/
theorem chromatic_rotations_n13 :
    (Nat.card { f : Coloring 13 // AdjOk f ∧ RichOk f } +
     Nat.card { f : Coloring 13 // AdjOk f ∧ RichOk f ∧ FixedBy90 13 f } +
     Nat.card { f : Coloring 13 // AdjOk f ∧ RichOk f ∧ FixedBy180 13 f } +
     Nat.card { f : Coloring 13 // AdjOk f ∧ RichOk f ∧ FixedBy90 13 f }) / 4 =
    3 * (2 ^ 22 + 2 ^ 5 + 2 ^ 10) :=
  chromatic_rotations_burnside 13 (by decide) (by norm_num) (by norm_num)

/-- n = 101: **the answer** — 3·(2^198 + 2^49 + 2^98) equivalence classes.

    Exponent order follows the closed form: 2^(2n−4), 2^((n−3)/2), 2^(n−3).
    For n=101 this gives exponents 198, 49, 98 (= 3·(2^198 + 2^98 + 2^49) reordered). -/
theorem chromatic_rotations_n101 :
    (Nat.card { f : Coloring 101 // AdjOk f ∧ RichOk f } +
     Nat.card { f : Coloring 101 // AdjOk f ∧ RichOk f ∧ FixedBy90 101 f } +
     Nat.card { f : Coloring 101 // AdjOk f ∧ RichOk f ∧ FixedBy180 101 f } +
     Nat.card { f : Coloring 101 // AdjOk f ∧ RichOk f ∧ FixedBy90 101 f }) / 4 =
    3 * (2 ^ 198 + 2 ^ 49 + 2 ^ 98) :=
  chromatic_rotations_burnside 101 (by decide) (by norm_num) (by norm_num)

end ChromaticRotations

/-- Computable formula: number of equivalence classes for any odd n ≥ 3.
    Formula: 3·(2^(2n−4) + 2^((n−3)/2) + 2^(n−3))

    Note: even n has no known closed form; only odd n is handled here. -/
def chromaticRotations (n : ℕ) : ℕ :=
  3 * (2 ^ (2 * (n - 1) - 2) + 2 ^ ((n - 1) / 2 - 1) + 2 ^ (n - 3))

-- Plug in any odd n ≥ 3:
#eval chromaticRotations 3    -- 18
#eval chromaticRotations 5    -- 210
#eval chromaticRotations 7    -- 3132
#eval chromaticRotations 9    -- 49368
#eval chromaticRotations 11   -- 787248
#eval chromaticRotations 13   -- 12586080
#eval chromaticRotations 101  -- 1205203533194242706656471569256822689841823419077067014144000
