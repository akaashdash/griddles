import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import GriddlesP1Lean.Defs

/-!
# Separability of Proper Colorings

The central structural theorem of the Chromatic Rotations problem:

**Every proper coloring f of an n×n grid satisfies f(r,c) = base + R(c) + D(r)**

for some base ∈ ZMod 3, column-offset function R : Fin n → ZMod 3, and
row-offset function D : Fin n → ZMod 3.

## Proof outline

1. **Local slope propagation** (`slope_propagation_local`): In any 2×2 sub-square
   satisfying both constraints, the horizontal color difference is the same in
   both rows, and the vertical color difference is the same in both columns.
   This is proved by exhaustive case analysis on (ZMod 3)⁴ via `decide`.

2. **Global slope invariance** (`hSlope_step`, `vSlope_step`): By induction,
   the horizontal slope h(c) = f(r,c+1) − f(r,c) is independent of r, and the
   vertical slope v(r) = f(r+1,c) − f(r,c) is independent of c.

3. **Column independence of vertical offsets** (`vOffset_col_independent`):
   For any row r and column c, f(r,c) − f(0,c) = f(r,0) − f(0,0).
   In other words, the "vertical offset" at row r doesn't depend on which column
   you're measuring it from. Proved by double induction with `linear_combination`.

4. **Separability** (`ProperColoring.isSeparable`): Take base = f(0,0),
   R(c) = f(0,c) − f(0,0), D(r) = f(r,0) − f(0,0). Then step 3 shows
   f(r,c) = base + R(c) + D(r).
-/

namespace ChromaticRotations

variable {n : ℕ}

/-- In any 2×2 sub-square satisfying (A)+(R), slopes propagate:
      b − a = d − c   (horizontal slope same in both rows)
      c − a = d − b   (vertical slope same in both columns)
    Proof: exhaustive case analysis on (ZMod 3)⁴ via `decide`. -/
lemma slope_propagation_local :
    ∀ (a b c d : ZMod 3),
      a ≠ b → a ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (ZMod 3)).card = 3 →
      b - a = d - c ∧ c - a = d - b := by decide

/-- Horizontal slope: color difference moving right. -/
def hSlope (f : Coloring n) (r c : Fin n) (hc : c.val + 1 < n) : ZMod 3 :=
  f r ⟨c.val + 1, hc⟩ - f r c

/-- Vertical slope: color difference moving down. -/
def vSlope (f : Coloring n) (r c : Fin n) (hr : r.val + 1 < n) : ZMod 3 :=
  f ⟨r.val + 1, hr⟩ c - f r c

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

end ChromaticRotations
