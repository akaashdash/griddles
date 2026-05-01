import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Definitions

This file sets up the core types and structures for the Chromatic Rotations problem:
counting equivalence classes of proper 3-colorings of an n×n grid under 90° rotational
symmetry.

## The problem

Color every cell of an n×n grid with one of three colors (represented as elements of
`ZMod 3`) subject to two constraints:

- **Adjacency (A)**: no two edge-adjacent (horizontally or vertically neighboring) cells
  share the same color.
- **Richness (R)**: every 2×2 sub-square contains all three colors.

Two colorings are *equivalent* if one can be obtained from the other by a 90° clockwise
rotation. We count the number of equivalence classes.

## Key insight

Every proper coloring is *separable*: there exist sequences R, D and a base value b such
that f(r,c) = b + R(c) + D(r) for all r, c. This is proved in `Separability.lean` and
reduces the problem to counting sequences with the right symmetry properties.
-/

namespace ChromaticRotations

/-- A 3-coloring of the n×n grid. Colors are elements of ZMod 3 = {0, 1, 2}. -/
abbrev Coloring (n : ℕ) := Fin n → Fin n → ZMod 3

variable {n : ℕ}

/-- Adjacency constraint: horizontally and vertically adjacent cells must differ. -/
def AdjOk (f : Coloring n) : Prop :=
  (∀ (r c : Fin n) (hc : c.val + 1 < n), f r c ≠ f r ⟨c.val + 1, hc⟩) ∧
  (∀ (r c : Fin n) (hr : r.val + 1 < n), f r c ≠ f ⟨r.val + 1, hr⟩ c)

/-- Richness constraint: every 2×2 sub-square contains all three colors.
    Together with adjacency, this forces the separable structure. -/
def RichOk (f : Coloring n) : Prop :=
  ∀ (r c : Fin n) (hr : r.val + 1 < n) (hc : c.val + 1 < n),
    ({f r c, f r ⟨c.val + 1, hc⟩,
      f ⟨r.val + 1, hr⟩ c,
      f ⟨r.val + 1, hr⟩ ⟨c.val + 1, hc⟩} : Finset (ZMod 3)).card = 3

/-- A proper coloring satisfies both the adjacency and richness constraints. -/
structure ProperColoring (n : ℕ) where
  toFun  : Coloring n
  adjOk  : AdjOk toFun
  richOk : RichOk toFun

/-- A coloring f is *separable* if f(r,c) = base + R(c) + D(r) for fixed sequences R
    (column offsets) and D (row offsets). This is the key structural property: all proper
    colorings are separable (proved in `Separability.lean`). -/
def IsSeparable (f : Coloring n) : Prop :=
  ∃ (base : ZMod 3) (R : Fin n → ZMod 3) (D : Fin n → ZMod 3),
    ∀ r c, f r c = base + R c + D r

/-- 90° clockwise rotation maps (r,c) to (c, n-1-r). Under this map the n×n grid is
    sent to itself; applying it four times is the identity (proved as `rotate90_pow4`). -/
def rotate90 (n : ℕ) (f : Coloring n) : Coloring n :=
  fun r c => f ⟨n - 1 - c.val, by have := c.isLt; omega⟩ r

/-- Applying rotate90 four times recovers the original coloring: rot^4 = id. -/
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

/-- Rotating a proper coloring gives a proper coloring. Horizontal adjacency of the
    rotated grid comes from vertical adjacency of the original, and vice versa. Richness
    is preserved because rotation permutes the cells of each 2×2 block. -/
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

/-- A coloring fixed by 90° rotation: f(r,c) = f(c, n-1-r) for all r, c. These are the
    colorings in orbits of size 1 under the full rotation group. -/
def FixedBy90 (n : ℕ) (f : Coloring n) : Prop := rotate90 n f = f

/-- A coloring fixed by 180° rotation: f(r,c) = f(n-1-r, n-1-c). These include both
    90°-fixed colorings and colorings in orbits of size 2. -/
def FixedBy180 (n : ℕ) (f : Coloring n) : Prop := rotate90 n (rotate90 n f) = f

end ChromaticRotations
