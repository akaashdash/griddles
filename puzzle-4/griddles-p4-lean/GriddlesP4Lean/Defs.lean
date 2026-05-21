import Mathlib.Data.PNat.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

/-!
# Definitions

Game semantics for the Trolley Retrieval problem (Puzzle 4 of the GRiddles Series A).

## Setup

A one-way infinite sequence of cells, indexed by positive integers `1, 2, 3, …`.  Each
cell `n` carries a label `c n` where `c : ℕ+ ≃ ℕ+` is a fixed permutation of positive
integers.  An invisible trolley sits on an unknown starting cell `k₀ : ℕ+`.

At each integer time `t ≥ 1`:

1. Bob picks a direction (`.left` or `.right`); the trolley moves one cell that way.
2. If the new position is `0`, Bob loses.  Otherwise the trolley emits a Boolean signal:
   `true` ("Yes") iff `c k_t < t`; `false` ("No") otherwise.

At any decision point (including `t = 0`, before any move) Bob may instead `.guess` a
cell.  A correct guess wins; an incorrect guess or falling off loses.

## Modelling choices

* Positions are stored as `ℤ` so that "fell off the left" is `≤ 0`.  The label is only
  meaningful when the position is `≥ 1`, in which case we cast to `ℕ+`.
* A strategy is a function `List Bool → Action`.  The history list is *most-recent-first*.
* Game trajectories continue forever in the model (we just keep applying `step`); winning
  requires that *the first guess* produced by the strategy be both timely (position is a
  valid cell) and correct.
-/

namespace TrolleyRetrieval

/-- A direction Bob may push the trolley each turn. -/
inductive Dir : Type
  | left
  | right
  deriving DecidableEq, Repr

namespace Dir

/-- Signed unit step on `ℤ` for each direction. -/
def delta : Dir → ℤ
  | .left  => -1
  | .right => 1

@[simp] lemma delta_left  : Dir.delta .left  = -1 := rfl
@[simp] lemma delta_right : Dir.delta .right =  1 := rfl

/-- The displacement contributed by one direction always has absolute value `1`. -/
lemma delta_abs (d : Dir) : d.delta.natAbs = 1 := by
  cases d <;> rfl

end Dir

/-- A decision Bob may make at a decision point: move one step, or guess a cell. -/
inductive Action : Type
  | move  (d : Dir)
  | guess (n : ℕ+)
  deriving Repr

/-- A *permutation* labelling cells: a bijection `ℕ+ ≃ ℕ+`. -/
abbrev Perm := ℕ+ ≃ ℕ+

/-- Bob's strategy: from a history of signals (most-recent-first) choose an action. -/
abbrev Strategy := List Bool → Action

variable (c : Perm) (σ : Strategy)

/-- Convert a positive `ℤ` to `ℕ+`.  Used to look up labels at safe positions. -/
@[inline] def Int.toPNat (n : ℤ) (h : 1 ≤ n) : ℕ+ :=
  ⟨n.toNat, by
    have hnn : (0 : ℤ) ≤ n := by linarith
    have : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hnn
    have h2 : (1 : ℤ) ≤ (n.toNat : ℤ) := by rw [this]; exact h
    exact_mod_cast h2⟩

@[simp] lemma Int.toPNat_val (n : ℤ) (h : 1 ≤ n) :
    (Int.toPNat n h : ℕ+).val = n.toNat := rfl

/-- The signal emitted by the trolley after moving to position `p` at time `t`.

If `p` is a valid cell (`1 ≤ p`), the signal is `true` iff the label there is `< t`.
If `p ≤ 0`, the trolley has fallen off — the signal we return is `false`, but in that
case Bob has already lost and the signal is irrelevant. -/
def signalOf (p : ℤ) (t : ℕ) : Bool :=
  if h : 1 ≤ p then
    decide ((c (Int.toPNat p h)).val < t)
  else
    false

/-- One transition of the game.

Given the previous position and history, the next state is computed by reading
`σ prev_hist` to obtain the action.  A *move* shifts position by `±1`; a *guess*
leaves the position unchanged (the game has already ended by the time this happens
in any meaningful trajectory, so the value is harmless).  The new signal is then
computed from the new position and the current time. -/
def step (prev_pos : ℤ) (prev_hist : List Bool) (t : ℕ) : ℤ × List Bool :=
  match σ prev_hist with
  | .move  d => (prev_pos + d.delta, signalOf c (prev_pos + d.delta) t :: prev_hist)
  | .guess _ => (prev_pos,           signalOf c prev_pos             t :: prev_hist)

@[simp] lemma step_move (p : ℤ) (h : List Bool) (t : ℕ) (d : Dir)
    (hd : σ h = .move d) :
    step c σ p h t = (p + d.delta, signalOf c (p + d.delta) t :: h) := by
  simp [step, hd]

@[simp] lemma step_guess (p : ℤ) (h : List Bool) (t : ℕ) (g : ℕ+)
    (hg : σ h = .guess g) :
    step c σ p h t = (p, signalOf c p t :: h) := by
  simp [step, hg]

/-- The (position, signal-history) state at time `t` under strategy `σ` starting from
    `k₀`.  Signal history is most-recent first. -/
def state (k₀ : ℤ) : ℕ → ℤ × List Bool
  | 0     => (k₀, [])
  | t+1   =>
    let prev := state k₀ t
    step c σ prev.1 prev.2 (t+1)

/-- The trolley's position at time `t`. -/
def position (k₀ : ℤ) (t : ℕ) : ℤ := (state c σ k₀ t).1

/-- The signal history at time `t` (most-recent first). -/
def history  (k₀ : ℤ) (t : ℕ) : List Bool := (state c σ k₀ t).2

/-- Bob's net displacement at time `t` (relative to the starting cell). -/
def displacement (k₀ : ℤ) (t : ℕ) : ℤ := position c σ k₀ t - k₀

@[simp] lemma position_zero (k₀ : ℤ) : position c σ k₀ 0 = k₀ := rfl
@[simp] lemma history_zero  (k₀ : ℤ) : history  c σ k₀ 0 = [] := rfl
@[simp] lemma displacement_zero (k₀ : ℤ) : displacement c σ k₀ 0 = 0 := by
  simp [displacement]

/-- Bob *wins from* starting cell `k₀` if there is a finite stop time `T` at which:

* every visited position through time `T` is a valid cell (`≥ 1`);
* his action chosen at every earlier decision point is a move (so the *first* guess
  comes at time `T`);
* at time `T` he guesses the trolley's actual position. -/
def WinsFrom (k₀ : ℕ+) : Prop :=
  ∃ T : ℕ,
    (∀ t, t ≤ T → 1 ≤ position c σ (k₀ : ℤ) t) ∧
    (∀ t, t < T → ∀ g, σ (history c σ (k₀ : ℤ) t) ≠ .guess g) ∧
    ∃ g : ℕ+,
      σ (history c σ (k₀ : ℤ) T) = .guess g ∧ (g : ℤ) = position c σ (k₀ : ℤ) T

/-- Bob has a winning strategy for the permutation `c` iff some strategy wins from
    every starting cell. -/
def BobWins (c : Perm) : Prop :=
  ∃ σ : Strategy, ∀ k₀ : ℕ+, WinsFrom c σ k₀

/-- `c` is *eventually identity* if there is some threshold `N` past which `c`
    fixes every cell. -/
def EventuallyIdentity (c : Perm) : Prop :=
  ∃ N : ℕ+, ∀ n : ℕ+, N ≤ n → c n = n

end TrolleyRetrieval
