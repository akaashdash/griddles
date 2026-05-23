import GriddlesP4Lean.Parity
import GriddlesP4Lean.LemmaA

/-!
# Winning direction (adaptive belief-state reduction)

The fixed-`K` sweep classes (`WinningRestricted`, `WinningKProbe`, `WinningKProbeGen`) prove
`BobWins` for permutations whose per-displacement first-"Yes" thresholds *decode* the start
cell at a *uniform* amplitude.  As documented at the `sorry` in `Answer.lean`, **no fixed `K`
suffices** for all non-eventually-identity `c` (the block-5 witness), so the genuinely-uniform
winning strategy must be **adaptive**: Bob maintains a *belief* — the set of start cells still
consistent with the signals he has seen — and guesses once that belief is a singleton.

This file formalises the **belief-state reduction** so that the only remaining gap is a single,
clearly-named combinatorial localization fact (`adaptive_localizes`).

## What this file builds

1. **Belief / consistency** (`Distinguished`, `Localizes`).  A candidate `k` is *distinguished*
   from the true start `k₀` by time `T` if some probe time `s ≤ T` yields a different signal.
   `Localizes c σ k₀` says: under exploration strategy `σ`, the trajectory from `k₀` stays safe
   through some time `T` and *every* wrong candidate is distinguished by `T`.

2. **Belief-driven strategy transformer** (`beliefStrat`).  Given any exploration strategy `σ`
   that never guesses, `beliefStrat` follows `σ`'s moves until the belief (computed purely from
   the observed history) collapses to a singleton, then guesses that unique candidate's current
   position.  The current position is reconstructed from the history via `dispFromHist`.

3. **Reduction lemma** (`localizes_BobWins`): if `σ` never guesses and `Localizes c σ k₀` for
   every `k₀`, then `BobWins c`.  *Fully proven* — the singleton guess is correct because the
   unique consistent candidate **is** `k₀`, safety transfers from the exploration trajectory,
   and the "first guess at the stop time" obligation is discharged via `Nat.find`.

4. **Isolated lemma** (`adaptive_localizes`): the single `sorry`.  It asserts that for non-EI
   `c` there *exists* a never-guessing exploration strategy that localizes every start cell.
   This is the hard adaptive-combinatorics content; it should be discharged using
   `not_eventually_identity_implies_distinguishable` (`LemmaA`).

5. **Conclusion** (`notEI_BobWins`): chains the reduction with the isolated lemma.

## Honesty note

Exactly **one** `sorry` is introduced (`adaptive_localizes`).  Everything else builds and is
`sorry`-free; the reduction is airtight in the sense that the guess-correctness, safety, and
first-guess-timing obligations of `WinsFrom` are all fully discharged from the localization
hypothesis.  See `#print axioms notEI_BobWins` at the end of the file.
-/

namespace TrolleyRetrieval

variable {c : Perm}

/-! ### Separators: per-displacement signal differences (the "catchable-ahead" language)

A *separator at displacement `D`* for a pair `(a, b)` is a valid reachable time `t`
(`t ≥ D`, `t ≡ D (mod 2)`) at which the displacement-`D` signals of the two trajectories
differ.  This is exactly the per-`D` *negation* of the `Indistinguishable` clause from
`LemmaA`; the bridge `indistinguishable_iff_no_separator` makes that precise.

Trajectory-based discharges of `adaptive_localizes` reason in this language: to localize
`k₀` against a wrong candidate, Bob must drive the trajectory to a separator and read off
the mismatched signal.  The fact that *some* separator exists for every wrong candidate
(`separators_exist`) is the combinatorial heart of localizability; it is the
contrapositive of `LemmaA`. -/

/-- The displacement-`D` cell `a + D : ℕ+` (positivity from `a ≥ 1`).  A local copy of the
    `private` `aD` of `LemmaA`, with the *same* positivity witness used inside the body of
    `Indistinguishable`, so the two reconcile definitionally. -/
def cellAt (a : ℕ+) (D : ℕ) : ℕ+ :=
  ⟨a.val + D, Nat.lt_of_lt_of_le a.property (Nat.le_add_right _ _)⟩

@[simp] lemma cellAt_val (a : ℕ+) (D : ℕ) : (cellAt a D).val = a.val + D := rfl

/-- **Separator at displacement `D`.**  There is a valid reachable time `t` (`t ≥ D`,
    `t ≡ D (mod 2)`) at which the displacement-`D` signals of `a` and `b` differ.

    Stated with `decide`-Booleans `[· < t]` exactly as in the "catchable-ahead" notation;
    the bridge below converts the Boolean inequality to the `Iff` form of
    `Indistinguishable`. -/
def separatedAtDisp (c : Perm) (a b : ℕ+) (D : ℕ) : Prop :=
  ∃ t : ℕ, (t : ℤ) ≥ D ∧ ((t : ℤ) - D) % 2 = 0 ∧
    (decide ((c (cellAt a D)).val < t) ≠ decide ((c (cellAt b D)).val < t))

/-- A Boolean signal-disagreement is the same as the failure of the corresponding `Iff`. -/
private lemma decide_ne_iff_not_iff (P Q : Prop) [Decidable P] [Decidable Q] :
    (decide P ≠ decide Q) ↔ ¬ (P ↔ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- **Bridge: indistinguishability is the absence of separators.**  A pair `(a, b)` is
    `Indistinguishable` iff there is *no* separator at any displacement.

    This is a definitional unfolding once the `decide`/`Iff` correspondence
    (`decide_ne_iff_not_iff`) is applied and the `cellAt` wrapper is reconciled with the
    inline cell of `Indistinguishable`. -/
theorem indistinguishable_iff_no_separator (c : Perm) (a b : ℕ+) :
    Indistinguishable c a b ↔ ∀ D : ℕ, ¬ separatedAtDisp c a b D := by
  constructor
  · -- Indistinguishable ⇒ no separator.
    intro h D
    rintro ⟨t, ht_ge, ht_par, hne⟩
    rw [decide_ne_iff_not_iff] at hne
    exact hne (h D t ht_ge ht_par)
  · -- No separator ⇒ Indistinguishable.
    intro h D t ht_ge ht_par
    by_contra hiff
    exact h D ⟨t, ht_ge, ht_par, (decide_ne_iff_not_iff _ _).mpr hiff⟩

/-- **Separators exist (the "catchable-ahead" fact).**  For a *non-eventually-identity*
    permutation `c`, every pair of distinct start cells `a ≠ b` has at least one separator:
    some displacement `D` and valid reachable time at which their signals differ.

    This is the contrapositive of `LemmaA`
    (`not_eventually_identity_implies_distinguishable`), routed through the
    `indistinguishable_iff_no_separator` bridge, with a WLOG ordering of `a, b` (the
    separator language is symmetric in the pair, and the predicate only differs by the
    Boolean disagreement, which is symmetric). -/
theorem separators_exist (c : Perm) (h : ¬ EventuallyIdentity c) (a b : ℕ+) (hab : a ≠ b) :
    ∃ D : ℕ, separatedAtDisp c a b D := by
  -- Order the pair as `lo < hi`.
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b.
    have hnind : ¬ Indistinguishable c a b :=
      not_eventually_identity_implies_distinguishable h a b hlt
    rw [indistinguishable_iff_no_separator] at hnind
    push_neg at hnind
    obtain ⟨D, hD⟩ := hnind
    exact ⟨D, hD⟩
  · -- b < a; obtain a separator for `(b, a)` and swap.
    have hnind : ¬ Indistinguishable c b a :=
      not_eventually_identity_implies_distinguishable h b a hgt
    rw [indistinguishable_iff_no_separator] at hnind
    push_neg at hnind
    obtain ⟨D, hD⟩ := hnind
    obtain ⟨t, ht_ge, ht_par, hne⟩ := hD
    exact ⟨D, t, ht_ge, ht_par, hne.symm⟩

-- Axiom audit for the separator lemmas.  Both are `sorry`-free: they depend only on the
-- three standard classical axioms `[propext, Classical.choice, Quot.sound]` — NO `sorryAx`.
-- (`separators_exist` routes through `LemmaA`'s axiom-clean
-- `not_eventually_identity_implies_distinguishable`.)
#print axioms indistinguishable_iff_no_separator
#print axioms separators_exist

/-! ### Never-guessing exploration strategies -/

/-- A strategy that *never guesses*: at every history it returns a move.  Exploration
    strategies for the belief reduction are required to be of this form (so their trajectories
    are pure walks, and the displacement is reconstructible from the history). -/
def NeverGuesses (σ : Strategy) : Prop := ∀ h : List Bool, ∃ d : Dir, σ h = .move d

/-- Under a never-guessing strategy, the history length equals the elapsed time. -/
lemma history_length_neverGuesses {σ : Strategy} (hng : NeverGuesses σ) (k₀ : ℤ) :
    ∀ t : ℕ, (history c σ k₀ t).length = t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
      obtain ⟨d, hd⟩ := hng (history c σ k₀ n)
      rw [history_succ_of_move hd, List.length_cons, ih]

/-- Under a never-guessing strategy, the history at time `t+1` prepends the new signal. -/
lemma history_succ_neverGuesses {σ : Strategy} (hng : NeverGuesses σ) (k₀ : ℤ) (t : ℕ) :
    history c σ k₀ (t + 1) =
      signalOf c (position c σ k₀ (t + 1)) (t + 1) :: history c σ k₀ t := by
  obtain ⟨d, hd⟩ := hng (history c σ k₀ t)
  rw [history_succ_of_move hd]
  congr 1
  rw [position_succ_of_move hd]

/-! ### Displacement reconstruction from the history

Bob does not know `k₀`, but he *does* know the strategy `σ` and the observed signal history
`h`.  Since the move at each step is `σ` applied to the *tail* history, Bob can replay his own
moves and recover his net displacement.  `dispFromHist σ h` walks the most-recent-first history
accumulating the per-step deltas. -/

/-- The signed step contributed by an action (`0` for a guess, `±1` for a move). -/
def actionDelta : Action → ℤ
  | .move d => d.delta
  | .guess _ => 0

/-- Net displacement reconstructed from a (most-recent-first) signal history under `σ`.
    The head `b` of `b :: bs` is the *latest* signal; the move that produced it was chosen by
    `σ bs`, so it contributes `actionDelta (σ bs)` on top of the displacement built from `bs`. -/
def dispFromHist (σ : Strategy) : List Bool → ℤ
  | [] => 0
  | _ :: bs => dispFromHist σ bs + actionDelta (σ bs)

/-- **Displacement reconstruction is correct.**  Replaying the moves from the history recovers
    the actual net displacement of the true trajectory.  (Holds for *any* strategy and start —
    not just never-guessing ones — since `actionDelta` returns `0` exactly when the step was a
    guess, matching `position_succ_of_guess`.) -/
lemma dispFromHist_eq (σ : Strategy) (k₀ : ℤ) :
    ∀ t : ℕ, dispFromHist σ (history c σ k₀ t) = displacement c σ k₀ t := by
  intro t
  induction t with
  | zero => simp [dispFromHist, displacement]
  | succ n ih =>
      -- Split on the action chosen from the time-`n` history.
      rcases hact : σ (history c σ k₀ n) with d | g
      · -- move step
        rw [history_succ_of_move hact]
        show dispFromHist σ (history c σ k₀ n) + actionDelta (σ (history c σ k₀ n))
              = displacement c σ k₀ (n + 1)
        rw [ih, hact, displacement_succ_of_move hact]
        rfl
      · -- guess step (position unchanged)
        rw [history_succ_of_guess hact]
        show dispFromHist σ (history c σ k₀ n) + actionDelta (σ (history c σ k₀ n))
              = displacement c σ k₀ (n + 1)
        rw [ih, hact]
        show displacement c σ k₀ n + 0 = displacement c σ k₀ (n + 1)
        unfold displacement
        rw [position_succ_of_guess hact]; ring

/-! ### The belief: candidates consistent with an observed history

A start cell `k` is *consistent* with a most-recent-first history `h` (under exploration
strategy `σ`) if replaying `σ` from `k` for `h.length` steps reproduces exactly `h`.  This is
computable from `h` alone, so Bob can use it; and the true start `k₀` is always consistent with
its own history. -/

/-- `k` is *consistent* with history `h` if the length-`h.length` trajectory from `k` reproduces
    `h`. -/
def Consistent (c : Perm) (σ : Strategy) (h : List Bool) (k : ℕ+) : Prop :=
  history c σ (k : ℤ) h.length = h

/-- The true start cell is always consistent with its own observed history. -/
lemma consistent_self (σ : Strategy) (k₀ : ℕ+) (t : ℕ)
    (hlen : (history c σ (k₀ : ℤ) t).length = t) :
    Consistent c σ (history c σ (k₀ : ℤ) t) k₀ := by
  unfold Consistent
  rw [hlen]

/-! ### Bridge: history-agreement ⇔ signal-agreement (under never-guessing)

The belief is most naturally stated as "the replayed history matches"; the localization
hypothesis is most naturally stated as "the signals match".  Under a never-guessing strategy
these coincide: two starts produce the same history through time `t` iff their per-step signals
agree at every `s ≤ t`.  The forward direction also yields that the *intermediate positions*
(via displacement) stay locked together while histories agree. -/

/-- **History agreement ⇔ signal agreement.**  Under a never-guessing strategy, the two
    trajectories from `k` and `j` have equal histories at time `t` iff they emit equal signals
    at every step `s ≤ t`. -/
lemma history_eq_iff_signals_eq {σ : Strategy} (hng : NeverGuesses σ) (k j : ℤ) :
    ∀ t : ℕ,
      history c σ k t = history c σ j t ↔
      ∀ s : ℕ, s ≤ t → signalOf c (position c σ k s) s = signalOf c (position c σ j s) s := by
  intro t
  induction t with
  | zero =>
      constructor
      · intro _ s hs
        interval_cases s
        -- s = 0: both signals are `signalOf c (position … 0) 0`; at t = 0 only s = 0 is allowed.
        simp [position_zero, signalOf]
      · intro _; rfl
  | succ n ih =>
      constructor
      · intro hhist s hs
        -- The histories at n+1 are conses; equality gives head-equality (the new signals) and
        -- tail-equality (the time-n histories).
        rw [history_succ_neverGuesses hng k n, history_succ_neverGuesses hng j n] at hhist
        have htail : history c σ k n = history c σ j n := (List.cons.injEq _ _ _ _).mp hhist |>.2
        have hhead : signalOf c (position c σ k (n + 1)) (n + 1)
                   = signalOf c (position c σ j (n + 1)) (n + 1) :=
          (List.cons.injEq _ _ _ _).mp hhist |>.1
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hs) with hlt | heq
        · exact (ih.mp htail) s (Nat.lt_succ_iff.mp hlt)
        · subst heq; exact hhead
      · intro hsig
        -- Build the time-(n+1) history equality from tail (IH) and head (s = n+1 signal).
        have htail : history c σ k n = history c σ j n :=
          ih.mpr (fun s hs => hsig s (Nat.le_succ_of_le hs))
        have hhead := hsig (n + 1) (le_refl _)
        rw [history_succ_neverGuesses hng k n, history_succ_neverGuesses hng j n, htail, hhead]

/-! ### Distinguishing and localization

These are stated in the *signal* form (friendly for the isolated lemma).  Via the bridge above
they translate to the *history* form used by the belief strategy. -/

/-- Candidate `k` is *distinguished* from the true start `k₀` by time `T`: some probe time
    `s ≤ T` yields different signals on the two trajectories. -/
def Distinguished (c : Perm) (σ : Strategy) (k₀ k : ℕ+) (T : ℕ) : Prop :=
  ∃ s : ℕ, s ≤ T ∧
    signalOf c (position c σ (k : ℤ) s) s ≠ signalOf c (position c σ (k₀ : ℤ) s) s

/-- **Localization** of a single start cell.  Under exploration strategy `σ`, the trajectory
    from `k₀` is safe through some finite time `T`, and *every* wrong candidate is distinguished
    from `k₀` by `T` (so the only consistent start at `T` is `k₀` itself). -/
def Localizes (c : Perm) (σ : Strategy) (k₀ : ℕ+) : Prop :=
  ∃ T : ℕ,
    (∀ t : ℕ, t ≤ T → 1 ≤ position c σ (k₀ : ℤ) t) ∧
    (∀ k : ℕ+, k ≠ k₀ → Distinguished c σ k₀ k T)

/-! ### The belief as a (classical) singleton predicate on histories -/

open Classical

/-- The belief is *resolved* at history `h` if exactly one start cell is consistent with `h`. -/
def BeliefResolved (c : Perm) (σ : Strategy) (h : List Bool) : Prop :=
  ∃ k : ℕ+, (∀ j : ℕ+, Consistent c σ h j ↔ j = k)

/-- When the belief is resolved, the unique consistent candidate (`Classical.choose`). -/
noncomputable def beliefWitness (c : Perm) (σ : Strategy) (h : List Bool)
    (hres : BeliefResolved c σ h) : ℕ+ :=
  Classical.choose hres

lemma beliefWitness_spec (σ : Strategy) (h : List Bool) (hres : BeliefResolved c σ h) :
    ∀ j : ℕ+, Consistent c σ h j ↔ j = beliefWitness c σ h hres :=
  Classical.choose_spec hres

/-- Clamp an integer position to a `ℕ+` for guessing (dummy `1` when off the board; the dummy
    is never exercised on the real winning play, where the position is `≥ 1`). -/
def guessPos (z : ℤ) : ℕ+ := if h : 1 ≤ z then Int.toPNat z h else 1

@[simp] lemma guessPos_val {z : ℤ} (h : 1 ≤ z) : ((guessPos z : ℕ+) : ℤ) = z := by
  unfold guessPos
  rw [dif_pos h]
  show ((Int.toPNat z h).val : ℤ) = z
  rw [Int.toPNat_val]
  exact Int.toNat_of_nonneg (by linarith)

/-! ### The belief-driven strategy

`beliefStrat c σ`: follow `σ`'s moves until the belief is resolved (exactly one consistent
start), then guess that start's *current* position, reconstructed from the history. -/

/-- The belief-driven strategy transformer. -/
noncomputable def beliefStrat (c : Perm) (σ : Strategy) : Strategy := fun h =>
  if hres : BeliefResolved c σ h then
    Action.guess (guessPos ((beliefWitness c σ h hres : ℤ) + dispFromHist σ h))
  else
    σ h

/-- When the belief is *not* resolved, the belief strategy falls through to the exploration
    move. -/
lemma beliefStrat_unresolved (σ : Strategy) (h : List Bool)
    (hnr : ¬ BeliefResolved c σ h) :
    beliefStrat c σ h = σ h := by
  unfold beliefStrat; rw [dif_neg hnr]

/-- When the belief *is* resolved, the belief strategy guesses the witness's current position. -/
lemma beliefStrat_resolved (σ : Strategy) (h : List Bool)
    (hres : BeliefResolved c σ h) :
    beliefStrat c σ h =
      Action.guess (guessPos ((beliefWitness c σ h hres : ℤ) + dispFromHist σ h)) := by
  unfold beliefStrat; rw [dif_pos hres]

/-! ### Consistency vs. distinguishing (on a real `k₀`-history) -/

/-- On the true `k₀`-history at time `t`, candidate `j` is consistent **iff** it has *not* been
    distinguished from `k₀` by time `t`.  (Bridge between the belief and the localization
    hypothesis, via `history_eq_iff_signals_eq`.) -/
lemma consistent_iff_not_distinguished {σ : Strategy} (hng : NeverGuesses σ)
    (k₀ j : ℕ+) (t : ℕ) :
    Consistent c σ (history c σ (k₀ : ℤ) t) j ↔ ¬ Distinguished c σ k₀ j t := by
  have hlen : (history c σ (k₀ : ℤ) t).length = t := history_length_neverGuesses hng _ t
  unfold Consistent
  rw [hlen]
  rw [history_eq_iff_signals_eq hng (j : ℤ) (k₀ : ℤ) t]
  unfold Distinguished
  constructor
  · intro hall ⟨s, hs, hne⟩
    exact hne (hall s hs)
  · intro hnd s hs
    by_contra hne
    exact hnd ⟨s, hs, hne⟩

/-- **Localization resolves the belief at the stop time.**  If every wrong candidate is
    distinguished by `T`, then on the true `k₀`-history at time `T` the belief is resolved with
    witness `k₀`. -/
lemma beliefResolved_of_localizes {σ : Strategy} (hng : NeverGuesses σ)
    (k₀ : ℕ+) (T : ℕ) (hdist : ∀ k : ℕ+, k ≠ k₀ → Distinguished c σ k₀ k T) :
    BeliefResolved c σ (history c σ (k₀ : ℤ) T) := by
  refine ⟨k₀, fun j => ?_⟩
  constructor
  · intro hcons
    by_contra hne
    have hd : Distinguished c σ k₀ j T := hdist j hne
    exact (consistent_iff_not_distinguished hng k₀ j T).mp hcons hd
  · intro hjk
    subst hjk
    rw [consistent_iff_not_distinguished hng]
    intro ⟨s, _, hne⟩
    exact hne rfl

/-! ### State match: `beliefStrat` tracks the exploration until the belief resolves -/

/-- **State match.**  As long as the belief has *not* resolved at any earlier step (on the true
    exploration history), `beliefStrat c σ` produces exactly the exploration trajectory. -/
lemma beliefStrat_state_eq {σ : Strategy} (hng : NeverGuesses σ) (k₀ : ℤ) :
    ∀ t : ℕ, (∀ n : ℕ, n < t → ¬ BeliefResolved c σ (history c σ k₀ n)) →
      state c (beliefStrat c σ) k₀ t = state c σ k₀ t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
      intro hnr
      have ihn := ih (fun m hm => hnr m (Nat.lt_succ_of_lt hm))
      have hhist : history c (beliefStrat c σ) k₀ n = history c σ k₀ n := by
        unfold history; rw [ihn]
      have hpos : position c (beliefStrat c σ) k₀ n = position c σ k₀ n := by
        unfold position; rw [ihn]
      -- At step n the σ-belief is unresolved, and the belief-strat history equals the σ-history.
      have hnr_n : ¬ BeliefResolved c σ (history c σ k₀ n) := hnr n (Nat.lt_succ_self n)
      obtain ⟨d, hd_expl⟩ := hng (history c σ k₀ n)
      have hact : beliefStrat c σ (history c (beliefStrat c σ) k₀ n) = .move d := by
        rw [hhist, beliefStrat_unresolved σ _ hnr_n, hd_expl]
      have hact_expl : σ (history c σ k₀ n) = .move d := hd_expl
      rw [state_succ, state_succ,
          step_move c (beliefStrat c σ) _ _ _ d hact,
          step_move c σ _ _ _ d hact_expl, hpos, hhist]

/-- The unique consistent candidate on a true `k₀`-history is `k₀` itself. -/
lemma beliefWitness_eq_k0 {σ : Strategy} (hng : NeverGuesses σ) (k₀ : ℕ+) (t : ℕ)
    (hres : BeliefResolved c σ (history c σ (k₀ : ℤ) t)) :
    beliefWitness c σ (history c σ (k₀ : ℤ) t) hres = k₀ := by
  have hlen : (history c σ (k₀ : ℤ) t).length = t := history_length_neverGuesses hng _ t
  have hcons : Consistent c σ (history c σ (k₀ : ℤ) t) k₀ := consistent_self σ k₀ t hlen
  exact ((beliefWitness_spec σ _ hres k₀).mp hcons).symm

/-! ### The reduction lemma -/

/-- **Reduction.**  If `σ` never guesses and *localizes* every start cell, then `beliefStrat c σ`
    is a winning strategy, so `BobWins c`.

The proof is fully discharged:

* the stop time is the *first* time the belief resolves (`Nat.find`), which is `≤` the
  localization time, so it is safe;
* before that time the belief is unresolved, so `beliefStrat` moves (never guesses early) and
  its trajectory matches the exploration trajectory (`beliefStrat_state_eq`);
* at the stop time the unique consistent candidate **is** `k₀` (`beliefWitness_eq_k0`), and the
  guessed position `k₀ + dispFromHist` equals the actual current position
  (`dispFromHist_eq`, `guessPos_val`). -/
theorem localizes_BobWins {σ : Strategy} (hng : NeverGuesses σ)
    (hloc : ∀ k₀ : ℕ+, Localizes c σ k₀) : BobWins c := by
  refine ⟨beliefStrat c σ, fun k₀ => ?_⟩
  classical
  -- The predicate "belief resolved at time n on the true k₀-history".
  set P : ℕ → Prop := fun n => BeliefResolved c σ (history c σ (k₀ : ℤ) n) with hP
  -- From localization, the belief resolves by time T.
  obtain ⟨T, hsafe, hdist⟩ := hloc k₀
  have hPT : P T := beliefResolved_of_localizes hng k₀ T hdist
  have hex : ∃ n, P n := ⟨T, hPT⟩
  -- First resolved time.
  set Tg := Nat.find hex with hTg
  have hTg_spec : P Tg := Nat.find_spec hex
  have hTg_le_T : Tg ≤ T := Nat.find_le hPT
  have hTg_min : ∀ n, n < Tg → ¬ P n := fun n hn => Nat.find_min hex hn
  -- State match through Tg.
  have hmatch : ∀ t : ℕ, t ≤ Tg →
      state c (beliefStrat c σ) (k₀ : ℤ) t = state c σ (k₀ : ℤ) t := by
    intro t ht
    exact beliefStrat_state_eq hng (k₀ : ℤ) t (fun n hn => hTg_min n (lt_of_lt_of_le hn ht))
  have hpos_match : ∀ t : ℕ, t ≤ Tg →
      position c (beliefStrat c σ) (k₀ : ℤ) t = position c σ (k₀ : ℤ) t := by
    intro t ht; unfold position; rw [hmatch t ht]
  have hhist_match : ∀ t : ℕ, t ≤ Tg →
      history c (beliefStrat c σ) (k₀ : ℤ) t = history c σ (k₀ : ℤ) t := by
    intro t ht; unfold history; rw [hmatch t ht]
  refine ⟨Tg, ?_, ?_, ?_⟩
  · -- Safety: positions valid through Tg.
    intro t ht
    rw [hpos_match t ht]
    exact hsafe t (le_trans ht hTg_le_T)
  · -- No guess before Tg: belief unresolved ⇒ beliefStrat moves.
    intro t ht g
    rw [hhist_match t (le_of_lt ht)]
    have hnr : ¬ BeliefResolved c σ (history c σ (k₀ : ℤ) t) := hTg_min t ht
    obtain ⟨d, hd⟩ := hng (history c σ (k₀ : ℤ) t)
    rw [beliefStrat_unresolved σ _ hnr, hd]
    exact Action.noConfusion
  · -- Correct guess at Tg.
    -- Resolution on the (matched) history; witness is k₀.
    have hres_expl : BeliefResolved c σ (history c σ (k₀ : ℤ) Tg) := hTg_spec
    have hwit : beliefWitness c σ (history c σ (k₀ : ℤ) Tg) hres_expl = k₀ :=
      beliefWitness_eq_k0 hng k₀ Tg hres_expl
    -- The belief-strat history at Tg equals the σ-history.
    have hh : history c (beliefStrat c σ) (k₀ : ℤ) Tg = history c σ (k₀ : ℤ) Tg :=
      hhist_match Tg (le_refl Tg)
    -- Resolution transported to the belief-strat history.
    have hres_b : BeliefResolved c σ (history c (beliefStrat c σ) (k₀ : ℤ) Tg) := by
      rw [hh]; exact hres_expl
    -- The actual current position is ≥ 1 (safety).
    have hcur_pos : 1 ≤ position c σ (k₀ : ℤ) Tg := hsafe Tg hTg_le_T
    -- The guessed integer = current position.
    have hguess_val :
        (beliefWitness c σ (history c (beliefStrat c σ) (k₀ : ℤ) Tg) hres_b : ℤ)
          + dispFromHist σ (history c (beliefStrat c σ) (k₀ : ℤ) Tg)
        = position c σ (k₀ : ℤ) Tg := by
      -- Rewrite both occurrences of the belief-strat history to the σ-history.
      -- For the witness we need to transport the proof term too; do it by congruence.
      have hwit_b : (beliefWitness c σ (history c (beliefStrat c σ) (k₀ : ℤ) Tg) hres_b : ℤ)
          = (k₀ : ℤ) := by
        -- consistency of k₀ with the matched history, then witness spec
        have hlen : (history c (beliefStrat c σ) (k₀ : ℤ) Tg).length = Tg := by
          rw [hh]; exact history_length_neverGuesses hng _ Tg
        have hcons : Consistent c σ (history c (beliefStrat c σ) (k₀ : ℤ) Tg) k₀ := by
          unfold Consistent; rw [hlen, hh]
        have hkw := (beliefWitness_spec σ _ hres_b k₀).mp hcons
        rw [← hkw]
      rw [hwit_b, hh, dispFromHist_eq σ (k₀ : ℤ) Tg]
      unfold displacement; ring
    -- Assemble the guess.
    refine ⟨guessPos ((beliefWitness c σ (history c (beliefStrat c σ) (k₀ : ℤ) Tg) hres_b : ℤ)
        + dispFromHist σ (history c (beliefStrat c σ) (k₀ : ℤ) Tg)), ?_, ?_⟩
    · rw [beliefStrat_resolved σ (history c (beliefStrat c σ) (k₀ : ℤ) Tg) hres_b]
    · -- guessed position equals the (belief-strat) current position.
      rw [hpos_match Tg (le_refl Tg)]
      rw [guessPos_val (by rw [hguess_val]; exact hcur_pos)]
      exact hguess_val

/-! ### The isolated hard lemma -/

/-- **Adaptive localization (the single remaining `sorry`).**

For every *non-eventually-identity* permutation `c`, there is a never-guessing exploration
strategy `σ` that *localizes* every start cell: from any `k₀`, `σ`'s trajectory stays safe for
finitely long and rules out every wrong candidate by a signal mismatch.

This is the genuinely hard adaptive-combinatorics content.  By `LemmaA`
(`not_eventually_identity_implies_distinguishable`), every pair of cells `a < b` is
*distinguishable*: there is a *reachable discriminator* `(D, t)` (with `D ≥ 0`, `t ≥ D`,
`t ≡ D (mod 2)`) at which the signals from `a + D` and `b + D` differ.  What remains — and what
this `sorry` packages — is the *constructive scheduling* problem: design ONE never-guessing
strategy whose single trajectory visits, for each `k₀`, enough `(D, t)` pairs (in the correct
parity/timing windows, never falling off the left) to separate `k₀` from *every* other
candidate in finite time.

Three exact-dynamics negative results (documented at the `sorry` in `Answer.lean`) show this
strategy must be genuinely adaptive (belief-guided): no fixed time-indexed displacement schedule
suffices, the two-phase "localize then navigate" approach fails on low-slack discriminators, and
"finite belief" alone does not imply winnability.  Hence the construction here is exactly the
belief-state strategy itself — the foresight invariant that interleaves "ride the diagonal to
catch low-slack discriminators" with "stay near the origin to bound `k₀`" — proven to terminate
(reach a singleton belief) for every `k₀`.

Discharging this lemma is the substantial separate Lean project flagged in `Answer.lean`; the
belief-state *plumbing* (this file's reduction) is complete, so closing this one statement
closes the winning direction of `main`. -/
theorem adaptive_localizes (c : Perm) (h : ¬ EventuallyIdentity c) :
    ∃ σ : Strategy, NeverGuesses σ ∧ ∀ k₀ : ℕ+, Localizes c σ k₀ :=
  sorry

/-! ### Conclusion: the winning direction -/

/-- **Winning direction of the main theorem.**  Every non-eventually-identity permutation is a
    Bob-win.  This is exactly what `Answer.main`'s `←` (`sorry`) branch needs; it chains the
    *fully proven* belief-state reduction (`localizes_BobWins`) with the single isolated
    localization lemma (`adaptive_localizes`). -/
theorem notEI_BobWins (c : Perm) (h : ¬ EventuallyIdentity c) : BobWins c := by
  obtain ⟨σ, hng, hloc⟩ := adaptive_localizes c h
  exact localizes_BobWins hng hloc

-- Axiom audit.  The REDUCTION (`localizes_BobWins`) is `sorry`-free: it depends only on the
-- three standard classical axioms.  The conclusion `notEI_BobWins` additionally depends on
-- `sorryAx` solely through the single isolated lemma `adaptive_localizes`.
#print axioms localizes_BobWins
#print axioms notEI_BobWins

end TrolleyRetrieval
