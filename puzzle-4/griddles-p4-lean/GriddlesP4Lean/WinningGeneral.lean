import GriddlesP4Lean.WinningRestricted
import GriddlesP4Lean.RestrictedSeparation

/-!
# Winning direction (general): `¬ EventuallyIdentity c → BobWins c`

This file builds the **monotone-right** strategy that wins for every permutation that is not
eventually the identity, consuming `restricted_separation` (proved separately) as a black box.

## The strategy

* **Phase 1.**  Bob oscillates exactly like `oscStrat` (right on even decision times, left on
  odd) while `firstEvenYes h = none`.  At the first even-time "Yes" — time
  `T₁ = evenThr (c k₀).val` — the position is exactly `k₀` (displacement `0`) and
  `c k₀ ∈ {T₁ − 2, T₁ − 1}`, narrowing `k₀` to two candidates
  `p₁ = c.symm ⟨T₁−2,_⟩`, `p₂ = c.symm ⟨T₁−1,_⟩`.

* **Phase 2.**  Bob now moves *right every turn*.  At Phase-2 step `D` (current displacement
  `D`, current time `T₁ + D`) the trolley emits `[c (k₀ + D) < T₁ + D]`.
  `restricted_separation` supplies the least displacement `D*` at which the probe signals of
  `p₁` and `p₂` differ; Bob walks right to displacement `D*`, reads the just-observed signal,
  deduces which candidate is the true `k₀`, and guesses its current cell `k₀ + D*`.

The `T₁ = 2` corner (`c k₀ = 1`) is handled separately: there `k₀ = c.symm 1` is already
determined, so Bob guesses immediately at time `2` (position still `k₀`).
-/

namespace TrolleyRetrieval

open Classical

variable {c : Perm}

/-! ### Phase-2 data extracted from `T₁` and `restricted_separation`

Everything below is a function of the (fixed) permutation `c`, the non-eventually-identity
hypothesis `hne`, and the detected first-even-Yes time `T₁`.  We only ever apply these when
`T₁` is even and `≥ 4`, in which case `m := (T₁ - 2)/2` satisfies `2*m = T₁ - 2` and
`2*m + 1 = T₁ - 1`, both `≥ 1`. -/

/-- `m` recovered from `T₁`: with `T₁` even `≥ 4`, `2 * mOf T₁ = T₁ - 2`. -/
def mOf (T₁ : ℕ) : ℕ := (T₁ - 2) / 2

lemma mOf_spec {T₁ : ℕ} (he : T₁ % 2 = 0) (h4 : 4 ≤ T₁) :
    2 * mOf T₁ = T₁ - 2 := by unfold mOf; omega

/-- A `ℕ+` whose value is `T₁ - 2` when `T₁ ≥ 3` (so `T₁ - 2 ≥ 1`), else the dummy `1`. -/
def loVal (T₁ : ℕ) : ℕ+ := ⟨max 1 (T₁ - 2), by positivity⟩

/-- A `ℕ+` whose value is `T₁ - 1` when `T₁ ≥ 2`, else the dummy `1`. -/
def hiVal (T₁ : ℕ) : ℕ+ := ⟨max 1 (T₁ - 1), by positivity⟩

lemma loVal_val {T₁ : ℕ} (h4 : 4 ≤ T₁) : (loVal T₁).val = T₁ - 2 := by
  unfold loVal; show max 1 (T₁ - 2) = T₁ - 2; omega

lemma hiVal_val {T₁ : ℕ} (h4 : 4 ≤ T₁) : (hiVal T₁).val = T₁ - 1 := by
  unfold hiVal; show max 1 (T₁ - 1) = T₁ - 1; omega

/-- First candidate cell: the cell whose label is `T₁ − 2`. -/
def candLo (c : Perm) (T₁ : ℕ) : ℕ+ := c.symm (loVal T₁)

/-- Second candidate cell: the cell whose label is `T₁ − 1`. -/
def candHi (c : Perm) (T₁ : ℕ) : ℕ+ := c.symm (hiVal T₁)

lemma candLo_label {T₁ : ℕ} (h4 : 4 ≤ T₁) : (c (candLo c T₁)).val = T₁ - 2 := by
  unfold candLo; rw [Equiv.apply_symm_apply]; exact loVal_val h4

lemma candHi_label {T₁ : ℕ} (h4 : 4 ≤ T₁) : (c (candHi c T₁)).val = T₁ - 1 := by
  unfold candHi; rw [Equiv.apply_symm_apply]; exact hiVal_val h4

/-! ### The separating displacement `D*`

For a fixed even `T₁ ≥ 4`, the candidates have labels `2m = T₁ − 2` and `2m + 1 = T₁ − 1`, so
`restricted_separation` applies and yields some `D` separating their probe signals.  We take
the *least* such `D` (so step-counting in Phase 2 is clean, and `D* ≥ 1`). -/

/-- The Phase-2 probe predicate: at displacement `D` the candidate-`p` world emits
    `[c (p + D) < T₁ + D]`.  `restricted_separation` separates the two candidates. -/
def probeBool (c : Perm) (T₁ D : ℕ) (p : ℕ+) : Bool :=
  decide ((c (shiftR p D)).val < T₁ + D)

/-- The separating predicate as a `Bool`-inequality (decidable, so `Nat.find` applies). -/
def sepPred (c : Perm) (T₁ D : ℕ) : Prop :=
  probeBool c T₁ D (candLo c T₁) ≠ probeBool c T₁ D (candHi c T₁)

instance (c : Perm) (T₁ D : ℕ) : Decidable (sepPred c T₁ D) := by
  unfold sepPred; infer_instance

/-- Existence of a separating displacement, from `restricted_separation`, packaged in the
    `Bool` form so `Nat.find` can extract the least one. -/
lemma exists_sepPred (hne : ¬ EventuallyIdentity c) {T₁ : ℕ} (he : T₁ % 2 = 0) (h4 : 4 ≤ T₁) :
    ∃ D : ℕ, sepPred c T₁ D := by
  set m := mOf T₁ with hm
  have hms : 2 * m = T₁ - 2 := mOf_spec he h4
  have hp₁ : (c (candLo c T₁)).val = 2 * m := by rw [candLo_label h4]; omega
  have hp₂ : (c (candHi c T₁)).val = 2 * m + 1 := by rw [candHi_label h4]; omega
  obtain ⟨D, hD⟩ := restricted_separation c hne m (candLo c T₁) (candHi c T₁) hp₁ hp₂
  refine ⟨D, ?_⟩
  -- 2*m + 2 + D = T₁ + D since 2*m = T₁ - 2 and T₁ ≥ 4
  have hidx : 2 * m + 2 + D = T₁ + D := by omega
  unfold sepPred probeBool
  rw [hidx] at hD
  -- hD : (… < T₁ + D) ≠ (… < T₁ + D)  as Props; convert to Bool ≠
  simpa using hD

/-- The least separating displacement `D*` for a fixed `T₁` (defined `0` when no separation
    exists, which never happens for the `T₁` we use). -/
noncomputable def sepD (c : Perm) (_hne : ¬ EventuallyIdentity c) (T₁ : ℕ) : ℕ :=
  if h : ∃ D : ℕ, sepPred c T₁ D then Nat.find h else 0

lemma sepD_spec (hne : ¬ EventuallyIdentity c) {T₁ : ℕ} (he : T₁ % 2 = 0) (h4 : 4 ≤ T₁) :
    sepPred c T₁ (sepD c hne T₁) := by
  have hex := exists_sepPred hne he h4
  unfold sepD; rw [dif_pos hex]; exact Nat.find_spec hex

lemma sepD_min (hne : ¬ EventuallyIdentity c) {T₁ D : ℕ} (he : T₁ % 2 = 0) (h4 : 4 ≤ T₁)
    (hD : D < sepD c hne T₁) : ¬ sepPred c T₁ D := by
  have hex := exists_sepPred hne he h4
  unfold sepD at hD; rw [dif_pos hex] at hD
  exact Nat.find_min hex hD

/-- `D* ≥ 1`: at displacement `0` both probes agree (both labels `< T₁`), so the least
    separating displacement is positive. -/
lemma sepD_pos (hne : ¬ EventuallyIdentity c) {T₁ : ℕ} (he : T₁ % 2 = 0) (h4 : 4 ≤ T₁) :
    1 ≤ sepD c hne T₁ := by
  rcases Nat.eq_zero_or_pos (sepD c hne T₁) with h0 | h; swap
  · exact h
  -- if D* = 0, the separation at displacement 0 fails: both labels are < T₁
  exfalso
  have hsep := sepD_spec hne he h4
  rw [h0] at hsep
  unfold sepPred probeBool at hsep
  rw [shiftR_zero, shiftR_zero, candLo_label h4, candHi_label h4] at hsep
  apply hsep
  have h1 : decide (T₁ - 2 < T₁ + 0) = true := by simp; omega
  have h2 : decide (T₁ - 1 < T₁ + 0) = true := by simp; omega
  rw [h1, h2]

/-! ### The monotone-right strategy -/

/-- The cell whose label is `1` (the `T₁ = 2`, i.e. `c k₀ = 1`, corner). -/
def oneCell (c : Perm) : ℕ+ := c.symm ⟨1, one_pos⟩

/-- **The monotone-right winning strategy.**

* While `firstEvenYes h = none`: oscillate exactly like `oscStrat`.
* On the first even-Yes `T₁`:
  * `T₁ = 2`: the start is `c.symm 1`; guess it (position is still `k₀` at time `2`).
  * `T₁ ≥ 4`: let `D = h.length − T₁` be the Phase-2 step.  While `D < D*`, move right;
    on reaching `D = D*`, read the head signal and guess the matching candidate's current cell.
-/
noncomputable def monoStrat (c : Perm) (hne : ¬ EventuallyIdentity c) : Strategy := fun h =>
  match firstEvenYes h with
  | none => Action.move (oscDir h.length)
  | some T₁ =>
      if T₁ < 4 then
        Action.guess (oneCell c)
      else
        let D := h.length - T₁
        if D < sepD c hne T₁ then
          Action.move .right
        else
          -- D = D*: decide which candidate matches the observed head signal
          if h.head?.getD false = probeBool c T₁ (sepD c hne T₁) (candLo c T₁) then
            Action.guess (shiftR (candLo c T₁) (sepD c hne T₁))
          else
            Action.guess (shiftR (candHi c T₁) (sepD c hne T₁))

lemma monoStrat_move_of_even_none (hne : ¬ EventuallyIdentity c) (h : List Bool)
    (hfe : firstEvenYes h = none) :
    monoStrat c hne h = Action.move (oscDir h.length) := by
  simp only [monoStrat, hfe]

/-- **Phase-2 action characterization.**  When the even-detector reports `some T₁` with
    `T₁ ≥ 4` and the history has length `T₁ + D`, the action is: a right-move if `D < D*`,
    otherwise the candidate guess decided by the head signal. -/
lemma monoStrat_phase2 (hne : ¬ EventuallyIdentity c) (h : List Bool) {T₁ D : ℕ}
    (hfe : firstEvenYes h = some T₁) (h4 : 4 ≤ T₁) (hlen : h.length = T₁ + D) :
    monoStrat c hne h =
      (if D < sepD c hne T₁ then Action.move .right
       else if h.head?.getD false = probeBool c T₁ (sepD c hne T₁) (candLo c T₁) then
              Action.guess (shiftR (candLo c T₁) (sepD c hne T₁))
            else Action.guess (shiftR (candHi c T₁) (sepD c hne T₁))) := by
  have hnlt : ¬ T₁ < 4 := by omega
  have hsub : T₁ + D - T₁ = D := by omega
  simp only [monoStrat, hfe, hlen, hnlt, if_false, hsub]

/-- **Phase-2 probe-signal identity.**  At the right-shifted cell `(k₀ : ℤ) + D` and time
    `T₁ + D`, the trolley emits exactly `probeBool c T₁ D k₀ = [c (k₀ + D) < T₁ + D]`. -/
lemma signal_at_shiftR (k₀ : ℕ+) (T₁ D : ℕ) :
    signalOf c ((k₀ : ℤ) + (D : ℕ)) (T₁ + D) = probeBool c T₁ D k₀ := by
  have hk : (1 : ℤ) ≤ (k₀ : ℤ) + (D : ℕ) := by
    have h1 : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.property
    have h2 : (0 : ℤ) ≤ (D : ℕ) := by positivity
    linarith
  rw [signalOf, dif_pos hk]
  unfold probeBool
  have heq : Int.toPNat ((k₀ : ℤ) + (D : ℕ)) hk = shiftR k₀ D := by
    apply Subtype.ext
    show ((k₀ : ℤ) + (D : ℕ)).toNat = (shiftR k₀ D).val
    rw [shiftR_val]
    have : ((k₀ : ℤ) + (D : ℕ)) = ((k₀.val + D : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [heq]

/-! ### Phase-1 alignment: before `T₁`, the mono strategy mirrors the oscillation -/

/-- Up to time `T₁ = evenThr (c k₀).val`, `monoStrat` produces exactly the oscillation
    trajectory: before `T₁` the even-detector is silent, so it oscillates step-for-step. -/
lemma monoStrat_state_eq (hne : ¬ EventuallyIdentity c) (k₀ : ℕ+) :
    ∀ t : ℕ, t ≤ evenThr (c k₀).val →
      state c (monoStrat c hne) (k₀ : ℤ) t = state c oscStrat (k₀ : ℤ) t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
      intro hle
      have ihn := ih (by omega)
      have hhist : history c (monoStrat c hne) (k₀ : ℤ) n = history c oscStrat (k₀ : ℤ) n := by
        unfold history; rw [ihn]
      have hpos : position c (monoStrat c hne) (k₀ : ℤ) n = position c oscStrat (k₀ : ℤ) n := by
        unfold position; rw [ihn]
      have hlen : (history c oscStrat (k₀ : ℤ) n).length = n := history_length_oscStrat _ _
      -- n < T₁, so the even detector is still silent at step n
      have hnT₁ : ¬ evenThr (c k₀).val ≤ n := by omega
      have hfe : firstEvenYes (history c oscStrat (k₀ : ℤ) n) = none := by
        rw [firstEvenYes_oscStrat, if_neg hnT₁]
      have hmove : monoStrat c hne (history c (monoStrat c hne) (k₀ : ℤ) n)
          = .move (oscDir n) := by
        rw [hhist, monoStrat_move_of_even_none hne _ hfe, hlen]
      have hmove_osc : oscStrat (history c oscStrat (k₀ : ℤ) n) = .move (oscDir n) := by
        simp only [oscStrat, hlen]
      rw [state_succ, state_succ,
          step_move c (monoStrat c hne) _ _ _ (oscDir n) hmove,
          step_move c oscStrat _ _ _ (oscDir n) hmove_osc, hpos, hhist]

/-! ### Phase-2 tracking: monotone-right navigation to displacement `D*` -/

/-- **Phase-2 tracking.**  Writing `T₁ = evenThr (c k₀).val` (assumed `≥ 4`), for every
    `D ≤ D* = sepD c hne T₁` the trolley at time `T₁ + D` sits at `(k₀ : ℤ) + D`, the history
    has length `T₁ + D`, and the even-detector still reports `some T₁`. -/
lemma phase2_track (hne : ¬ EventuallyIdentity c) (k₀ : ℕ+)
    (h4 : 4 ≤ evenThr (c k₀).val) :
    ∀ D : ℕ, D ≤ sepD c hne (evenThr (c k₀).val) →
      position c (monoStrat c hne) (k₀ : ℤ) (evenThr (c k₀).val + D)
          = (k₀ : ℤ) + (D : ℕ) ∧
      (history c (monoStrat c hne) (k₀ : ℤ) (evenThr (c k₀).val + D)).length
          = evenThr (c k₀).val + D ∧
      firstEvenYes (history c (monoStrat c hne) (k₀ : ℤ) (evenThr (c k₀).val + D))
          = some (evenThr (c k₀).val) := by
  set T₁ := evenThr (c k₀).val with hT₁def
  have hT₁even : T₁ % 2 = 0 := evenThr_even _
  intro D
  induction D with
  | zero =>
      intro _
      -- base: time T₁, use Phase-1 alignment
      have hst : state c (monoStrat c hne) (k₀ : ℤ) T₁ = state c oscStrat (k₀ : ℤ) T₁ :=
        monoStrat_state_eq hne k₀ T₁ (le_refl _)
      refine ⟨?_, ?_, ?_⟩
      · simp only [Nat.cast_zero, add_zero]
        have : position c (monoStrat c hne) (k₀ : ℤ) T₁ = position c oscStrat (k₀ : ℤ) T₁ := by
          unfold position; rw [hst]
        rw [this, position_oscStrat_even k₀ T₁ hT₁even]
      · simp only [Nat.add_zero]
        have : history c (monoStrat c hne) (k₀ : ℤ) T₁ = history c oscStrat (k₀ : ℤ) T₁ := by
          unfold history; rw [hst]
        rw [this, history_length_oscStrat]
      · simp only [Nat.add_zero]
        have : history c (monoStrat c hne) (k₀ : ℤ) T₁ = history c oscStrat (k₀ : ℤ) T₁ := by
          unfold history; rw [hst]
        rw [this, firstEvenYes_oscStrat, if_pos (le_refl T₁)]
  | succ D ih =>
      intro hle
      obtain ⟨ihpos, ihlen, ihfe⟩ := ih (by omega)
      -- at step T₁ + D the strategy moves right (since D < D*)
      have hDlt : D < sepD c hne T₁ := by omega
      have hmove : monoStrat c hne (history c (monoStrat c hne) (k₀ : ℤ) (T₁ + D))
          = .move .right := by
        have hnlt : ¬ T₁ < 4 := by omega
        have hsub : T₁ + D - T₁ = D := by omega
        simp only [monoStrat, ihfe, ihlen, hnlt, if_false, hsub, if_pos hDlt]
      refine ⟨?_, ?_, ?_⟩
      · -- position
        have hp : position c (monoStrat c hne) (k₀ : ℤ) (T₁ + D + 1)
            = position c (monoStrat c hne) (k₀ : ℤ) (T₁ + D) + (Dir.right).delta :=
          position_succ_of_move hmove
        have : T₁ + (D + 1) = T₁ + D + 1 := by omega
        rw [this, hp, ihpos]
        push_cast
        simp [Dir.delta]
        ring
      · -- length
        have hh : history c (monoStrat c hne) (k₀ : ℤ) (T₁ + D + 1)
            = signalOf c (position c (monoStrat c hne) (k₀ : ℤ) (T₁ + D) + (Dir.right).delta)
                (T₁ + D + 1) :: history c (monoStrat c hne) (k₀ : ℤ) (T₁ + D) :=
          history_succ_of_move hmove
        have he : T₁ + (D + 1) = T₁ + D + 1 := by omega
        rw [he, hh, List.length_cons, ihlen]
      · -- firstEvenYes stable
        have hh : history c (monoStrat c hne) (k₀ : ℤ) (T₁ + D + 1)
            = signalOf c (position c (monoStrat c hne) (k₀ : ℤ) (T₁ + D) + (Dir.right).delta)
                (T₁ + D + 1) :: history c (monoStrat c hne) (k₀ : ℤ) (T₁ + D) :=
          history_succ_of_move hmove
        have he : T₁ + (D + 1) = T₁ + D + 1 := by omega
        rw [he, hh, firstEvenYes_cons, ihfe]

/-! ### Candidate membership

From `T₁ = evenThr (c k₀).val` we recover `c k₀ ∈ {T₁ − 2, T₁ − 1}`, hence (by injectivity)
`k₀` is one of the two candidates. -/

/-- `evenThr v ∈ {v + 1, v + 2}`, so `v ∈ {T₁ − 2, T₁ − 1}` where `T₁ = evenThr v`. -/
lemma label_mem_candidates (k₀ : ℕ+) :
    (c k₀).val = evenThr (c k₀).val - 2 ∨ (c k₀).val = evenThr (c k₀).val - 1 := by
  unfold evenThr; omega

/-- The true start is one of the two candidates. -/
lemma start_eq_candidate (k₀ : ℕ+) (h4 : 4 ≤ evenThr (c k₀).val) :
    k₀ = candLo c (evenThr (c k₀).val) ∨ k₀ = candHi c (evenThr (c k₀).val) := by
  set T₁ := evenThr (c k₀).val with hT₁def
  rcases label_mem_candidates k₀ with h | h
  · left
    apply c.injective
    apply Subtype.ext
    show (c k₀).val = (c (candLo c T₁)).val
    rw [candLo_label (c := c) h4]
    exact h
  · right
    apply c.injective
    apply Subtype.ext
    show (c k₀).val = (c (candHi c T₁)).val
    rw [candHi_label (c := c) h4]
    exact h

/-! ### No-guess-before-`T` helper

Before time `T₁`, the strategy oscillates (so it is a move).  This handles the safety and the
no-early-guess obligations on the Phase-1 segment, shared by both the corner and main cases. -/

/-- Before `T₁`, `monoStrat` agrees with `oscStrat` on history, so it returns a move. -/
lemma monoStrat_move_before_T₁ (hne : ¬ EventuallyIdentity c) (k₀ : ℕ+) {t : ℕ}
    (ht : t < evenThr (c k₀).val) :
    ∃ d, monoStrat c hne (history c (monoStrat c hne) (k₀ : ℤ) t) = .move d := by
  have hst := monoStrat_state_eq hne k₀ t (le_of_lt ht)
  have hhist : history c (monoStrat c hne) (k₀ : ℤ) t = history c oscStrat (k₀ : ℤ) t := by
    unfold history; rw [hst]
  have hfe : firstEvenYes (history c oscStrat (k₀ : ℤ) t) = none := by
    rw [firstEvenYes_oscStrat, if_neg (by omega)]
  refine ⟨oscDir t, ?_⟩
  rw [hhist, monoStrat_move_of_even_none hne _ hfe, history_length_oscStrat]

/-- Before `T₁`, the position equals the oscillation position, hence is `≥ 1` (safe). -/
lemma monoStrat_pos_before_T₁ (hne : ¬ EventuallyIdentity c) (k₀ : ℕ+) {t : ℕ}
    (ht : t ≤ evenThr (c k₀).val) :
    1 ≤ position c (monoStrat c hne) (k₀ : ℤ) t := by
  have hst := monoStrat_state_eq hne k₀ t ht
  have hp : position c (monoStrat c hne) (k₀ : ℤ) t = position c oscStrat (k₀ : ℤ) t := by
    unfold position; rw [hst]
  rw [hp]; exact position_oscStrat_pos k₀ t

/-! ### The general winning theorem -/

/-- **General winning direction.**  Every permutation that is not eventually the identity is
    won by Bob via the monotone-right strategy. -/
theorem notEventuallyIdentity_BobWins (c : Perm) (hne : ¬ EventuallyIdentity c) :
    BobWins c := by
  refine ⟨monoStrat c hne, fun k₀ => ?_⟩
  set v := (c k₀).val with hvdef
  set T₁ := evenThr v with hT₁def
  have hT₁even : T₁ % 2 = 0 := evenThr_even _
  have hvpos : 1 ≤ v := (c k₀).property
  by_cases hv1 : v = 1
  · -- corner case c k₀ = 1: T₁ = 2, guess oneCell = k₀ at time 2
    have hT₁2 : T₁ = 2 := by rw [hT₁def, hv1]; unfold evenThr; omega
    -- k₀ = oneCell c
    have hk0 : oneCell c = k₀ := by
      unfold oneCell
      have : c k₀ = ⟨1, one_pos⟩ := by apply Subtype.ext; show (c k₀).val = 1; omega
      rw [← this, Equiv.symm_apply_apply]
    refine ⟨T₁, ?_, ?_, ?_⟩
    · -- safety through T₁ = 2
      intro t ht
      exact monoStrat_pos_before_T₁ hne k₀ ht
    · -- no guess before T₁
      intro t ht g
      obtain ⟨d, hd⟩ := monoStrat_move_before_T₁ hne k₀ ht
      rw [hd]; simp
    · -- correct guess at T₁ = 2
      have hst := monoStrat_state_eq hne k₀ T₁ (le_refl _)
      have hhist : history c (monoStrat c hne) (k₀ : ℤ) T₁ = history c oscStrat (k₀ : ℤ) T₁ := by
        unfold history; rw [hst]
      have hlen : (history c oscStrat (k₀ : ℤ) T₁).length = T₁ := history_length_oscStrat _ _
      have hfe : firstEvenYes (history c oscStrat (k₀ : ℤ) T₁) = some T₁ := by
        rw [firstEvenYes_oscStrat, if_pos (le_refl _)]
      refine ⟨oneCell c, ?_, ?_⟩
      · -- the action chosen at T₁ is the guess of oneCell
        rw [hhist]
        have hlt : T₁ < 4 := by omega
        simp only [monoStrat, hfe, hlen, hlt, if_true]
      · -- position at T₁ = 2 is k₀, and oneCell = k₀
        have hp : position c (monoStrat c hne) (k₀ : ℤ) T₁
            = position c oscStrat (k₀ : ℤ) T₁ := by unfold position; rw [hst]
        rw [hp, position_oscStrat_even k₀ T₁ hT₁even, ← hk0]
  · -- main case v ≥ 2: T₁ ≥ 4, navigate right to D*, guess
    have hv2 : 2 ≤ v := by omega
    have h4 : 4 ≤ T₁ := by rw [hT₁def]; unfold evenThr; omega
    set Dstar := sepD c hne T₁ with hDstar
    have hDpos : 1 ≤ Dstar := sepD_pos hne hT₁even h4
    -- the full track up to D*
    obtain ⟨htpos, htlen, htfe⟩ := phase2_track hne k₀ h4 Dstar (le_refl _)
    refine ⟨T₁ + Dstar, ?_, ?_, ?_⟩
    · -- safety: positions valid through T₁ + Dstar
      intro t ht
      by_cases htT₁ : t ≤ T₁
      · exact monoStrat_pos_before_T₁ hne k₀ htT₁
      · -- t = T₁ + D for some D ≤ Dstar; use phase2_track position
        obtain ⟨D, hD⟩ : ∃ D, t = T₁ + D := ⟨t - T₁, by omega⟩
        have hDle : D ≤ Dstar := by omega
        obtain ⟨hp, _, _⟩ := phase2_track hne k₀ h4 D hDle
        rw [hD, hp]
        have : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.property
        have : (0 : ℤ) ≤ (D : ℕ) := by positivity
        linarith
    · -- no guess before T₁ + Dstar
      intro t ht g
      by_cases htT₁ : t < T₁
      · obtain ⟨d, hd⟩ := monoStrat_move_before_T₁ hne k₀ htT₁
        rw [hd]; simp
      · -- T₁ ≤ t < T₁ + Dstar; t = T₁ + D, D < Dstar; strategy moves right
        obtain ⟨D, hD⟩ : ∃ D, t = T₁ + D := ⟨t - T₁, by omega⟩
        have hDlt : D < Dstar := by omega
        obtain ⟨_, hlen, hfe⟩ := phase2_track hne k₀ h4 D (le_of_lt hDlt)
        have hact : monoStrat c hne (history c (monoStrat c hne) (k₀ : ℤ) t)
            = .move .right := by
          rw [hD, monoStrat_phase2 hne _ hfe h4 hlen, ← hDstar, if_pos hDlt]
        rw [hact]; simp
    · -- correct guess at T₁ + Dstar
      -- write Dstar = D' + 1 (since Dstar ≥ 1) so the last step is a right-move
      obtain ⟨D', hD'⟩ : ∃ D', Dstar = D' + 1 := ⟨Dstar - 1, by omega⟩
      have hD'lt : D' < Dstar := by omega
      -- at step T₁ + D' the strategy moves right; the history head at T₁ + Dstar is the probe
      obtain ⟨hp', hlen', hfe'⟩ := phase2_track hne k₀ h4 D' (le_of_lt hD'lt)
      have hmove' : monoStrat c hne (history c (monoStrat c hne) (k₀ : ℤ) (T₁ + D'))
          = .move .right := by
        rw [monoStrat_phase2 hne _ hfe' h4 hlen', ← hDstar, if_pos hD'lt]
      -- the history at T₁ + Dstar = (T₁ + D') + 1
      have hidx : T₁ + Dstar = (T₁ + D') + 1 := by omega
      have hhist : history c (monoStrat c hne) (k₀ : ℤ) (T₁ + Dstar)
          = signalOf c (position c (monoStrat c hne) (k₀ : ℤ) (T₁ + D')
              + (Dir.right).delta) (T₁ + Dstar)
            :: history c (monoStrat c hne) (k₀ : ℤ) (T₁ + D') := by
        rw [hidx]; exact history_succ_of_move hmove'
      -- compute the head signal = probeBool c T₁ Dstar k₀
      have hheadpos : position c (monoStrat c hne) (k₀ : ℤ) (T₁ + D')
          + (Dir.right).delta = (k₀ : ℤ) + (Dstar : ℕ) := by
        rw [hp']; simp only [Dir.delta_right]; omega
      have hhead : signalOf c (position c (monoStrat c hne) (k₀ : ℤ) (T₁ + D')
              + (Dir.right).delta) (T₁ + Dstar)
          = probeBool c T₁ Dstar k₀ := by
        rw [hheadpos]; exact signal_at_shiftR k₀ T₁ Dstar
      -- the firstEvenYes at T₁ + Dstar is some T₁
      have hfeT : firstEvenYes (history c (monoStrat c hne) (k₀ : ℤ) (T₁ + Dstar)) = some T₁ :=
        htfe
      -- the separation that decides which candidate matches the head
      have hsep : sepPred c T₁ Dstar := sepD_spec hne hT₁even h4
      -- the head value of the history equals the probe of the true start
      have hheadeq : (history c (monoStrat c hne) (k₀ : ℤ) (T₁ + Dstar)).head?.getD false
          = probeBool c T₁ Dstar k₀ := by
        rw [hhist]; simp only [List.head?_cons, Option.getD_some]; exact hhead
      -- k₀ is one of the candidates
      rcases start_eq_candidate k₀ h4 with hcand | hcand
      · -- k₀ = candLo: head = probeBool ... (candLo), so the `if` triggers, guess candLo+Dstar
        have hheadlo : (history c (monoStrat c hne) (k₀ : ℤ) (T₁ + Dstar)).head?.getD false
            = probeBool c T₁ Dstar (candLo c T₁) := by rw [hheadeq, ← hcand]
        refine ⟨shiftR (candLo c T₁) Dstar, ?_, ?_⟩
        · -- action is the guess
          rw [monoStrat_phase2 hne _ hfeT h4 htlen, ← hDstar,
            if_neg (lt_irrefl Dstar), if_pos hheadlo]
        · -- the guessed cell equals the position
          rw [htpos, ← hcand]
          show ((shiftR k₀ Dstar : ℕ+) : ℤ) = (k₀ : ℤ) + (Dstar : ℕ)
          rw [shiftR_val]; push_cast; ring
      · -- k₀ = candHi: head ≠ probeBool ... (candLo) by separation, so guess candHi+Dstar
        have hheadhi : (history c (monoStrat c hne) (k₀ : ℤ) (T₁ + Dstar)).head?.getD false
            = probeBool c T₁ Dstar (candHi c T₁) := by rw [hheadeq, ← hcand]
        have hne_lo : ¬ ((history c (monoStrat c hne) (k₀ : ℤ) (T₁ + Dstar)).head?.getD false
            = probeBool c T₁ Dstar (candLo c T₁)) := by
          rw [hheadhi]
          intro heq
          exact hsep heq.symm
        refine ⟨shiftR (candHi c T₁) Dstar, ?_, ?_⟩
        · rw [monoStrat_phase2 hne _ hfeT h4 htlen, ← hDstar,
            if_neg (lt_irrefl Dstar), if_neg hne_lo]
        · rw [htpos, ← hcand]
          show ((shiftR k₀ Dstar : ℕ+) : ℤ) = (k₀ : ℤ) + (Dstar : ℕ)
          rw [shiftR_val]; push_cast; ring

end TrolleyRetrieval
