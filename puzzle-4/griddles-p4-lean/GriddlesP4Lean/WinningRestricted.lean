import GriddlesP4Lean.Parity

/-!
# Winning direction (restricted): a complete strategy under a discriminability hypothesis

The general winning direction (`¬ EventuallyIdentity c → BobWins c`) needs the full
`LemmaA` (including the research-level `Δ ≥ 2` value-hogging argument).  Here we instead
prove a *complete, sorry-free* winning theorem under an explicit hypothesis that supplies
the Phase-2 discriminator directly — capturing the entire game-strategy plumbing
(adaptive Phase 1 + Phase 2 navigation + safety + timing), which is the substantial part.

## The strategy

* **Phase 1.**  Bob oscillates `D_t ∈ {0,1}` (right on even decision times, left on odd).
  At even time `t = 2m` the position is exactly `k₀`, so the signal is `c(k₀) < 2m`.  The
  first "Yes" at an even time `2m*` reveals `c k₀ ∈ {2m*−2, 2m*−1}`, narrowing `k₀` to two
  candidates `p₁ = c⁻¹(2m*−2)`, `p₂ = c⁻¹(2m*−1)`.

* **Phase 2.**  The hypothesis hands Bob a displacement `D` and time `T` (with `T ≥ T₁`,
  parity-consistent) at which the signals from `p₁` and `p₂` differ.  Bob navigates right to
  displacement `D`, reads the signal at `T`, deduces `k₀`, and guesses its position.

This file builds the pieces bottom-up.  First: the Phase-1 oscillation behaviour.
-/

namespace TrolleyRetrieval

variable {c : Perm}

/-- Phase-1 oscillation direction at decision time `t`: right on even, left on odd.
    This keeps the displacement in `{0, 1}` and returns to `k₀` at every even time. -/
def oscDir (t : ℕ) : Dir := if t % 2 = 0 then .right else .left

/-- The pure oscillation strategy (Phase 1 in isolation): always move, never guess. -/
def oscStrat : Strategy := fun h => Action.move (oscDir h.length)

/-- Under any strategy that never guesses, the history length equals the time. -/
lemma history_length_oscStrat (k₀ : ℤ) :
    ∀ t : ℕ, (history c oscStrat k₀ t).length = t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
      have hmove : oscStrat (history c oscStrat k₀ n) = .move (oscDir n) := by
        simp only [oscStrat, ih]
      rw [history_succ_of_move hmove, List.length_cons, ih]

/-- **Phase-1 position.**  Under the oscillation strategy, the position at time `t` is
    `k₀ + (t % 2)`: exactly `k₀` at even times, `k₀ + 1` at odd times. -/
lemma position_oscStrat (k₀ : ℤ) :
    ∀ t : ℕ, position c oscStrat k₀ t = k₀ + (t % 2 : ℕ) := by
  intro t
  induction t with
  | zero => simp [position_zero]
  | succ n ih =>
      have hlen : (history c oscStrat k₀ n).length = n := history_length_oscStrat k₀ n
      have hmove : oscStrat (history c oscStrat k₀ n) = .move (oscDir n) := by
        simp only [oscStrat, hlen]
      rw [position_succ_of_move hmove, ih]
      -- goal: k₀ + (n % 2) + (oscDir n).delta = k₀ + ((n+1) % 2)
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- n even
        have h1 : n % 2 = 0 := by omega
        have h2 : (n + 1) % 2 = 1 := by omega
        have h3 : oscDir n = .right := by simp [oscDir, h1]
        rw [h1, h2, h3]
        push_cast
        simp [Dir.delta]
      · -- n odd
        have h1 : n % 2 = 1 := by omega
        have h2 : (n + 1) % 2 = 0 := by omega
        have h3 : oscDir n = .left := by simp [oscDir, h1]
        rw [h1, h2, h3]
        push_cast
        simp [Dir.delta]

/-- Phase-1 safety: the oscillation never falls off (position stays `≥ k₀ ≥ 1`). -/
lemma position_oscStrat_pos (k₀ : ℕ+) (t : ℕ) :
    1 ≤ position c oscStrat (k₀ : ℤ) t := by
  rw [position_oscStrat]
  have hk : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.property
  have : (0 : ℤ) ≤ ((t % 2 : ℕ) : ℤ) := by positivity
  linarith

/-- `Int.toPNat` is a left inverse of the `ℕ+ → ℤ` coercion. -/
lemma toPNat_coe (k : ℕ+) (h : (1 : ℤ) ≤ (k : ℤ)) : Int.toPNat (k : ℤ) h = k := by
  apply Subtype.ext
  show (k : ℤ).toNat = k.val
  simp

/-- At even times, the position is exactly `k₀`. -/
lemma position_oscStrat_even (k₀ : ℕ+) (t : ℕ) (ht : t % 2 = 0) :
    position c oscStrat (k₀ : ℤ) t = (k₀ : ℤ) := by
  rw [position_oscStrat, ht]; simp

/-- **Phase-1 signal at even times.**  The signal emitted at an even time `t` is exactly
    `c(k₀) < t` — Bob is probing the label of his own (unknown) starting cell. -/
lemma signal_even_oscStrat (k₀ : ℕ+) (t : ℕ) (ht : t % 2 = 0) :
    signalOf c (position c oscStrat (k₀ : ℤ) t) t = decide ((c k₀).val < t) := by
  rw [position_oscStrat_even k₀ t ht]
  have hk : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.property
  rw [signalOf, dif_pos hk, toPNat_coe k₀ hk]

/-- **Phase-1 signal at odd times.**  The signal emitted at an odd time `t` probes the
    label of the cell *next to* the start: `c(k₀ + 1) < t`. -/
lemma signal_odd_oscStrat (k₀ : ℕ+) (t : ℕ) (ht : t % 2 = 1) :
    signalOf c (position c oscStrat (k₀ : ℤ) t) t = decide ((c (k₀ + 1)).val < t) := by
  have hpos : position c oscStrat (k₀ : ℤ) t = ((k₀ + 1 : ℕ+) : ℤ) := by
    rw [position_oscStrat, ht]
    push_cast
    ring
  rw [hpos]
  have hk : (1 : ℤ) ≤ ((k₀ + 1 : ℕ+) : ℤ) := by exact_mod_cast (k₀ + 1).property
  rw [signalOf, dif_pos hk, toPNat_coe (k₀ + 1) hk]

/-- One-step unfolding of the oscillation history: prepend the new signal. -/
lemma history_oscStrat_succ (k₀ : ℤ) (t : ℕ) :
    history c oscStrat k₀ (t + 1) =
      signalOf c (position c oscStrat k₀ (t + 1)) (t + 1) :: history c oscStrat k₀ t := by
  have hlen : (history c oscStrat k₀ t).length = t := history_length_oscStrat k₀ t
  have hmove : oscStrat (history c oscStrat k₀ t) = .move (oscDir t) := by
    simp only [oscStrat, hlen]
  rw [history_succ_of_move hmove]
  congr 1
  rw [position_succ_of_move hmove]

/-! ### Phase-1 detection: first even-time "Yes"

`firstEvenYes h` returns the *earliest* even time at which a "Yes" was observed (or `none`).
The trolley's even-time signals are monotone (`c k₀ < t` once `t > c k₀`), so the first
even-Yes pins down `c k₀ ∈ {T₁−2, T₁−1}` where `T₁` is that time.  Crucially the value is
*stable*: once it is `some T₁`, the cons-recurrence preserves it — so the detector keeps
reporting `T₁` throughout Phase 2, no matter what Bob does there. -/

/-- Scan a most-recent-first signal list (whose head has time `t`) for the *oldest*
    even-time "Yes". -/
def lastEvenYesFrom : List Bool → ℕ → Option ℕ
  | [], _ => none
  | (b :: bs), t =>
      match lastEvenYesFrom bs (t - 1) with
      | some s => some s
      | none => if t % 2 = 0 ∧ b then some t else none

/-- The first (earliest) even time with a "Yes" signal in history `h`, or `none`. -/
def firstEvenYes (h : List Bool) : Option ℕ := lastEvenYesFrom h h.length

/-- Odd-time twin of `lastEvenYesFrom`: scan for the *oldest* odd-time "Yes". -/
def lastOddYesFrom : List Bool → ℕ → Option ℕ
  | [], _ => none
  | (b :: bs), t =>
      match lastOddYesFrom bs (t - 1) with
      | some s => some s
      | none => if t % 2 = 1 ∧ b then some t else none

/-- The first (earliest) odd time with a "Yes" signal in history `h`, or `none`. -/
def firstOddYes (h : List Bool) : Option ℕ := lastOddYesFrom h h.length

/-- **Cons-recurrence for the odd detector.** -/
lemma firstOddYes_cons (b : Bool) (bs : List Bool) :
    firstOddYes (b :: bs) =
      match firstOddYes bs with
      | some s => some s
      | none =>
          if (b :: bs).length % 2 = 1 ∧ b then some ((b :: bs).length) else none := by
  show lastOddYesFrom (b :: bs) (bs.length + 1) = _
  simp only [lastOddYesFrom, Nat.add_sub_cancel, firstOddYes, List.length_cons]

/-- **Cons-recurrence for the detector.**  Prepending the most-recent signal `b` (at time
    `(b :: bs).length`) keeps any earlier even-Yes, else checks the new signal. -/
lemma firstEvenYes_cons (b : Bool) (bs : List Bool) :
    firstEvenYes (b :: bs) =
      match firstEvenYes bs with
      | some s => some s
      | none =>
          if (b :: bs).length % 2 = 0 ∧ b then some ((b :: bs).length) else none := by
  show lastEvenYesFrom (b :: bs) (bs.length + 1) = _
  simp only [lastEvenYesFrom, Nat.add_sub_cancel, firstEvenYes, List.length_cons]

/-! ### Detector behaviour along the oscillation trajectory -/

/-- The smallest even number strictly greater than `v` — the time the even-probe first
    says "Yes" when `c k₀ = v`. -/
def evenThr (v : ℕ) : ℕ := 2 * (v / 2) + 2

/-- The smallest odd number strictly greater than `v`. -/
def oddThr (v : ℕ) : ℕ := 2 * ((v + 1) / 2) + 1

lemma evenThr_even (v : ℕ) : evenThr v % 2 = 0 := by unfold evenThr; omega
lemma evenThr_gt (v : ℕ) : v < evenThr v := by unfold evenThr; omega
lemma evenThr_minimal (v s : ℕ) (hs : s % 2 = 0) (hvs : v < s) : evenThr v ≤ s := by
  unfold evenThr; omega
lemma oddThr_odd (v : ℕ) : oddThr v % 2 = 1 := by unfold oddThr; omega
lemma oddThr_gt (v : ℕ) : v < oddThr v := by unfold oddThr; omega
lemma oddThr_minimal (v s : ℕ) (hs : s % 2 = 1) (hvs : v < s) : oddThr v ≤ s := by
  unfold oddThr; omega

/-- **Even detector on the trajectory.**  Along the oscillation, the first even-time "Yes"
    occurs exactly at `T₁ = evenThr (c k₀)`: the detector is `none` before `T₁` and
    `some T₁` from `T₁` onward. -/
lemma firstEvenYes_oscStrat (k₀ : ℕ+) (t : ℕ) :
    firstEvenYes (history c oscStrat (k₀ : ℤ) t) =
      if evenThr (c k₀).val ≤ t then some (evenThr (c k₀).val) else none := by
  set T₁ := evenThr (c k₀).val with hT₁
  induction t with
  | zero =>
      have : ¬ T₁ ≤ 0 := by have := evenThr_gt (c k₀).val; omega
      simp [firstEvenYes, lastEvenYesFrom, this]
  | succ n ih =>
      rw [history_oscStrat_succ, firstEvenYes_cons]
      have hlen : (history c oscStrat (k₀ : ℤ) n).length = n := history_length_oscStrat _ _
      rw [List.length_cons, hlen, ih]
      by_cases hTn : T₁ ≤ n
      · simp only [hTn, if_true]
        have : T₁ ≤ n + 1 := by omega
        simp [this]
      · rw [if_neg hTn]
        by_cases hpar : (n + 1) % 2 = 0
        · have hsig : signalOf c (position c oscStrat (k₀ : ℤ) (n + 1)) (n + 1)
              = decide ((c k₀).val < (n + 1)) := signal_even_oscStrat k₀ (n + 1) hpar
          rw [hsig]
          by_cases hyes : (c k₀).val < (n + 1)
          · have hge : T₁ ≤ n + 1 := evenThr_minimal _ _ hpar hyes
            have heq : T₁ = n + 1 := by omega
            have hcond : (n + 1) % 2 = 0 ∧ decide ((c k₀).val < (n + 1)) = true :=
              ⟨hpar, by simpa using hyes⟩
            rw [if_pos hcond, heq, if_pos (le_refl (n + 1))]
          · have hno : ¬ T₁ ≤ n + 1 := by
              intro h
              have : (c k₀).val < T₁ := evenThr_gt _
              omega
            have hcond : ¬ ((n + 1) % 2 = 0 ∧ decide ((c k₀).val < (n + 1)) = true) := by
              simp [hyes]
            rw [if_neg hcond, if_neg hno]
        · have hno : ¬ T₁ ≤ n + 1 := by
            intro h
            have hT₁even : T₁ % 2 = 0 := evenThr_even _
            omega
          have hcond : ¬ ((n + 1) % 2 = 0 ∧
              (signalOf c (position c oscStrat (k₀ : ℤ) (n + 1)) (n + 1)) = true) := by
            rintro ⟨h1, -⟩; exact hpar h1
          rw [if_neg hcond, if_neg hno]

/-- **Odd detector on the trajectory.**  The first odd-time "Yes" occurs at
    `T₁' = oddThr (c (k₀ + 1))` — the smallest odd `> c(k₀+1)`. -/
lemma firstOddYes_oscStrat (k₀ : ℕ+) (t : ℕ) :
    firstOddYes (history c oscStrat (k₀ : ℤ) t) =
      if oddThr (c (k₀ + 1)).val ≤ t then some (oddThr (c (k₀ + 1)).val) else none := by
  set T₁' := oddThr (c (k₀ + 1)).val with hT₁'
  induction t with
  | zero =>
      have : ¬ T₁' ≤ 0 := by have := oddThr_gt (c (k₀ + 1)).val; omega
      simp [firstOddYes, lastOddYesFrom, this]
  | succ n ih =>
      rw [history_oscStrat_succ, firstOddYes_cons]
      have hlen : (history c oscStrat (k₀ : ℤ) n).length = n := history_length_oscStrat _ _
      rw [List.length_cons, hlen, ih]
      by_cases hTn : T₁' ≤ n
      · simp only [hTn, if_true]
        have : T₁' ≤ n + 1 := by omega
        simp [this]
      · rw [if_neg hTn]
        by_cases hpar : (n + 1) % 2 = 1
        · have hsig : signalOf c (position c oscStrat (k₀ : ℤ) (n + 1)) (n + 1)
              = decide ((c (k₀ + 1)).val < (n + 1)) := signal_odd_oscStrat k₀ (n + 1) hpar
          rw [hsig]
          by_cases hyes : (c (k₀ + 1)).val < (n + 1)
          · have hge : T₁' ≤ n + 1 := oddThr_minimal _ _ hpar hyes
            have heq : T₁' = n + 1 := by omega
            have hcond : (n + 1) % 2 = 1 ∧ decide ((c (k₀ + 1)).val < (n + 1)) = true :=
              ⟨hpar, by simpa using hyes⟩
            rw [if_pos hcond, heq, if_pos (le_refl (n + 1))]
          · have hno : ¬ T₁' ≤ n + 1 := by
              intro h
              have : (c (k₀ + 1)).val < T₁' := oddThr_gt _
              omega
            have hcond : ¬ ((n + 1) % 2 = 1 ∧ decide ((c (k₀ + 1)).val < (n + 1)) = true) := by
              simp [hyes]
            rw [if_neg hcond, if_neg hno]
        · have hno : ¬ T₁' ≤ n + 1 := by
            intro h
            have hodd : T₁' % 2 = 1 := oddThr_odd _
            omega
          have hcond : ¬ ((n + 1) % 2 = 1 ∧
              (signalOf c (position c oscStrat (k₀ : ℤ) (n + 1)) (n + 1)) = true) := by
            rintro ⟨h1, -⟩; exact hpar h1
          rw [if_neg hcond, if_neg hno]

/-! ### The combined winning strategy and its hypothesis -/

/-- **Hypothesis (locally decodable).**  The map `k₀ ↦ (T₁, T₁')` — where
    `T₁ = evenThr (c k₀)` and `T₁' = oddThr (c (k₀+1))` are the first even/odd "Yes" times —
    admits a left inverse `decode`.  Equivalently, `(c k₀, c (k₀+1))` (up to the ±1 buckets)
    determines `k₀`.  This holds for all "locally 2-distinguishable" permutations such as
    adjacent transpositions and 3-cycles (verified by simulation). -/
def LocallyDecodable (c : Perm) : Prop :=
  ∃ decode : ℕ → ℕ → ℕ+, ∀ k₀ : ℕ+,
    decode (evenThr (c k₀).val) (oddThr (c (k₀ + 1)).val) = k₀

/-- **The winning strategy.**  Oscillate while either detector is silent; once *both* the
    even- and odd-time "Yes" have fired (times `T₁, T₁'`), decode `k₀` and guess the current
    position `k₀ + (t % 2)`. -/
def winStrat (decode : ℕ → ℕ → ℕ+) : Strategy := fun h =>
  match firstEvenYes h with
  | none => Action.move (oscDir h.length)
  | some T₁ =>
    match firstOddYes h with
    | none => Action.move (oscDir h.length)
    | some T₁' =>
        Action.guess (if h.length % 2 = 0 then decode T₁ T₁' else decode T₁ T₁' + 1)

lemma winStrat_move_of_even_none (decode : ℕ → ℕ → ℕ+) (h : List Bool)
    (hfe : firstEvenYes h = none) :
    winStrat decode h = Action.move (oscDir h.length) := by
  simp only [winStrat, hfe]

lemma winStrat_move_of_odd_none (decode : ℕ → ℕ → ℕ+) (h : List Bool)
    (hfo : firstOddYes h = none) :
    winStrat decode h = Action.move (oscDir h.length) := by
  simp only [winStrat, hfo]
  cases firstEvenYes h <;> rfl

lemma winStrat_guess_of_both (decode : ℕ → ℕ → ℕ+) (h : List Bool) {T₁ T₁' : ℕ}
    (hfe : firstEvenYes h = some T₁) (hfo : firstOddYes h = some T₁') :
    winStrat decode h =
      Action.guess (if h.length % 2 = 0 then decode T₁ T₁' else decode T₁ T₁' + 1) := by
  simp only [winStrat, hfe, hfo]

/-- **State match.**  Up to the guess time `T_g = max(T₁, T₁')`, the winning strategy
    produces exactly the oscillation trajectory: before `T_g`, at least one detector is
    silent, so `winStrat` oscillates step-for-step like `oscStrat`. -/
lemma winStrat_state_eq (decode : ℕ → ℕ → ℕ+) (k₀ : ℕ+) :
    ∀ t : ℕ, t ≤ max (evenThr (c k₀).val) (oddThr (c (k₀ + 1)).val) →
      state c (winStrat decode) (k₀ : ℤ) t = state c oscStrat (k₀ : ℤ) t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
      intro hle
      have ihn := ih (by omega)
      have hhist : history c (winStrat decode) (k₀ : ℤ) n = history c oscStrat (k₀ : ℤ) n := by
        unfold history; rw [ihn]
      have hpos : position c (winStrat decode) (k₀ : ℤ) n = position c oscStrat (k₀ : ℤ) n := by
        unfold position; rw [ihn]
      have hlen : (history c oscStrat (k₀ : ℤ) n).length = n := history_length_oscStrat _ _
      -- winStrat oscillates at step n (at least one detector silent, since n < T_g)
      have hmove : winStrat decode (history c (winStrat decode) (k₀ : ℤ) n)
          = .move (oscDir n) := by
        rw [hhist]
        by_cases hT₁ : evenThr (c k₀).val ≤ n
        · have hT₁' : ¬ oddThr (c (k₀ + 1)).val ≤ n := by omega
          have hfo : firstOddYes (history c oscStrat (k₀ : ℤ) n) = none := by
            rw [firstOddYes_oscStrat, if_neg hT₁']
          rw [winStrat_move_of_odd_none _ _ hfo, hlen]
        · have hfe : firstEvenYes (history c oscStrat (k₀ : ℤ) n) = none := by
            rw [firstEvenYes_oscStrat, if_neg hT₁]
          rw [winStrat_move_of_even_none _ _ hfe, hlen]
      have hmove_osc : oscStrat (history c oscStrat (k₀ : ℤ) n) = .move (oscDir n) := by
        simp only [oscStrat, hlen]
      rw [state_succ, state_succ,
          step_move c (winStrat decode) _ _ _ (oscDir n) hmove,
          step_move c oscStrat _ _ _ (oscDir n) hmove_osc, hpos, hhist]

/-! ### The restricted winning theorem -/

/-- **Restricted winning theorem.**  For every *locally decodable* permutation `c`, Bob
    has a winning strategy.  The strategy oscillates, reads off `c k₀` and `c (k₀+1)` from
    the first even/odd "Yes", decodes `k₀`, and guesses its position — all while the trolley
    safely stays in `{k₀, k₀+1}`.  This is a complete, `sorry`-free `BobWins` covering, e.g.,
    adjacent transpositions and 3-cycles. -/
theorem LocallyDecodable_BobWins (c : Perm) (hdec : LocallyDecodable c) : BobWins c := by
  obtain ⟨decode, hdecode⟩ := hdec
  refine ⟨winStrat decode, fun k₀ => ?_⟩
  set T₁ := evenThr (c k₀).val with hT₁def
  set T₁' := oddThr (c (k₀ + 1)).val with hT₁'def
  set Tg := max T₁ T₁' with hTgdef
  have hT₁le : T₁ ≤ Tg := le_max_left _ _
  have hT₁'le : T₁' ≤ Tg := le_max_right _ _
  refine ⟨Tg, ?_, ?_, ?_⟩
  · -- positions valid through Tg
    intro t ht
    have hst := winStrat_state_eq decode k₀ t ht
    have hp : position c (winStrat decode) (k₀ : ℤ) t = position c oscStrat (k₀ : ℤ) t := by
      unfold position; rw [hst]
    rw [hp]; exact position_oscStrat_pos k₀ t
  · -- no guess before Tg
    intro t ht g
    have hst := winStrat_state_eq decode k₀ t (le_of_lt ht)
    have hhist : history c (winStrat decode) (k₀ : ℤ) t = history c oscStrat (k₀ : ℤ) t := by
      unfold history; rw [hst]
    rw [hhist]
    by_cases hT₁t : T₁ ≤ t
    · have hT₁'t : ¬ T₁' ≤ t := by omega
      have hfo : firstOddYes (history c oscStrat (k₀ : ℤ) t) = none := by
        rw [firstOddYes_oscStrat, if_neg hT₁'t]
      rw [winStrat_move_of_odd_none _ _ hfo]; simp
    · have hfe : firstEvenYes (history c oscStrat (k₀ : ℤ) t) = none := by
        rw [firstEvenYes_oscStrat, if_neg hT₁t]
      rw [winStrat_move_of_even_none _ _ hfe]; simp
  · -- correct guess at Tg
    have hst := winStrat_state_eq decode k₀ Tg (le_refl Tg)
    have hhist : history c (winStrat decode) (k₀ : ℤ) Tg = history c oscStrat (k₀ : ℤ) Tg := by
      unfold history; rw [hst]
    have hlen : (history c oscStrat (k₀ : ℤ) Tg).length = Tg := history_length_oscStrat _ _
    have hfe : firstEvenYes (history c oscStrat (k₀ : ℤ) Tg) = some T₁ := by
      rw [firstEvenYes_oscStrat, if_pos hT₁le]
    have hfo : firstOddYes (history c oscStrat (k₀ : ℤ) Tg) = some T₁' := by
      rw [firstOddYes_oscStrat, if_pos hT₁'le]
    have hk0 : decode T₁ T₁' = k₀ := hdecode k₀
    refine ⟨if Tg % 2 = 0 then decode T₁ T₁' else decode T₁ T₁' + 1, ?_, ?_⟩
    · rw [hhist, winStrat_guess_of_both decode _ hfe hfo, hlen]
    · have hp : position c (winStrat decode) (k₀ : ℤ) Tg = position c oscStrat (k₀ : ℤ) Tg := by
        unfold position; rw [hst]
      rw [hp, position_oscStrat]
      by_cases hpar : Tg % 2 = 0
      · rw [if_pos hpar, hk0, hpar]; simp
      · have h1 : Tg % 2 = 1 := by omega
        rw [if_neg hpar, hk0, h1]
        push_cast
        ring

/-! ### Concrete instance: adjacent transpositions

`c` swaps `2k-1 ↔ 2k` for every `k` — a non-eventually-identity permutation.  We show it is
locally decodable, hence `BobWins`, giving a fully concrete worked example. -/

/-- Adjacent-transposition map: `n ↦ n+1` if `n` is odd, `n-1` if `n` is even. -/
def adjF (n : ℕ+) : ℕ+ :=
  ⟨if n.val % 2 = 1 then n.val + 1 else n.val - 1, by
    obtain ⟨v, hv⟩ := n
    show 0 < if v % 2 = 1 then v + 1 else v - 1
    split_ifs with h <;> omega⟩

lemma adjF_val (n : ℕ+) : (adjF n).val = if n.val % 2 = 1 then n.val + 1 else n.val - 1 := rfl

lemma adjF_involutive : Function.Involutive adjF := by
  intro n
  have hn : 1 ≤ n.val := n.property
  apply Subtype.ext
  show (adjF (adjF n)).val = n.val
  rw [adjF_val, adjF_val]
  split_ifs <;> omega

/-- Adjacent transpositions as a permutation of `ℕ+`. -/
def adjPerm : Perm := adjF_involutive.toPerm

@[simp] lemma adjPerm_apply (n : ℕ+) : adjPerm n = adjF n := rfl

/-- Clamp a natural to `ℕ+` (mapping `0 ↦ 1`); the identity on positives. -/
def clampPos (n : ℕ) : ℕ+ := ⟨max 1 n, Nat.lt_of_lt_of_le one_pos (le_max_left 1 n)⟩

/-- Adjacent transpositions are locally decodable: `(c k₀, c (k₀+1))` determines `k₀`. -/
lemma adjPerm_locallyDecodable : LocallyDecodable adjPerm := by
  refine ⟨fun T₁ T₁' => clampPos (if T₁ < T₁' then T₁ else T₁' - 2), fun k₀ => ?_⟩
  obtain ⟨v, hv⟩ := k₀
  apply Subtype.ext
  have e1 : (adjPerm ⟨v, hv⟩).val = if v % 2 = 1 then v + 1 else v - 1 := rfl
  have e2 : (adjPerm (⟨v, hv⟩ + 1)).val
      = if (v + 1) % 2 = 1 then (v + 1) + 1 else (v + 1) - 1 := rfl
  simp only [e1, e2, clampPos, evenThr, oddThr]
  split_ifs <;> omega

/-- **Worked example.**  Bob wins against adjacent transpositions. -/
theorem adjPerm_BobWins : BobWins adjPerm :=
  LocallyDecodable_BobWins adjPerm adjPerm_locallyDecodable

end TrolleyRetrieval
