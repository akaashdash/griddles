import GriddlesP4Lean.WinningRestricted

/-!
# Winning direction (parametric `K`): a complete strategy under a `K`-distinguishability hypothesis

`WinningRestricted.lean` (K=2) and `WinningKProbe.lean` (K=3) prove complete, `sorry`-free
winning theorems for the *locally 2- and 3-distinguishable* classes.  This file generalises the
probe amplitude to an **arbitrary** `K : ℕ+`: Bob runs the period-`2K` reflecting triangle
wave, samples cells `k₀, k₀+1, …, k₀+K` on the *upswing*, reads off the per-displacement first
"Yes" times, decodes `k₀`, and guesses its position.

## The strategy

* **Sweep.**  Bob runs the period-`2K` triangle wave with displacements
  `0,1,…,K,K−1,…,1,0,1,…` (`tri K t = reflect (t % 2K)`).  Safety is automatic: displacement
  `≥ 0`, so position `≥ k₀ ≥ 1`.

* **Per-displacement upswing detectors.**  For each `v ∈ {0,…,K}` we monitor the *upswing*
  occurrences of displacement `v` — the times `t ≡ v (mod 2K)` — for the first "Yes".  Along the
  trajectory this fires at the clean arithmetic-progression threshold
  `upThr v K (c (k₀+v)) = ` the least `t ≡ v (mod 2K)` with `t > c(k₀+v)` (and `t ≥ 1`).

* **Decode + guess.**  Once *all* `K+1` detectors have fired, the hypothesis decodes `k₀`, and
  Bob guesses the current position `k₀ + tri K t`.

This is a single, parametric generalisation of `WinningKProbe.lean` (which is the `K=3`,
two-residues-per-displacement instance; here we use one residue per displacement, the upswing,
which is cleaner and suffices).

## Scope

This **strictly broadens** the proven Bob-win class (e.g. it covers reverse-block-5, which needs
`K=4`).  It does **not** prove the full winning direction `¬EventuallyIdentity → BobWins`: there
are non-eventually-identity permutations for which *no* fixed `K` makes the upswing-threshold
tuple injective — see the obstacle note in `Answer.lean` (block-5 is the witness).
-/

namespace TrolleyRetrieval

variable {c : Perm}

/-! ### Offset helper: add a `ℕ` displacement to a starting `ℕ+` cell -/

/-- Cell `k₀ + v` as a `ℕ+` (positivity from `k₀ ≥ 1`).  Mirrors `aD` from `LemmaA`. -/
def offCell (k₀ : ℕ+) (v : ℕ) : ℕ+ :=
  ⟨k₀.val + v, Nat.lt_of_lt_of_le k₀.property (Nat.le_add_right _ _)⟩

@[simp] lemma offCell_val (k₀ : ℕ+) (v : ℕ) : (offCell k₀ v).val = k₀.val + v := rfl

/-! ### Phase-1 sweep (period-`2K` reflecting triangle wave) -/

/-- Reflect a residue `r ∈ [0, 2K)` into `[0, K]`: identity below `K`, mirror above. -/
def reflectK (K : ℕ+) (r : ℕ) : ℕ := if r ≤ K.val then r else 2 * K.val - r

/-- Reflecting triangle displacement of amplitude `K`: `0,1,…,K,K−1,…,1` repeating with
    period `2K`. -/
def triK (K : ℕ+) (t : ℕ) : ℕ := reflectK K (t % (2 * K.val))

/-- Sweep direction at decision time `t`: right while on the upswing (`t % 2K < K`), else
    left. -/
def triDir (K : ℕ+) (t : ℕ) : Dir := if t % (2 * K.val) < K.val then .right else .left

/-- The pure sweep strategy (Phase 1 in isolation): always move, never guess. -/
def sweepK (K : ℕ+) : Strategy := fun h => Action.move (triDir K h.length)

/-- `triDir` in terms of the residue. -/
lemma triDir_eq (K : ℕ+) (t : ℕ) :
    triDir K t = if t % (2 * K.val) < K.val then .right else .left := rfl

/-- The key one-step recurrence: `triK K t + (triDir K t).delta = triK K (t+1)`. -/
lemma triK_step (K : ℕ+) (t : ℕ) :
    (triK K t : ℤ) + (triDir K t).delta = (triK K (t + 1) : ℤ) := by
  have hK : 0 < K.val := K.property
  have hP : 0 < 2 * K.val := by omega
  have hrlt : t % (2 * K.val) < 2 * K.val := Nat.mod_lt _ hP
  have h1mod : (1 : ℕ) % (2 * K.val) = 1 := Nat.mod_eq_of_lt (by omega)
  set r := t % (2 * K.val) with hr
  have hr1 : (t + 1) % (2 * K.val) = (r + 1) % (2 * K.val) := by
    rw [hr, Nat.add_mod t 1 (2 * K.val), h1mod]
  rw [triK, triK, triDir_eq, ← hr, hr1, reflectK]
  -- Forget `r = t % 2K`; keep only `r < 2K` (hrlt) so omega can reduce `(r+1) % 2K`.
  clear_value r
  clear hr hr1
  -- The integer value of `reflectK K x` for `x ≤ 2K`, as an omega-friendly fact.
  have hrefl : ∀ x : ℕ, x ≤ 2 * K.val →
      ((if x ≤ K.val then x else 2 * K.val - x : ℕ) : ℤ)
        = if x ≤ K.val then (x : ℤ) else 2 * (K.val : ℤ) - x := by
    intro x hx
    split_ifs with h
    · rfl
    · push_cast [Nat.cast_sub (by omega : x ≤ 2 * K.val)]; ring
  -- Resolve `(r+1) % 2K`: `0` at the wrap point `r+1 = 2K`, else `r+1`.
  by_cases hwrap : r + 1 = 2 * K.val
  · -- wrap: triK (r+1) = reflectK 0 = 0.  (`omega` can't do `% (2*K.val)`; use mod lemmas.)
    have hmod : (r + 1) % (2 * K.val) = 0 := by rw [hwrap]; exact Nat.mod_self _
    rw [hmod, reflectK]
    rw [hrefl r (by omega), hrefl 0 (by omega)]
    split_ifs <;> simp only [Dir.delta] <;> omega
  · -- no wrap: triK (r+1) = reflectK (r+1).
    have hmod : (r + 1) % (2 * K.val) = r + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod, reflectK]
    rw [hrefl r (by omega), hrefl (r + 1) (by omega)]
    split_ifs <;> simp only [Dir.delta] <;> omega

/-- At an *upswing* time (`t ≡ v (mod 2K)` with `v ≤ K`), the displacement is exactly `v`. -/
lemma triK_at_upswing (K : ℕ+) (t v : ℕ) (hmod : t % (2 * K.val) = v) (hv : v ≤ K.val) :
    triK K t = v := by
  rw [triK, hmod, reflectK, if_pos hv]

/-- `triK` is always `≤ K` (so displacement never exceeds the amplitude). -/
lemma triK_le (K : ℕ+) (t : ℕ) : triK K t ≤ K.val := by
  rw [triK, reflectK]
  have hK : 0 < K.val := K.property
  have hlt : t % (2 * K.val) < 2 * K.val := Nat.mod_lt _ (by omega)
  split_ifs with h <;> omega

/-! ### Phase-1 sweep position and safety -/

/-- Under the sweep strategy (which never guesses), the history length equals the time. -/
lemma history_length_sweepK (K : ℕ+) (k₀ : ℤ) :
    ∀ t : ℕ, (history c (sweepK K) k₀ t).length = t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
      have hmove : sweepK K (history c (sweepK K) k₀ n) = .move (triDir K n) := by
        simp only [sweepK, ih]
      rw [history_succ_of_move hmove, List.length_cons, ih]

/-- **Phase-1 position.**  Under the sweep, the position at time `t` is `k₀ + triK K t`. -/
lemma position_sweepK (K : ℕ+) (k₀ : ℤ) :
    ∀ t : ℕ, position c (sweepK K) k₀ t = k₀ + (triK K t : ℕ) := by
  intro t
  induction t with
  | zero => simp [position_zero, triK, reflectK]
  | succ n ih =>
      have hlen : (history c (sweepK K) k₀ n).length = n := history_length_sweepK K k₀ n
      have hmove : sweepK K (history c (sweepK K) k₀ n) = .move (triDir K n) := by
        simp only [sweepK, hlen]
      rw [position_succ_of_move hmove, ih]
      have hkey := triK_step K n
      push_cast
      linarith [hkey]

/-- Phase-1 safety: the sweep never falls off (position stays `≥ k₀ ≥ 1`). -/
lemma position_sweepK_pos (K : ℕ+) (k₀ : ℕ+) (t : ℕ) :
    1 ≤ position c (sweepK K) (k₀ : ℤ) t := by
  rw [position_sweepK]
  have hk : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.property
  have : (0 : ℤ) ≤ ((triK K t : ℕ) : ℤ) := by positivity
  linarith

/-- At an upswing time for displacement `v ≤ K`, the position is exactly `k₀ + v`. -/
lemma position_sweepK_upswing (K : ℕ+) (k₀ : ℕ+) (t v : ℕ)
    (hmod : t % (2 * K.val) = v) (hv : v ≤ K.val) :
    position c (sweepK K) (k₀ : ℤ) t = ((offCell k₀ v : ℕ+) : ℤ) := by
  rw [position_sweepK, triK_at_upswing K t v hmod hv]
  push_cast [offCell_val]; ring

/-- **Signal at an upswing time.**  At a time `t ≡ v (mod 2K)` (`v ≤ K`), the sweep probes
    `c (k₀ + v) < t`. -/
lemma signal_upswing_sweepK (K : ℕ+) (k₀ : ℕ+) (t v : ℕ)
    (hmod : t % (2 * K.val) = v) (hv : v ≤ K.val) :
    signalOf c (position c (sweepK K) (k₀ : ℤ) t) t = decide ((c (offCell k₀ v)).val < t) := by
  rw [position_sweepK_upswing K k₀ t v hmod hv]
  have hk : (1 : ℤ) ≤ ((offCell k₀ v : ℕ+) : ℤ) := by exact_mod_cast (offCell k₀ v).property
  rw [signalOf, dif_pos hk, toPNat_coe (offCell k₀ v) hk]

/-- One-step unfolding of the sweep history: prepend the new signal. -/
lemma history_sweepK_succ (K : ℕ+) (k₀ : ℤ) (t : ℕ) :
    history c (sweepK K) k₀ (t + 1) =
      signalOf c (position c (sweepK K) k₀ (t + 1)) (t + 1) :: history c (sweepK K) k₀ t := by
  have hlen : (history c (sweepK K) k₀ t).length = t := history_length_sweepK K k₀ t
  have hmove : sweepK K (history c (sweepK K) k₀ t) = .move (triDir K t) := by
    simp only [sweepK, hlen]
  rw [history_succ_of_move hmove]
  congr 1
  rw [position_succ_of_move hmove]

/-! ### The parametric upswing detector and its threshold -/

/-- Scan a most-recent-first signal list (whose head has time `t`) for the *oldest* "Yes"
    at a time `≡ v (mod 2K)` (an *upswing* occurrence of displacement `v`). -/
def lastUpYesFrom (v K : ℕ) : List Bool → ℕ → Option ℕ
  | [], _ => none
  | (b :: bs), t =>
      match lastUpYesFrom v K bs (t - 1) with
      | some s => some s
      | none => if t % (2 * K) = v ∧ b then some t else none

/-- The first (earliest) time `≡ v (mod 2K)` with a "Yes" signal in history `h`. -/
def firstUpYes (v K : ℕ) (h : List Bool) : Option ℕ := lastUpYesFrom v K h h.length

/-- **Cons-recurrence for the upswing detector.** -/
lemma firstUpYes_cons (v K : ℕ) (b : Bool) (bs : List Bool) :
    firstUpYes v K (b :: bs) =
      match firstUpYes v K bs with
      | some s => some s
      | none =>
          if (b :: bs).length % (2 * K) = v ∧ b then some ((b :: bs).length) else none := by
  show lastUpYesFrom v K (b :: bs) (bs.length + 1) = _
  simp only [lastUpYesFrom, Nat.add_sub_cancel, firstUpYes, List.length_cons]

/-- The first time `≡ v (mod 2K)` strictly greater than `val` (and `≥ 1`):
    `2K · ⌈(val + 2K − v)/2K⌉ + v`. -/
def upThr (v K val : ℕ) : ℕ := 2 * K * ((val + (2 * K - v)) / (2 * K)) + v

lemma upThr_mod {v K val : ℕ} (hK : 0 < K) (hv : v ≤ K) :
    upThr v K val % (2 * K) = v := by
  unfold upThr
  rw [Nat.mul_add_mod]  -- (2K * q + v) % (2K) = v % (2K)
  exact Nat.mod_eq_of_lt (by omega)

lemma upThr_gt {v K val : ℕ} (hK : 0 < K) (hv : v ≤ K) : val < upThr v K val := by
  unfold upThr
  have hP : 0 < 2 * K := by omega
  -- Let q = (val + (2K - v)) / 2K, ρ = (val + (2K - v)) % 2K. Then val + (2K - v) = 2K·q + ρ
  -- with ρ < 2K. Goal: val < 2K·q + v, i.e. (2K - v) > ρ - ... handled by omega.
  have hq := Nat.div_add_mod (val + (2 * K - v)) (2 * K)
  have hr : (val + (2 * K - v)) % (2 * K) < 2 * K := Nat.mod_lt _ hP
  generalize hQ : 2 * K * ((val + (2 * K - v)) / (2 * K)) = Q at hq ⊢
  omega

lemma upThr_minimal {v K val s : ℕ} (hK : 0 < K) (hv : v ≤ K)
    (hs : s % (2 * K) = v) (hvs : val < s) : upThr v K val ≤ s := by
  unfold upThr
  have hP : 0 < 2 * K := by omega
  -- Write s = 2K·qs + v.
  have hsdiv := Nat.div_add_mod s (2 * K)
  rw [hs] at hsdiv
  set qs := s / (2 * K) with hqs
  -- From s > val: 2K·qs + v > val, so val + (2K - v) < 2K·(qs + 1).
  have hbound : val + (2 * K - v) < 2 * K * (qs + 1) := by
    have : 2 * K * qs + v = s := hsdiv
    have hmul : 2 * K * (qs + 1) = 2 * K * qs + 2 * K := by ring
    omega
  -- Hence threshold-quotient ≤ qs.
  have hqt : (val + (2 * K - v)) / (2 * K) ≤ qs := by
    rw [Nat.div_le_iff_le_mul_add_pred hP]
    omega
  have hmul : 2 * K * ((val + (2 * K - v)) / (2 * K)) ≤ 2 * K * qs :=
    Nat.mul_le_mul_left (2 * K) hqt
  generalize hA : 2 * K * ((val + (2 * K - v)) / (2 * K)) = A at hmul ⊢
  generalize hB : 2 * K * qs = B at hmul hsdiv
  omega

lemma upThr_pos {v K val : ℕ} (hK : 0 < K) (hv : v ≤ K) : 1 ≤ upThr v K val := by
  have := upThr_gt (v := v) (K := K) (val := val) hK hv
  omega

/-- **Upswing detector on the sweep trajectory.**  Along the period-`2K` sweep, the first
    "Yes" at a time `≡ v (mod 2K)` (`v ≤ K`) occurs exactly at `upThr v K (c (k₀+v))`. -/
lemma firstUpYes_sweepK (K : ℕ+) (v : ℕ) (hv : v ≤ K.val) (k₀ : ℕ+) (t : ℕ) :
    firstUpYes v K.val (history c (sweepK K) (k₀ : ℤ) t) =
      if upThr v K.val (c (offCell k₀ v)).val ≤ t then some (upThr v K.val (c (offCell k₀ v)).val)
      else none := by
  have hK : 0 < K.val := K.property
  set Tv := upThr v K.val (c (offCell k₀ v)).val with hTv
  induction t with
  | zero =>
      have : ¬ Tv ≤ 0 := by
        have := upThr_pos (v := v) (K := K.val) (val := (c (offCell k₀ v)).val) hK hv
        omega
      simp [firstUpYes, lastUpYesFrom, this]
  | succ n ih =>
      rw [history_sweepK_succ, firstUpYes_cons]
      have hlen : (history c (sweepK K) (k₀ : ℤ) n).length = n := history_length_sweepK K _ _
      rw [List.length_cons, hlen, ih]
      by_cases hTn : Tv ≤ n
      · simp only [hTn, if_true]
        have : Tv ≤ n + 1 := by omega
        simp [this]
      · rw [if_neg hTn]
        by_cases hpar : (n + 1) % (2 * K.val) = v
        · have hsig : signalOf c (position c (sweepK K) (k₀ : ℤ) (n + 1)) (n + 1)
              = decide ((c (offCell k₀ v)).val < (n + 1)) :=
            signal_upswing_sweepK K k₀ (n + 1) v hpar hv
          rw [hsig]
          by_cases hyes : (c (offCell k₀ v)).val < (n + 1)
          · have hge : Tv ≤ n + 1 := upThr_minimal hK hv hpar hyes
            have heq : Tv = n + 1 := by omega
            have hcond : (n + 1) % (2 * K.val) = v ∧ decide ((c (offCell k₀ v)).val < (n + 1)) = true :=
              ⟨hpar, by simpa using hyes⟩
            rw [if_pos hcond, heq, if_pos (le_refl (n + 1))]
          · have hno : ¬ Tv ≤ n + 1 := by
              intro h
              have : (c (offCell k₀ v)).val < Tv := upThr_gt hK hv
              omega
            have hcond : ¬ ((n + 1) % (2 * K.val) = v ∧
                decide ((c (offCell k₀ v)).val < (n + 1)) = true) := by simp [hyes]
            rw [if_neg hcond, if_neg hno]
        · have hno : ¬ Tv ≤ n + 1 := by
            intro h
            have hTvmod : Tv % (2 * K.val) = v := upThr_mod hK hv
            -- Tv ≤ n+1, Tv > n (since ¬Tv≤n), so Tv = n+1, but (n+1)%2K ≠ v while Tv%2K = v.
            have heq : Tv = n + 1 := by omega
            rw [heq] at hTvmod
            exact hpar hTvmod
          have hcond : ¬ ((n + 1) % (2 * K.val) = v ∧
              (signalOf c (position c (sweepK K) (k₀ : ℤ) (n + 1)) (n + 1)) = true) := by
            rintro ⟨h1, -⟩; exact hpar h1
          rw [if_neg hcond, if_neg hno]

/-! ### The combined winning strategy and its hypothesis -/

/-- **Hypothesis (locally `K`-decodable).**  The per-displacement first-"Yes"-time tuple
    `v ↦ upThr v K (c (k₀+v))` (for `v ∈ {0,…,K}`) admits a left inverse `decode`.
    Equivalently, the labels `(c k₀, c (k₀+1), …, c (k₀+K))` (up to the threshold buckets)
    determine `k₀`. -/
def LocallyKDecodable (c : Perm) (K : ℕ+) : Prop :=
  ∃ decode : (ℕ → ℕ) → ℕ+, ∀ k₀ : ℕ+,
    decode (fun v => if v ≤ K.val then upThr v K.val (c (offCell k₀ v)).val else 0) = k₀

/-- The guess time: the latest of the `K+1` detector thresholds. -/
def TgK (c : Perm) (K : ℕ+) (k₀ : ℕ+) : ℕ :=
  (Finset.range (K.val + 1)).sup (fun v => upThr v K.val (c (offCell k₀ v)).val)

/-- Each detector threshold is `≤ TgK`. -/
lemma upThr_le_TgK (K : ℕ+) (k₀ : ℕ+) {v : ℕ} (hv : v ≤ K.val) :
    upThr v K.val (c (offCell k₀ v)).val ≤ TgK c K k₀ :=
  Finset.le_sup (f := fun v => upThr v K.val (c (offCell k₀ v)).val)
    (Finset.mem_range.mpr (by omega))

/-- "All `K+1` detectors have fired" — a decidable predicate on a history. -/
def allFired (K : ℕ+) (h : List Bool) : Prop :=
  ∀ v ∈ Finset.range (K.val + 1), (firstUpYes v K.val h).isSome = true

instance (K : ℕ+) (h : List Bool) : Decidable (allFired K h) := by
  unfold allFired; infer_instance

/-- **The winning strategy.**  Sweep while any of the `K+1` detectors is silent; once all
    have fired, decode `k₀` from the threshold tuple and guess the current position
    `k₀ + triK K t`. -/
def winStratK (K : ℕ+) (decode : (ℕ → ℕ) → ℕ+) : Strategy := fun h =>
  if allFired K h then
    Action.guess (offCell
      (decode (fun v => if v ≤ K.val then (firstUpYes v K.val h).getD 0 else 0))
      (triK K h.length))
  else
    Action.move (triDir K h.length)

/-- The strategy moves whenever a detector `v` is silent. -/
lemma winStratK_move_of_silent (K : ℕ+) (decode : (ℕ → ℕ) → ℕ+) (h : List Bool)
    {v : ℕ} (hv : v ≤ K.val) (hsil : firstUpYes v K.val h = none) :
    winStratK K decode h = Action.move (triDir K h.length) := by
  have hnot : ¬ allFired K h := by
    intro hall
    have := hall v (Finset.mem_range.mpr (by omega))
    rw [hsil] at this
    simp at this
  rw [winStratK, if_neg hnot]

/-- When all detectors have fired, the strategy guesses the decoded current position. -/
lemma winStratK_guess_of_allFired (K : ℕ+) (decode : (ℕ → ℕ) → ℕ+) (h : List Bool)
    (hall : allFired K h) :
    winStratK K decode h =
      Action.guess (offCell
        (decode (fun v => if v ≤ K.val then (firstUpYes v K.val h).getD 0 else 0))
        (triK K h.length)) := by
  rw [winStratK, if_pos hall]

/-- Before `TgK`, some detector `v` is still silent (its threshold exceeds `t`). -/
lemma exists_silent_before_TgK (K : ℕ+) (k₀ : ℕ+) (t : ℕ) (ht : t < TgK c K k₀) :
    ∃ v, v ≤ K.val ∧ firstUpYes v K.val (history c (sweepK K) (k₀ : ℤ) t) = none := by
  -- TgK is a Finset.sup attained at some v ∈ range (K+1); its threshold > t.
  have hne : (Finset.range (K.val + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨v, hvmem, hvsup⟩ := Finset.exists_mem_eq_sup _ hne
    (fun v => upThr v K.val (c (offCell k₀ v)).val)
  have hvle : v ≤ K.val := by have := Finset.mem_range.mp hvmem; omega
  refine ⟨v, hvle, ?_⟩
  rw [firstUpYes_sweepK K v hvle k₀ t, if_neg]
  show ¬ upThr v K.val (c (offCell k₀ v)).val ≤ t
  -- ht : t < TgK = sup; hvsup : sup = upThr v ...
  rw [TgK] at ht
  have hts : t < upThr v K.val (c (offCell k₀ v)).val := hvsup ▸ ht
  omega

/-! ### State match: winStratK tracks the sweep up to the guess time -/

/-- **State match.**  Up to the guess time `TgK`, `winStratK` produces exactly the sweep
    trajectory (at every earlier step at least one detector is silent, so it moves). -/
lemma winStratK_state_eq (K : ℕ+) (decode : (ℕ → ℕ) → ℕ+) (k₀ : ℕ+) :
    ∀ t : ℕ, t ≤ TgK c K k₀ →
      state c (winStratK K decode) (k₀ : ℤ) t = state c (sweepK K) (k₀ : ℤ) t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
      intro hle
      have ihn := ih (by omega)
      have hhist : history c (winStratK K decode) (k₀ : ℤ) n
          = history c (sweepK K) (k₀ : ℤ) n := by unfold history; rw [ihn]
      have hpos : position c (winStratK K decode) (k₀ : ℤ) n
          = position c (sweepK K) (k₀ : ℤ) n := by unfold position; rw [ihn]
      have hlen : (history c (sweepK K) (k₀ : ℤ) n).length = n := history_length_sweepK K _ _
      have hmove : winStratK K decode (history c (winStratK K decode) (k₀ : ℤ) n)
          = .move (triDir K n) := by
        rw [hhist]
        obtain ⟨v, hvle, hsil⟩ := exists_silent_before_TgK (c := c) K k₀ n (by omega)
        rw [winStratK_move_of_silent K decode _ hvle hsil, hlen]
      have hmove_sweep : sweepK K (history c (sweepK K) (k₀ : ℤ) n) = .move (triDir K n) := by
        simp only [sweepK, hlen]
      rw [state_succ, state_succ,
          step_move c (winStratK K decode) _ _ _ (triDir K n) hmove,
          step_move c (sweepK K) _ _ _ (triDir K n) hmove_sweep, hpos, hhist]

/-! ### The parametric `K` winning theorem -/

/-- **Parametric-`K` winning theorem.**  For every *locally `K`-decodable* permutation `c`,
    Bob has a winning strategy.  The strategy runs the period-`2K` sweep, reads off the
    `K+1` upswing thresholds `upThr v K (c (k₀+v))`, decodes `k₀`, and guesses its position —
    all while the trolley safely stays in `{k₀, …, k₀+K}`. -/
theorem LocallyKDecodable_BobWins (c : Perm) (K : ℕ+) (hdec : LocallyKDecodable c K) :
    BobWins c := by
  obtain ⟨decode, hdecode⟩ := hdec
  refine ⟨winStratK K decode, fun k₀ => ?_⟩
  set Tg := TgK c K k₀ with hTgdef
  refine ⟨Tg, ?_, ?_, ?_⟩
  · -- positions valid through Tg
    intro t ht
    have hst := winStratK_state_eq K decode k₀ t ht
    have hp : position c (winStratK K decode) (k₀ : ℤ) t = position c (sweepK K) (k₀ : ℤ) t := by
      unfold position; rw [hst]
    rw [hp]; exact position_sweepK_pos K k₀ t
  · -- no guess before Tg
    intro t ht g
    have hst := winStratK_state_eq K decode k₀ t (le_of_lt ht)
    have hhist : history c (winStratK K decode) (k₀ : ℤ) t = history c (sweepK K) (k₀ : ℤ) t := by
      unfold history; rw [hst]
    rw [hhist]
    obtain ⟨v, hvle, hsil⟩ := exists_silent_before_TgK K k₀ t ht
    rw [winStratK_move_of_silent K decode _ hvle hsil]; simp
  · -- correct guess at Tg
    have hst := winStratK_state_eq K decode k₀ Tg (le_refl Tg)
    have hhist : history c (winStratK K decode) (k₀ : ℤ) Tg
        = history c (sweepK K) (k₀ : ℤ) Tg := by unfold history; rw [hst]
    have hlen : (history c (sweepK K) (k₀ : ℤ) Tg).length = Tg := history_length_sweepK K _ _
    -- At Tg, every detector has fired (each threshold ≤ Tg) and returns its threshold.
    have hfired_v : ∀ v, v ≤ K.val →
        firstUpYes v K.val (history c (sweepK K) (k₀ : ℤ) Tg)
          = some (upThr v K.val (c (offCell k₀ v)).val) := by
      intro v hv
      rw [firstUpYes_sweepK K v hv k₀ Tg, if_pos (upThr_le_TgK K k₀ hv)]
    have hall : allFired K (history c (sweepK K) (k₀ : ℤ) Tg) := by
      intro v hvmem
      have hv : v ≤ K.val := by have := Finset.mem_range.mp hvmem; omega
      rw [hfired_v v hv]; rfl
    -- The (clamped) decode input matches the actual threshold tuple, so decode = k₀.
    have hdecinput :
        (fun v => if v ≤ K.val
            then (firstUpYes v K.val (history c (sweepK K) (k₀ : ℤ) Tg)).getD 0 else 0)
        = (fun v => if v ≤ K.val then upThr v K.val (c (offCell k₀ v)).val else 0) := by
      funext v
      by_cases hv : v ≤ K.val
      · rw [if_pos hv, if_pos hv, hfired_v v hv]; rfl
      · rw [if_neg hv, if_neg hv]
    have hk0 : decode (fun v => if v ≤ K.val then upThr v K.val (c (offCell k₀ v)).val else 0)
        = k₀ := hdecode k₀
    -- Assemble the guess.
    refine ⟨offCell (decode (fun v => if v ≤ K.val
        then (firstUpYes v K.val (history c (sweepK K) (k₀ : ℤ) Tg)).getD 0 else 0))
        (triK K Tg), ?_, ?_⟩
    · rw [hhist, winStratK_guess_of_allFired K decode _ hall, hlen]
    · have hp : position c (winStratK K decode) (k₀ : ℤ) Tg
          = position c (sweepK K) (k₀ : ℤ) Tg := by unfold position; rw [hst]
      rw [hp, position_sweepK, hdecinput, hk0]
      push_cast [offCell_val]; ring

/-- A convenient sufficient condition: if the clamped threshold-tuple map is injective, then
    `c` is locally `K`-decodable (via `Function.invFun`). -/
lemma locallyKDecodable_of_injective (c : Perm) (K : ℕ+)
    (hinj : Function.Injective
      (fun k₀ : ℕ+ => (fun v => if v ≤ K.val then upThr v K.val (c (offCell k₀ v)).val else 0))) :
    LocallyKDecodable c K := by
  classical
  refine ⟨fun f => Function.invFun
    (fun k₀ : ℕ+ => (fun v => if v ≤ K.val then upThr v K.val (c (offCell k₀ v)).val else 0)) f,
    fun k₀ => ?_⟩
  exact Function.leftInverse_invFun hinj k₀

-- Axiom audit: the parametric-K winning theorem depends only on the three standard classical
-- axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no custom axioms.
#print axioms LocallyKDecodable_BobWins

end TrolleyRetrieval
