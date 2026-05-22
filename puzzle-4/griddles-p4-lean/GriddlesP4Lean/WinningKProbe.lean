import GriddlesP4Lean.WinningRestricted

/-!
# Winning direction (K = 3 probe): a complete strategy under a 3-distinguishability hypothesis

`WinningRestricted.lean` proves a complete, `sorry`-free winning theorem for the *locally
2-distinguishable* class — permutations where `(c k₀, c (k₀+1))` determines `k₀`.  There Bob
oscillates `D_t ∈ {0,1}` and reads off two labels from the first even/odd "Yes".

Here we generalize the *probe width* to `K = 3`: Bob samples cells `k₀, k₀+1, k₀+2` and the
hypothesis is that `(c k₀, c (k₀+1), c (k₀+2))` determines `k₀`.  This strictly enlarges the
covered class (some permutations whose adjacent pair `(c k₀, c (k₀+1))` is ambiguous become
decodable once the third label is added).

## The strategy

* **Sweep.**  Instead of `R,L,R,L,…` (period 2, displacements `0,1`), Bob runs the period-4
  triangle wave `R,R,L,L,R,R,L,L,…`.  Displacements cycle `0,1,2,1,0,1,2,1,…`.  Safety stays
  automatic: displacement `≥ 0`, so position `≥ k₀ ≥ 1`.

* **Per-displacement detectors.**  Displacement `0` is sampled at times `≡ 0 (mod 4)`,
  displacement `2` at times `≡ 2 (mod 4)`, and displacement `1` at *all odd* times (residues
  `1` and `3`).  So the j=1 detector is exactly `firstOddYes` from `WinningRestricted` (reused
  verbatim).  We add two new "mod-4" detectors for j=0 and j=2.

* **Decode + guess.**  Once all three detectors have fired (times `T0, T1, T2`), the
  hypothesis decodes `k₀`, and Bob guesses the current position `k₀ + tri₃(t)`.

This mirrors `WinningRestricted.lean` section-for-section.
-/

namespace TrolleyRetrieval

variable {c : Perm}

/-! ### Phase-1 sweep (period-4 triangle wave) -/

/-- Sweep direction at decision time `t`: right when `t % 4 < 2`, else left.  Produces the
    move sequence `R,R,L,L,R,R,L,L,…`. -/
def sweepDir (t : ℕ) : Dir := if t % 4 < 2 then .right else .left

/-- The triangle-wave displacement: `0,1,2,1` repeating with period `4`. -/
def tri₃ (m : ℕ) : ℕ := match m % 4 with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 1

/-- The pure sweep strategy (Phase 1 in isolation): always move, never guess. -/
def sweepStrat : Strategy := fun h => Action.move (sweepDir h.length)

/-- Under the sweep strategy (which never guesses), the history length equals the time. -/
lemma history_length_sweepStrat (k₀ : ℤ) :
    ∀ t : ℕ, (history c sweepStrat k₀ t).length = t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
      have hmove : sweepStrat (history c sweepStrat k₀ n) = .move (sweepDir n) := by
        simp only [sweepStrat, ih]
      rw [history_succ_of_move hmove, List.length_cons, ih]

/-- **Phase-1 position.**  Under the sweep, the position at time `t` is `k₀ + tri₃ t`. -/
lemma position_sweepStrat (k₀ : ℤ) :
    ∀ t : ℕ, position c sweepStrat k₀ t = k₀ + (tri₃ t : ℕ) := by
  intro t
  induction t with
  | zero => simp [position_zero, tri₃]
  | succ n ih =>
      have hlen : (history c sweepStrat k₀ n).length = n := history_length_sweepStrat k₀ n
      have hmove : sweepStrat (history c sweepStrat k₀ n) = .move (sweepDir n) := by
        simp only [sweepStrat, hlen]
      rw [position_succ_of_move hmove, ih]
      -- goal: k₀ + tri₃ n + (sweepDir n).delta = k₀ + tri₃ (n+1)
      have hkey : (tri₃ n : ℤ) + (sweepDir n).delta = (tri₃ (n + 1) : ℤ) := by
        unfold tri₃ sweepDir
        have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
        rcases h4 with h | h | h | h <;>
          · have hn1 : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
            rw [hn1, h]
            simp only [Dir.delta]
            norm_num
      linarith [hkey]

/-- Phase-1 safety: the sweep never falls off (position stays `≥ k₀ ≥ 1`). -/
lemma position_sweepStrat_pos (k₀ : ℕ+) (t : ℕ) :
    1 ≤ position c sweepStrat (k₀ : ℤ) t := by
  rw [position_sweepStrat]
  have hk : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.property
  have : (0 : ℤ) ≤ ((tri₃ t : ℕ) : ℤ) := by positivity
  linarith

/-- At times `≡ 0 (mod 4)`, the position is exactly `k₀` (displacement `0`). -/
lemma position_sweepStrat_mod4_0 (k₀ : ℕ+) (t : ℕ) (ht : t % 4 = 0) :
    position c sweepStrat (k₀ : ℤ) t = (k₀ : ℤ) := by
  rw [position_sweepStrat]
  have : tri₃ t = 0 := by unfold tri₃; rw [ht]
  rw [this]; simp

/-- At times `≡ 2 (mod 4)`, the position is exactly `k₀ + 2` (displacement `2`). -/
lemma position_sweepStrat_mod4_2 (k₀ : ℕ+) (t : ℕ) (ht : t % 4 = 2) :
    position c sweepStrat (k₀ : ℤ) t = ((k₀ + 2 : ℕ+) : ℤ) := by
  rw [position_sweepStrat]
  have htri : tri₃ t = 2 := by unfold tri₃; rw [ht]
  rw [htri]; push_cast; ring

/-- At odd times, the position is exactly `k₀ + 1` (displacement `1`). -/
lemma position_sweepStrat_odd (k₀ : ℕ+) (t : ℕ) (ht : t % 2 = 1) :
    position c sweepStrat (k₀ : ℤ) t = ((k₀ + 1 : ℕ+) : ℤ) := by
  rw [position_sweepStrat]
  have htri : tri₃ t = 1 := by
    unfold tri₃
    have : t % 4 = 1 ∨ t % 4 = 3 := by omega
    rcases this with h | h <;> rw [h]
  rw [htri]; push_cast; ring

/-- **Signal at times `≡ 0 (mod 4)`.**  Probes the start cell: `c(k₀) < t`. -/
lemma signal_mod4_0_sweepStrat (k₀ : ℕ+) (t : ℕ) (ht : t % 4 = 0) :
    signalOf c (position c sweepStrat (k₀ : ℤ) t) t = decide ((c k₀).val < t) := by
  rw [position_sweepStrat_mod4_0 k₀ t ht]
  have hk : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.property
  rw [signalOf, dif_pos hk, toPNat_coe k₀ hk]

/-- **Signal at times `≡ 2 (mod 4)`.**  Probes `c(k₀+2) < t`. -/
lemma signal_mod4_2_sweepStrat (k₀ : ℕ+) (t : ℕ) (ht : t % 4 = 2) :
    signalOf c (position c sweepStrat (k₀ : ℤ) t) t = decide ((c (k₀ + 2)).val < t) := by
  rw [position_sweepStrat_mod4_2 k₀ t ht]
  have hk : (1 : ℤ) ≤ ((k₀ + 2 : ℕ+) : ℤ) := by exact_mod_cast (k₀ + 2).property
  rw [signalOf, dif_pos hk, toPNat_coe (k₀ + 2) hk]

/-- **Signal at odd times.**  Probes `c(k₀+1) < t`. -/
lemma signal_odd_sweepStrat (k₀ : ℕ+) (t : ℕ) (ht : t % 2 = 1) :
    signalOf c (position c sweepStrat (k₀ : ℤ) t) t = decide ((c (k₀ + 1)).val < t) := by
  rw [position_sweepStrat_odd k₀ t ht]
  have hk : (1 : ℤ) ≤ ((k₀ + 1 : ℕ+) : ℤ) := by exact_mod_cast (k₀ + 1).property
  rw [signalOf, dif_pos hk, toPNat_coe (k₀ + 1) hk]

/-- One-step unfolding of the sweep history: prepend the new signal. -/
lemma history_sweepStrat_succ (k₀ : ℤ) (t : ℕ) :
    history c sweepStrat k₀ (t + 1) =
      signalOf c (position c sweepStrat k₀ (t + 1)) (t + 1) :: history c sweepStrat k₀ t := by
  have hlen : (history c sweepStrat k₀ t).length = t := history_length_sweepStrat k₀ t
  have hmove : sweepStrat (history c sweepStrat k₀ t) = .move (sweepDir t) := by
    simp only [sweepStrat, hlen]
  rw [history_succ_of_move hmove]
  congr 1
  rw [position_succ_of_move hmove]

/-! ### Mod-4 detectors and their thresholds

We need detectors for the first "Yes" at times `≡ 0 (mod 4)` (probing `c k₀`) and `≡ 2
(mod 4)` (probing `c (k₀+2)`).  These mirror `lastEvenYesFrom`/`firstEvenYes` but with the
even-parity test `t % 2 = 0` replaced by `t % 4 = 0` resp. `t % 4 = 2`.  The j=1 detector
(odd times) is reused verbatim from `WinningRestricted` (`firstOddYes`). -/

/-- Scan a most-recent-first signal list (whose head has time `t`) for the *oldest*
    "Yes" at a time `≡ 0 (mod 4)`. -/
def lastMod4_0YesFrom : List Bool → ℕ → Option ℕ
  | [], _ => none
  | (b :: bs), t =>
      match lastMod4_0YesFrom bs (t - 1) with
      | some s => some s
      | none => if t % 4 = 0 ∧ b then some t else none

/-- The first (earliest) time `≡ 0 (mod 4)` with a "Yes" signal in history `h`. -/
def firstMod4_0Yes (h : List Bool) : Option ℕ := lastMod4_0YesFrom h h.length

/-- Scan for the *oldest* "Yes" at a time `≡ 2 (mod 4)`. -/
def lastMod4_2YesFrom : List Bool → ℕ → Option ℕ
  | [], _ => none
  | (b :: bs), t =>
      match lastMod4_2YesFrom bs (t - 1) with
      | some s => some s
      | none => if t % 4 = 2 ∧ b then some t else none

/-- The first (earliest) time `≡ 2 (mod 4)` with a "Yes" signal in history `h`. -/
def firstMod4_2Yes (h : List Bool) : Option ℕ := lastMod4_2YesFrom h h.length

/-- **Cons-recurrence for the mod-4-0 detector.** -/
lemma firstMod4_0Yes_cons (b : Bool) (bs : List Bool) :
    firstMod4_0Yes (b :: bs) =
      match firstMod4_0Yes bs with
      | some s => some s
      | none =>
          if (b :: bs).length % 4 = 0 ∧ b then some ((b :: bs).length) else none := by
  show lastMod4_0YesFrom (b :: bs) (bs.length + 1) = _
  simp only [lastMod4_0YesFrom, Nat.add_sub_cancel, firstMod4_0Yes, List.length_cons]

/-- **Cons-recurrence for the mod-4-2 detector.** -/
lemma firstMod4_2Yes_cons (b : Bool) (bs : List Bool) :
    firstMod4_2Yes (b :: bs) =
      match firstMod4_2Yes bs with
      | some s => some s
      | none =>
          if (b :: bs).length % 4 = 2 ∧ b then some ((b :: bs).length) else none := by
  show lastMod4_2YesFrom (b :: bs) (bs.length + 1) = _
  simp only [lastMod4_2YesFrom, Nat.add_sub_cancel, firstMod4_2Yes, List.length_cons]

/-- The smallest `m ≡ 0 (mod 4)` strictly greater than `v`. -/
def mod4_0Thr (v : ℕ) : ℕ := 4 * (v / 4) + 4

/-- The smallest `m ≡ 2 (mod 4)` strictly greater than `v`. -/
def mod4_2Thr (v : ℕ) : ℕ := 4 * ((v + 2) / 4) + 2

lemma mod4_0Thr_mod (v : ℕ) : mod4_0Thr v % 4 = 0 := by unfold mod4_0Thr; omega
lemma mod4_0Thr_gt (v : ℕ) : v < mod4_0Thr v := by unfold mod4_0Thr; omega
lemma mod4_0Thr_minimal (v s : ℕ) (hs : s % 4 = 0) (hvs : v < s) : mod4_0Thr v ≤ s := by
  unfold mod4_0Thr; omega

lemma mod4_2Thr_mod (v : ℕ) : mod4_2Thr v % 4 = 2 := by unfold mod4_2Thr; omega
lemma mod4_2Thr_gt (v : ℕ) : v < mod4_2Thr v := by unfold mod4_2Thr; omega
lemma mod4_2Thr_minimal (v s : ℕ) (hs : s % 4 = 2) (hvs : v < s) : mod4_2Thr v ≤ s := by
  unfold mod4_2Thr; omega

/-- **Mod-4-0 detector on the trajectory.**  Along the sweep, the first "Yes" at a time
    `≡ 0 (mod 4)` occurs exactly at `T0 = mod4_0Thr (c k₀)`. -/
lemma firstMod4_0Yes_sweepStrat (k₀ : ℕ+) (t : ℕ) :
    firstMod4_0Yes (history c sweepStrat (k₀ : ℤ) t) =
      if mod4_0Thr (c k₀).val ≤ t then some (mod4_0Thr (c k₀).val) else none := by
  set T0 := mod4_0Thr (c k₀).val with hT0
  induction t with
  | zero =>
      have : ¬ T0 ≤ 0 := by have := mod4_0Thr_gt (c k₀).val; omega
      simp [firstMod4_0Yes, lastMod4_0YesFrom, this]
  | succ n ih =>
      rw [history_sweepStrat_succ, firstMod4_0Yes_cons]
      have hlen : (history c sweepStrat (k₀ : ℤ) n).length = n := history_length_sweepStrat _ _
      rw [List.length_cons, hlen, ih]
      by_cases hTn : T0 ≤ n
      · simp only [hTn, if_true]
        have : T0 ≤ n + 1 := by omega
        simp [this]
      · rw [if_neg hTn]
        by_cases hpar : (n + 1) % 4 = 0
        · have hsig : signalOf c (position c sweepStrat (k₀ : ℤ) (n + 1)) (n + 1)
              = decide ((c k₀).val < (n + 1)) := signal_mod4_0_sweepStrat k₀ (n + 1) hpar
          rw [hsig]
          by_cases hyes : (c k₀).val < (n + 1)
          · have hge : T0 ≤ n + 1 := mod4_0Thr_minimal _ _ hpar hyes
            have heq : T0 = n + 1 := by omega
            have hcond : (n + 1) % 4 = 0 ∧ decide ((c k₀).val < (n + 1)) = true :=
              ⟨hpar, by simpa using hyes⟩
            rw [if_pos hcond, heq, if_pos (le_refl (n + 1))]
          · have hno : ¬ T0 ≤ n + 1 := by
              intro h
              have : (c k₀).val < T0 := mod4_0Thr_gt _
              omega
            have hcond : ¬ ((n + 1) % 4 = 0 ∧ decide ((c k₀).val < (n + 1)) = true) := by
              simp [hyes]
            rw [if_neg hcond, if_neg hno]
        · have hno : ¬ T0 ≤ n + 1 := by
            intro h
            have hT0mod : T0 % 4 = 0 := mod4_0Thr_mod _
            omega
          have hcond : ¬ ((n + 1) % 4 = 0 ∧
              (signalOf c (position c sweepStrat (k₀ : ℤ) (n + 1)) (n + 1)) = true) := by
            rintro ⟨h1, -⟩; exact hpar h1
          rw [if_neg hcond, if_neg hno]

/-- **Mod-4-2 detector on the trajectory.**  The first "Yes" at a time `≡ 2 (mod 4)` occurs
    at `T2 = mod4_2Thr (c (k₀+2))`. -/
lemma firstMod4_2Yes_sweepStrat (k₀ : ℕ+) (t : ℕ) :
    firstMod4_2Yes (history c sweepStrat (k₀ : ℤ) t) =
      if mod4_2Thr (c (k₀ + 2)).val ≤ t then some (mod4_2Thr (c (k₀ + 2)).val) else none := by
  set T2 := mod4_2Thr (c (k₀ + 2)).val with hT2
  induction t with
  | zero =>
      have : ¬ T2 ≤ 0 := by have := mod4_2Thr_gt (c (k₀ + 2)).val; omega
      simp [firstMod4_2Yes, lastMod4_2YesFrom, this]
  | succ n ih =>
      rw [history_sweepStrat_succ, firstMod4_2Yes_cons]
      have hlen : (history c sweepStrat (k₀ : ℤ) n).length = n := history_length_sweepStrat _ _
      rw [List.length_cons, hlen, ih]
      by_cases hTn : T2 ≤ n
      · simp only [hTn, if_true]
        have : T2 ≤ n + 1 := by omega
        simp [this]
      · rw [if_neg hTn]
        by_cases hpar : (n + 1) % 4 = 2
        · have hsig : signalOf c (position c sweepStrat (k₀ : ℤ) (n + 1)) (n + 1)
              = decide ((c (k₀ + 2)).val < (n + 1)) := signal_mod4_2_sweepStrat k₀ (n + 1) hpar
          rw [hsig]
          by_cases hyes : (c (k₀ + 2)).val < (n + 1)
          · have hge : T2 ≤ n + 1 := mod4_2Thr_minimal _ _ hpar hyes
            have heq : T2 = n + 1 := by omega
            have hcond : (n + 1) % 4 = 2 ∧ decide ((c (k₀ + 2)).val < (n + 1)) = true :=
              ⟨hpar, by simpa using hyes⟩
            rw [if_pos hcond, heq, if_pos (le_refl (n + 1))]
          · have hno : ¬ T2 ≤ n + 1 := by
              intro h
              have : (c (k₀ + 2)).val < T2 := mod4_2Thr_gt _
              omega
            have hcond : ¬ ((n + 1) % 4 = 2 ∧ decide ((c (k₀ + 2)).val < (n + 1)) = true) := by
              simp [hyes]
            rw [if_neg hcond, if_neg hno]
        · have hno : ¬ T2 ≤ n + 1 := by
            intro h
            have hT2mod : T2 % 4 = 2 := mod4_2Thr_mod _
            omega
          have hcond : ¬ ((n + 1) % 4 = 2 ∧
              (signalOf c (position c sweepStrat (k₀ : ℤ) (n + 1)) (n + 1)) = true) := by
            rintro ⟨h1, -⟩; exact hpar h1
          rw [if_neg hcond, if_neg hno]

/-! ### The j=1 (odd) detector along the SWEEP trajectory

`firstOddYes` (and its cons-recurrence) is reused from `WinningRestricted`.  But the
trajectory lemma `firstOddYes_oscStrat` was proven for `oscStrat`; we re-prove the analog for
`sweepStrat` (the odd-time signal is the same `c (k₀+1) < t` because at odd times the sweep
displacement is `1`, exactly as in the oscillation). -/

/-- **Odd detector on the sweep trajectory.**  The first odd-time "Yes" occurs at
    `T1 = oddThr (c (k₀ + 1))`. -/
lemma firstOddYes_sweepStrat (k₀ : ℕ+) (t : ℕ) :
    firstOddYes (history c sweepStrat (k₀ : ℤ) t) =
      if oddThr (c (k₀ + 1)).val ≤ t then some (oddThr (c (k₀ + 1)).val) else none := by
  set T1 := oddThr (c (k₀ + 1)).val with hT1
  induction t with
  | zero =>
      have : ¬ T1 ≤ 0 := by have := oddThr_gt (c (k₀ + 1)).val; omega
      simp [firstOddYes, lastOddYesFrom, this]
  | succ n ih =>
      rw [history_sweepStrat_succ, firstOddYes_cons]
      have hlen : (history c sweepStrat (k₀ : ℤ) n).length = n := history_length_sweepStrat _ _
      rw [List.length_cons, hlen, ih]
      by_cases hTn : T1 ≤ n
      · simp only [hTn, if_true]
        have : T1 ≤ n + 1 := by omega
        simp [this]
      · rw [if_neg hTn]
        by_cases hpar : (n + 1) % 2 = 1
        · have hsig : signalOf c (position c sweepStrat (k₀ : ℤ) (n + 1)) (n + 1)
              = decide ((c (k₀ + 1)).val < (n + 1)) := signal_odd_sweepStrat k₀ (n + 1) hpar
          rw [hsig]
          by_cases hyes : (c (k₀ + 1)).val < (n + 1)
          · have hge : T1 ≤ n + 1 := oddThr_minimal _ _ hpar hyes
            have heq : T1 = n + 1 := by omega
            have hcond : (n + 1) % 2 = 1 ∧ decide ((c (k₀ + 1)).val < (n + 1)) = true :=
              ⟨hpar, by simpa using hyes⟩
            rw [if_pos hcond, heq, if_pos (le_refl (n + 1))]
          · have hno : ¬ T1 ≤ n + 1 := by
              intro h
              have : (c (k₀ + 1)).val < T1 := oddThr_gt _
              omega
            have hcond : ¬ ((n + 1) % 2 = 1 ∧ decide ((c (k₀ + 1)).val < (n + 1)) = true) := by
              simp [hyes]
            rw [if_neg hcond, if_neg hno]
        · have hno : ¬ T1 ≤ n + 1 := by
            intro h
            have hodd : T1 % 2 = 1 := oddThr_odd _
            omega
          have hcond : ¬ ((n + 1) % 2 = 1 ∧
              (signalOf c (position c sweepStrat (k₀ : ℤ) (n + 1)) (n + 1)) = true) := by
            rintro ⟨h1, -⟩; exact hpar h1
          rw [if_neg hcond, if_neg hno]

/-! ### The combined winning strategy and its hypothesis -/

/-- **Hypothesis (locally 3-decodable).**  The map
    `k₀ ↦ (mod4_0Thr (c k₀), oddThr (c (k₀+1)), mod4_2Thr (c (k₀+2)))` — the first
    "Yes" times at displacements `0, 1, 2` — admits a left inverse `decode`.  Equivalently,
    the triple of labels `(c k₀, c (k₀+1), c (k₀+2))` (up to the threshold buckets)
    determines `k₀`. -/
def LocallyK3Decodable (c : Perm) : Prop :=
  ∃ decode : ℕ → ℕ → ℕ → ℕ+, ∀ k₀ : ℕ+,
    decode (mod4_0Thr (c k₀).val) (oddThr (c (k₀ + 1)).val) (mod4_2Thr (c (k₀ + 2)).val) = k₀

/-- A convenient sufficient condition: if the threshold triple map is injective, then `c` is
    locally 3-decodable (via `Function.invFun`). -/
lemma locallyK3Decodable_of_injective
    (hinj : Function.Injective
      (fun k₀ : ℕ+ => (mod4_0Thr (c k₀).val, oddThr (c (k₀ + 1)).val,
                       mod4_2Thr (c (k₀ + 2)).val))) :
    LocallyK3Decodable c := by
  classical
  set f : ℕ+ → ℕ × ℕ × ℕ :=
    fun k₀ => (mod4_0Thr (c k₀).val, oddThr (c (k₀ + 1)).val, mod4_2Thr (c (k₀ + 2)).val)
    with hf
  refine ⟨fun T0 T1 T2 => Function.invFun f (T0, T1, T2), fun k₀ => ?_⟩
  have := Function.leftInverse_invFun hinj k₀
  simpa [hf] using this

/-- **The winning strategy.**  Sweep while any detector is silent; once all three (j=0,1,2)
    "Yes" times `T0, T1, T2` are known, decode `k₀` and guess the current position
    `k₀ + tri₃ t`. -/
def winStrat₃ (decode : ℕ → ℕ → ℕ → ℕ+) : Strategy := fun h =>
  match firstMod4_0Yes h with
  | none => Action.move (sweepDir h.length)
  | some T0 =>
    match firstOddYes h with
    | none => Action.move (sweepDir h.length)
    | some T1 =>
      match firstMod4_2Yes h with
      | none => Action.move (sweepDir h.length)
      | some T2 =>
          Action.guess (let k := decode T0 T1 T2;
            match h.length % 4 with
            | 0 => k
            | 1 => k + 1
            | 2 => k + 2
            | _ => k + 1)

lemma winStrat₃_move_of_mod4_0_none (decode : ℕ → ℕ → ℕ → ℕ+) (h : List Bool)
    (h0 : firstMod4_0Yes h = none) :
    winStrat₃ decode h = Action.move (sweepDir h.length) := by
  simp only [winStrat₃, h0]

lemma winStrat₃_move_of_odd_none (decode : ℕ → ℕ → ℕ → ℕ+) (h : List Bool)
    (h1 : firstOddYes h = none) :
    winStrat₃ decode h = Action.move (sweepDir h.length) := by
  simp only [winStrat₃, h1]
  cases firstMod4_0Yes h <;> rfl

lemma winStrat₃_move_of_mod4_2_none (decode : ℕ → ℕ → ℕ → ℕ+) (h : List Bool)
    (h2 : firstMod4_2Yes h = none) :
    winStrat₃ decode h = Action.move (sweepDir h.length) := by
  simp only [winStrat₃, h2]
  cases firstMod4_0Yes h <;> [rfl; cases firstOddYes h <;> rfl]

lemma winStrat₃_guess_of_all (decode : ℕ → ℕ → ℕ → ℕ+) (h : List Bool) {T0 T1 T2 : ℕ}
    (h0 : firstMod4_0Yes h = some T0) (h1 : firstOddYes h = some T1)
    (h2 : firstMod4_2Yes h = some T2) :
    winStrat₃ decode h =
      Action.guess (let k := decode T0 T1 T2;
        match h.length % 4 with
        | 0 => k | 1 => k + 1 | 2 => k + 2 | _ => k + 1) := by
  simp only [winStrat₃, h0, h1, h2]

/-! ### State match: winStrat₃ tracks the sweep up to the guess time -/

/-- The guess time is the latest of the three detector thresholds. -/
private lemma silent_before_Tg (k₀ : ℕ+) (n : ℕ)
    (hn : n < max (max (mod4_0Thr (c k₀).val) (oddThr (c (k₀ + 1)).val))
            (mod4_2Thr (c (k₀ + 2)).val)) :
    firstMod4_0Yes (history c sweepStrat (k₀ : ℤ) n) = none ∨
    firstOddYes (history c sweepStrat (k₀ : ℤ) n) = none ∨
    firstMod4_2Yes (history c sweepStrat (k₀ : ℤ) n) = none := by
  by_cases hT0 : mod4_0Thr (c k₀).val ≤ n
  · by_cases hT1 : oddThr (c (k₀ + 1)).val ≤ n
    · -- then T2 > n
      have hT2 : ¬ mod4_2Thr (c (k₀ + 2)).val ≤ n := by omega
      right; right
      rw [firstMod4_2Yes_sweepStrat, if_neg hT2]
    · right; left
      rw [firstOddYes_sweepStrat, if_neg hT1]
  · left
    rw [firstMod4_0Yes_sweepStrat, if_neg hT0]

/-- **State match.**  Up to the guess time `Tg = max (max T0 T1) T2`, `winStrat₃` produces
    exactly the sweep trajectory. -/
lemma winStrat₃_state_eq (decode : ℕ → ℕ → ℕ → ℕ+) (k₀ : ℕ+) :
    ∀ t : ℕ, t ≤ max (max (mod4_0Thr (c k₀).val) (oddThr (c (k₀ + 1)).val))
                  (mod4_2Thr (c (k₀ + 2)).val) →
      state c (winStrat₃ decode) (k₀ : ℤ) t = state c sweepStrat (k₀ : ℤ) t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
      intro hle
      have ihn := ih (by omega)
      have hhist : history c (winStrat₃ decode) (k₀ : ℤ) n
          = history c sweepStrat (k₀ : ℤ) n := by unfold history; rw [ihn]
      have hpos : position c (winStrat₃ decode) (k₀ : ℤ) n
          = position c sweepStrat (k₀ : ℤ) n := by unfold position; rw [ihn]
      have hlen : (history c sweepStrat (k₀ : ℤ) n).length = n := history_length_sweepStrat _ _
      have hmove : winStrat₃ decode (history c (winStrat₃ decode) (k₀ : ℤ) n)
          = .move (sweepDir n) := by
        rw [hhist]
        rcases silent_before_Tg (c := c) k₀ n (by omega) with h0 | h1 | h2
        · rw [winStrat₃_move_of_mod4_0_none _ _ h0, hlen]
        · rw [winStrat₃_move_of_odd_none _ _ h1, hlen]
        · rw [winStrat₃_move_of_mod4_2_none _ _ h2, hlen]
      have hmove_sweep : sweepStrat (history c sweepStrat (k₀ : ℤ) n) = .move (sweepDir n) := by
        simp only [sweepStrat, hlen]
      rw [state_succ, state_succ,
          step_move c (winStrat₃ decode) _ _ _ (sweepDir n) hmove,
          step_move c sweepStrat _ _ _ (sweepDir n) hmove_sweep, hpos, hhist]

/-! ### The K=3 winning theorem -/

/-- **K=3 winning theorem.**  For every *locally 3-decodable* permutation `c`, Bob has a
    winning strategy.  The strategy runs the period-4 sweep, reads off `c k₀`, `c (k₀+1)`,
    `c (k₀+2)` from the first "Yes" at displacements `0, 1, 2`, decodes `k₀`, and guesses its
    position — all while the trolley safely stays in `{k₀, k₀+1, k₀+2}`. -/
theorem LocallyK3Decodable_BobWins (c : Perm) (hdec : LocallyK3Decodable c) : BobWins c := by
  obtain ⟨decode, hdecode⟩ := hdec
  refine ⟨winStrat₃ decode, fun k₀ => ?_⟩
  set T0 := mod4_0Thr (c k₀).val with hT0def
  set T1 := oddThr (c (k₀ + 1)).val with hT1def
  set T2 := mod4_2Thr (c (k₀ + 2)).val with hT2def
  set Tg := max (max T0 T1) T2 with hTgdef
  have hT0le : T0 ≤ Tg := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT1le : T1 ≤ Tg := le_trans (le_max_right _ _) (le_max_left _ _)
  have hT2le : T2 ≤ Tg := le_max_right _ _
  refine ⟨Tg, ?_, ?_, ?_⟩
  · -- positions valid through Tg
    intro t ht
    have hst := winStrat₃_state_eq decode k₀ t ht
    have hp : position c (winStrat₃ decode) (k₀ : ℤ) t = position c sweepStrat (k₀ : ℤ) t := by
      unfold position; rw [hst]
    rw [hp]; exact position_sweepStrat_pos k₀ t
  · -- no guess before Tg
    intro t ht g
    have hst := winStrat₃_state_eq decode k₀ t (le_of_lt ht)
    have hhist : history c (winStrat₃ decode) (k₀ : ℤ) t = history c sweepStrat (k₀ : ℤ) t := by
      unfold history; rw [hst]
    rw [hhist]
    rcases silent_before_Tg (c := c) k₀ t (by omega) with h0 | h1 | h2
    · rw [winStrat₃_move_of_mod4_0_none _ _ h0]; simp
    · rw [winStrat₃_move_of_odd_none _ _ h1]; simp
    · rw [winStrat₃_move_of_mod4_2_none _ _ h2]; simp
  · -- correct guess at Tg
    have hst := winStrat₃_state_eq decode k₀ Tg (le_refl Tg)
    have hhist : history c (winStrat₃ decode) (k₀ : ℤ) Tg = history c sweepStrat (k₀ : ℤ) Tg := by
      unfold history; rw [hst]
    have hlen : (history c sweepStrat (k₀ : ℤ) Tg).length = Tg := history_length_sweepStrat _ _
    have h0 : firstMod4_0Yes (history c sweepStrat (k₀ : ℤ) Tg) = some T0 := by
      rw [firstMod4_0Yes_sweepStrat, if_pos hT0le]
    have h1 : firstOddYes (history c sweepStrat (k₀ : ℤ) Tg) = some T1 := by
      rw [firstOddYes_sweepStrat, if_pos hT1le]
    have h2 : firstMod4_2Yes (history c sweepStrat (k₀ : ℤ) Tg) = some T2 := by
      rw [firstMod4_2Yes_sweepStrat, if_pos hT2le]
    have hk0 : decode T0 T1 T2 = k₀ := hdecode k₀
    refine ⟨(let k := decode T0 T1 T2;
        match Tg % 4 with | 0 => k | 1 => k + 1 | 2 => k + 2 | _ => k + 1), ?_, ?_⟩
    · rw [hhist, winStrat₃_guess_of_all decode _ h0 h1 h2, hlen]
    · have hp : position c (winStrat₃ decode) (k₀ : ℤ) Tg
          = position c sweepStrat (k₀ : ℤ) Tg := by unfold position; rw [hst]
      rw [hp, position_sweepStrat]
      simp only [hk0]
      -- goal: (match Tg%4 ...).val (as ℤ) = k₀ + tri₃ Tg
      have hr : Tg % 4 = 0 ∨ Tg % 4 = 1 ∨ Tg % 4 = 2 ∨ Tg % 4 = 3 := by omega
      rcases hr with h | h | h | h <;>
        · simp only [h, tri₃]
          push_cast
          ring

/-! ### Concrete instance: the block 3-cycle (a permutation that genuinely needs K = 3)

`c` cyclically rotates each block `{3b+1, 3b+2, 3b+3}` forwards:
`3b+1 ↦ 3b+2 ↦ 3b+3 ↦ 3b+1`.  Equivalently `c m = m+1` unless `m ≡ 0 (mod 3)`, in which
case `c m = m−2`.  This is not eventually identity.  Its adjacent pair `(c k₀, c (k₀+1))`
is *not* always enough to recover `k₀` (some pairs collide under the 2-probe), but the full
triple `(c k₀, c (k₀+1), c (k₀+2))` is — so it lies in the K=3 class but illustrates the
extra reach over the 2-probe of `WinningRestricted`. -/

/-- Block 3-cycle map: `m ↦ m+1` if `m % 3 ≠ 0`, else `m−2`. -/
def blkF (n : ℕ+) : ℕ+ :=
  ⟨if n.val % 3 = 0 then n.val - 2 else n.val + 1, by
    obtain ⟨v, hv⟩ := n
    show 0 < if v % 3 = 0 then v - 2 else v + 1
    split_ifs with h <;> omega⟩

lemma blkF_val (n : ℕ+) : (blkF n).val = if n.val % 3 = 0 then n.val - 2 else n.val + 1 := rfl

/-- The inverse rotation: `m ↦ m−1` if `m % 3 ≠ 1`, else `m+2`. -/
def blkG (n : ℕ+) : ℕ+ :=
  ⟨if n.val % 3 = 1 then n.val + 2 else n.val - 1, by
    obtain ⟨v, hv⟩ := n
    show 0 < if v % 3 = 1 then v + 2 else v - 1
    split_ifs with h <;> omega⟩

lemma blkG_val (n : ℕ+) : (blkG n).val = if n.val % 3 = 1 then n.val + 2 else n.val - 1 := rfl

lemma blkF_blkG (n : ℕ+) : blkF (blkG n) = n := by
  have hn : 1 ≤ n.val := n.property
  apply Subtype.ext
  show (blkF (blkG n)).val = n.val
  rw [blkF_val]
  have hg : (blkG n).val = if n.val % 3 = 1 then n.val + 2 else n.val - 1 := blkG_val n
  rw [hg]; split_ifs <;> omega

lemma blkG_blkF (n : ℕ+) : blkG (blkF n) = n := by
  have hn : 1 ≤ n.val := n.property
  apply Subtype.ext
  show (blkG (blkF n)).val = n.val
  rw [blkG_val]
  have hf : (blkF n).val = if n.val % 3 = 0 then n.val - 2 else n.val + 1 := blkF_val n
  rw [hf]; split_ifs <;> omega

/-- The block 3-cycle as a permutation of `ℕ+`. -/
def blkPerm : Perm where
  toFun := blkF
  invFun := blkG
  left_inv := blkG_blkF
  right_inv := blkF_blkG

@[simp] lemma blkPerm_apply (n : ℕ+) : blkPerm n = blkF n := rfl

/-- The threshold triple of the block 3-cycle is injective in `k₀`, so `c` is locally
    3-decodable. -/
lemma blkPerm_locallyK3Decodable : LocallyK3Decodable blkPerm := by
  apply locallyK3Decodable_of_injective
  intro a b hab
  obtain ⟨va, hva⟩ := a
  obtain ⟨vb, hvb⟩ := b
  apply Subtype.ext
  show va = vb
  -- unfold the three threshold-coordinate equalities
  simp only [Prod.mk.injEq, blkPerm_apply, mod4_0Thr, oddThr, mod4_2Thr] at hab
  obtain ⟨e0, e1, e2⟩ := hab
  have ca : (blkF ⟨va, hva⟩).val = if va % 3 = 0 then va - 2 else va + 1 := blkF_val _
  have ca1 : (blkF (⟨va, hva⟩ + 1)).val
      = if (va + 1) % 3 = 0 then (va + 1) - 2 else (va + 1) + 1 := blkF_val _
  have ca2 : (blkF (⟨va, hva⟩ + 2)).val
      = if (va + 2) % 3 = 0 then (va + 2) - 2 else (va + 2) + 1 := blkF_val _
  have cb : (blkF ⟨vb, hvb⟩).val = if vb % 3 = 0 then vb - 2 else vb + 1 := blkF_val _
  have cb1 : (blkF (⟨vb, hvb⟩ + 1)).val
      = if (vb + 1) % 3 = 0 then (vb + 1) - 2 else (vb + 1) + 1 := blkF_val _
  have cb2 : (blkF (⟨vb, hvb⟩ + 2)).val
      = if (vb + 2) % 3 = 0 then (vb + 2) - 2 else (vb + 2) + 1 := blkF_val _
  simp only [ca, ca1, ca2, cb, cb1, cb2] at e0 e1 e2
  split_ifs at e0 e1 e2 <;> omega

/-- **Worked example.**  Bob wins against the block 3-cycle. -/
theorem blkPerm_BobWins : BobWins blkPerm :=
  LocallyK3Decodable_BobWins blkPerm blkPerm_locallyK3Decodable

-- Axiom audit: the K=3 winning theorem and its worked instance depend only on the three
-- standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`,
-- no custom axioms.
#print axioms LocallyK3Decodable_BobWins
#print axioms blkPerm_BobWins
