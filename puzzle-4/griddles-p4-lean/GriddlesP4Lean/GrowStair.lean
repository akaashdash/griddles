import GriddlesP4Lean.Q2Even

/-!
# Unbounded-above ⟹ Bob wins: the growing-lag staircase

This file closes the lone remaining residue of `main`'s winning direction: the **unbounded-above**
regime.  When `c` is not eventually identity and *not* bounded above (no `B` bounds
`(c n).val ≤ n.val + B`), `band_of_boundedAbove`'s fixed-slack recurrence can fail, so the
band-top staircase of `WinningAdaptive` is unavailable.  Instead we build a **growing-lag**
staircase: a fixed (signal-independent) move sequence whose lag rises to a *per-pair* separator
slack supplied by `q2even` (`Q2Even.lean`).

## The construction (`GrowStair`)

We enumerate all ordered distinct pairs `(a, b)` with `a < b` as `nthPair : ℕ → ℕ+ × ℕ+`
(surjective onto `{a < b}`).  We process them in *phases*; phase `i` handles `nthPair i = (a, b)`.
The trajectory maintains a displacement `D ≥ 0`, a time `t`, and a lag `lag = t − D` (always even).
Phase `i` starts at `(Dcur, tcur, lagcur)` (`tcur = Dcur + lagcur`) and:

1. Sets the lag floor `L_i := lagcur + 2*Dcur`, asks `q2even` for an even `s_i ≥ L_i` and a
   displacement `D_i` with `separatorAtSlack c a b s_i D_i`.
2. **Walks** to displacement `D_i` (all `R` if `D_i ≥ Dcur`, all `L` otherwise — each `L` fires
   at `D ≥ 1`), then **oscillates** `osc_i := (s_i − lagcur − 2*(Dcur ∸ D_i))/2` `RL`-pairs to lift
   the lag to `s_i`.  This lands at `(D_i, t_i = D_i + s_i)`, lag `= s_i`.  Since
   `time = D + lag = D_i + s_i = t_i`, the ride signal there reads the slack-`s_i` comparison, i.e.
   the `q2even` separator: the two cells' signals differ (Separation).
3. The phase ends at `(D_i, t_i)`; the next phase starts there with `lag = s_i`.

Displacement stays `≥ 0` throughout (Safety).  Displacement `D_i → ∞` along phases (the q2even
slacks `s_i ≥ L_i → ∞` and `t_i = D_i + s_i`; combined with weak descents this gives Yes).

The deliverable is `notEI_unboundedAbove_BobWins`, closing `main`'s last `sorry`.
-/

namespace TrolleyRetrieval

namespace GrowStair

variable (c : Perm)

/-! ### Pair enumeration `nthPair : ℕ → ℕ+ × ℕ+` -/

/-- Advance the pair cursor `(a, b)` (with `a < b`) to the next ordered distinct pair:
    `(a+1, b)` while `a+1 < b`, else wrap to `(1, b+1)`. -/
def nextPair (p : ℕ+ × ℕ+) : ℕ+ × ℕ+ :=
  if p.1 + 1 < p.2 then (p.1 + 1, p.2) else (1, p.2 + 1)

/-- The pair enumeration: `nthPair 0 = (1, 2)`, then walk the cursor. -/
def nthPair : ℕ → ℕ+ × ℕ+
  | 0 => (1, 2)
  | i + 1 => nextPair (nthPair i)

/-- Every enumerated pair is an ordered distinct pair `a < b`. -/
lemma nthPair_lt (i : ℕ) : (nthPair i).1 < (nthPair i).2 := by
  induction i with
  | zero => decide
  | succ n ih =>
      show (nextPair (nthPair n)).1 < (nextPair (nthPair n)).2
      unfold nextPair
      split
      · rename_i h; exact h
      · rename_i h
        -- (1, b+1): 1 < b+1 since b ≥ 1
        show (1 : ℕ+) < (nthPair n).2 + 1
        have hb : 0 < ((nthPair n).2 : ℕ) := (nthPair n).2.pos
        have : (1 : ℕ) < ((nthPair n).2 + 1 : ℕ+).val := by
          simp only [PNat.add_coe, PNat.one_coe]; omega
        exact_mod_cast this

/-- From a state with `(nthPair i).1.val = av`, `(nthPair i).2 = b` and `av + j < b.val`, after `j`
    steps the cursor is at value `av + j` in the same column `b`.  (Stated via `.val`/`.2` to dodge
    `ℕ+` subtype constructions.) -/
lemma nthPair_walk {i : ℕ} {b : ℕ+} {av : ℕ}
    (hi1 : (nthPair i).1.val = av) (hi2 : (nthPair i).2 = b) :
    ∀ j : ℕ, (av + j < b.val) →
      (nthPair (i + j)).1.val = av + j ∧ (nthPair (i + j)).2 = b := by
  intro j
  induction j with
  | zero => intro _; exact ⟨by simpa using hi1, by simpa using hi2⟩
  | succ k ih =>
      intro hlt
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hstep : i + (k + 1) = (i + k) + 1 := by ring
      rw [hstep]
      show (nextPair (nthPair (i + k))).1.val = av + (k + 1)
            ∧ (nextPair (nthPair (i + k))).2 = b
      unfold nextPair
      -- branch on (nthPair (i+k)).1 + 1 < (nthPair (i+k)).2
      have hbranch : (nthPair (i + k)).1 + 1 < (nthPair (i + k)).2 := by
        apply (PNat.coe_lt_coe _ _).1
        rw [PNat.add_coe, ih1, ih2]; simp only [PNat.one_coe]; omega
      rw [if_pos hbranch]
      refine ⟨?_, ih2⟩
      show ((nthPair (i + k)).1 + 1).val = av + (k + 1)
      rw [PNat.add_coe, ih1]; simp only [PNat.one_coe]; omega

/-- The cursor reaches the column start `(1, b)` for every `b ≥ 2`: `(nthPair i).1 = 1` and
    `(nthPair i).2.val = b`. -/
lemma nthPair_reaches_col (b : ℕ) (hb : 2 ≤ b) :
    ∃ i : ℕ, (nthPair i).1 = 1 ∧ (nthPair i).2.val = b := by
  induction b with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 2 with hn | hn
      · -- n+1 = 2 ⇒ n = 1
        have hn1 : n = 1 := by omega
        subst hn1
        exact ⟨0, by decide, by decide⟩
      · -- reach (1, n), walk to (n-1, n), one more step wraps to (1, n+1)
        obtain ⟨i, hi1, hi2⟩ := ih hn
        -- from (1, n) walk j = n-2 steps to value 1 + (n-2) = n-1 < n
        set bcol : ℕ+ := (nthPair i).2 with hbcol
        have hbcolval : bcol.val = n := hi2
        have hav1 : (nthPair i).1.val = 1 := by rw [hi1]; rfl
        obtain ⟨hw1, hw2⟩ := nthPair_walk hav1 rfl (n - 2) (by rw [hbcolval]; omega)
        refine ⟨(i + (n - 2)) + 1, ?_, ?_⟩
        · show (nextPair (nthPair (i + (n - 2)))).1 = 1
          unfold nextPair
          have hbranch : ¬ (nthPair (i + (n - 2))).1 + 1 < (nthPair (i + (n - 2))).2 := by
            intro hlt
            have := (PNat.coe_lt_coe _ _).2 hlt
            rw [PNat.add_coe, hw1] at this
            rw [hw2, hbcolval] at this
            simp only [PNat.one_coe] at this; omega
          rw [if_neg hbranch]
        · show (nextPair (nthPair (i + (n - 2)))).2.val = n + 1
          unfold nextPair
          have hbranch : ¬ (nthPair (i + (n - 2))).1 + 1 < (nthPair (i + (n - 2))).2 := by
            intro hlt
            have := (PNat.coe_lt_coe _ _).2 hlt
            rw [PNat.add_coe, hw1] at this
            rw [hw2, hbcolval] at this
            simp only [PNat.one_coe] at this; omega
          rw [if_neg hbranch]
          show ((nthPair (i + (n - 2))).2 + 1).val = n + 1
          rw [PNat.add_coe, hw2, hbcolval]; rfl

/-- **Surjectivity.**  Every ordered distinct pair `(a, b)` with `a < b` is `nthPair i` for some `i`. -/
lemma nthPair_surj {a b : ℕ+} (hab : a < b) : ∃ i : ℕ, nthPair i = (a, b) := by
  have habval : a.val < b.val := hab
  have ha1 : 0 < a.val := a.pos
  have hb2 : 2 ≤ b.val := by omega
  obtain ⟨i, hi1, hi2⟩ := nthPair_reaches_col b.val hb2
  have hav1 : (nthPair i).1.val = 1 := by rw [hi1]; rfl
  -- need (nthPair i).2 = b; from hi2 : (nthPair i).2.val = b.val
  have hi2' : (nthPair i).2 = b := PNat.coe_injective hi2
  -- walk from value 1 to value a.val: j = a.val - 1 steps; 1 + (a.val-1) = a.val < b.val
  obtain ⟨hw1, hw2⟩ := nthPair_walk hav1 hi2' (a.val - 1) (by omega)
  refine ⟨i + (a.val - 1), ?_⟩
  apply Prod.ext
  · -- (nthPair (i + (a.val-1))).1 = a, via .val
    apply PNat.coe_injective
    show (nthPair (i + (a.val - 1))).1.val = a.val
    rw [hw1]; omega
  · exact hw2

/-! ### Per-phase data

We need the unbounded-above hypothesis `hub` to invoke `q2even`.  We carry it as a section variable.
`phaseInfo i` records the trajectory state at the **start** of phase `i`: the displacement `Dcur`
and the lag `lagcur` (the time is `tcur = Dcur + lagcur`).  Phase `i` handles `nthPair i = (a, b)`:
it requests a `q2even` separator at lag floor `L_i := lagcur + 2*Dcur`, getting an even slack
`s_i ≥ L_i` and a displacement `D_i` with `separatorAtSlack c a b s_i D_i`; the phase ends at
`(D_i, t_i = D_i + s_i)` with lag `s_i`. -/

variable (hub : ¬ ∃ B : ℕ, ∀ n : ℕ+, (c n).val ≤ n.val + B)

/-- The slack/displacement pair `(s_i, D_i)` chosen by `q2even` for phase `i`, given the lag floor
    `L` and the phase's pair `(a, b)`.  Returns `(s, D)`. -/
noncomputable def q2pick (a b : ℕ+) (hab : a < b) (L : ℕ) : ℕ × ℕ :=
  let h := q2even c hub a b hab L
  (Classical.choose h, Classical.choose (Classical.choose_spec h).2.2)

lemma q2pick_spec (a b : ℕ+) (hab : a < b) (L : ℕ) :
    Even (q2pick c hub a b hab L).1 ∧ L ≤ (q2pick c hub a b hab L).1 ∧
      separatorAtSlack c a b (q2pick c hub a b hab L).1 (q2pick c hub a b hab L).2 := by
  unfold q2pick
  set h := q2even c hub a b hab L with hh
  have h1 := (Classical.choose_spec h).1
  have h2 := (Classical.choose_spec h).2.1
  have h3 := Classical.choose_spec (Classical.choose_spec h).2.2
  exact ⟨h1, h2, h3⟩

/-- The lag floor requested at phase `i`, given the start `(Dcur, lagcur)`:
    `lagcur + 2*Dcur + 2*(i+1)` (the `2*(i+1)` term forces `sPick → ∞`). -/
def LfloorOf (i Dcur lagcur : ℕ) : ℕ := lagcur + 2 * Dcur + 2 * (i + 1)

/-- Phase state at the **start** of phase `i`: `(Dcur, lagcur)`.  Phase `i` requests a `q2even`
    separator at floor `LfloorOf i Dcur lagcur`, getting `(s_i, D_i)`; rides a tail to
    `Dfinal := max (i+1) (D_i + 1)`; phase `i+1` starts at `(Dfinal, s_i)`. -/
noncomputable def phaseInfo : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | i + 1 =>
      let a := (nthPair i).1
      let b := (nthPair i).2
      let Dcur := (phaseInfo i).1
      let lagcur := (phaseInfo i).2
      let L := LfloorOf i Dcur lagcur
      let sd := q2pick c hub a b (nthPair_lt i) L
      let Dfinal := max (i + 1) (sd.2 + 1)
      (Dfinal, sd.1)   -- next start: D = Dfinal_i, lag = s_i

/-- `Dcur i` — displacement at the start of phase `i`. -/
noncomputable def Dcur (i : ℕ) : ℕ := (phaseInfo c hub i).1
/-- `lagcur i` — lag at the start of phase `i`. -/
noncomputable def lagcur (i : ℕ) : ℕ := (phaseInfo c hub i).2
/-- `tcur i` — time at the start of phase `i` ( = Dcur + lagcur). -/
noncomputable def tcur (i : ℕ) : ℕ := Dcur c hub i + lagcur c hub i

/-- The lag floor requested at phase `i`. -/
noncomputable def Lfloor (i : ℕ) : ℕ := LfloorOf i (Dcur c hub i) (lagcur c hub i)

/-- The slack `s_i` chosen at phase `i`. -/
noncomputable def sPick (i : ℕ) : ℕ :=
  (q2pick c hub (nthPair i).1 (nthPair i).2 (nthPair_lt i) (Lfloor c hub i)).1
/-- The displacement `D_i` chosen at phase `i`. -/
noncomputable def DPick (i : ℕ) : ℕ :=
  (q2pick c hub (nthPair i).1 (nthPair i).2 (nthPair_lt i) (Lfloor c hub i)).2

/-- Tail-ride length of phase `i`: rides from `DPick i` up to `Dfinal i = max (i+1) (DPick i + 1)`. -/
noncomputable def tailRight (i : ℕ) : ℕ := max (i + 1) (DPick c hub i + 1) - DPick c hub i
/-- Phase-end displacement of phase `i`: `Dfinal i = max (i+1) (DPick i + 1)`. -/
noncomputable def Dfinal (i : ℕ) : ℕ := max (i + 1) (DPick c hub i + 1)

lemma tailRight_pos (i : ℕ) : 1 ≤ tailRight c hub i := by
  unfold tailRight; omega
lemma Dfinal_eq (i : ℕ) : Dfinal c hub i = DPick c hub i + tailRight c hub i := by
  unfold Dfinal tailRight; omega
lemma Dfinal_ge_idx (i : ℕ) : i + 1 ≤ Dfinal c hub i := by unfold Dfinal; omega

lemma phaseInfo_succ (i : ℕ) :
    phaseInfo c hub (i + 1) = (Dfinal c hub i, sPick c hub i) := by
  show (_, _) = _
  rfl

lemma Dcur_succ (i : ℕ) : Dcur c hub (i + 1) = Dfinal c hub i := by
  unfold Dcur; rw [phaseInfo_succ]
lemma lagcur_succ (i : ℕ) : lagcur c hub (i + 1) = sPick c hub i := by
  unfold lagcur; rw [phaseInfo_succ]

/-- The chosen slack is even, `≥ Lfloor`, and is a separator at `DPick`. -/
lemma sPick_spec (i : ℕ) :
    Even (sPick c hub i) ∧ Lfloor c hub i ≤ sPick c hub i ∧
      separatorAtSlack c (nthPair i).1 (nthPair i).2 (sPick c hub i) (DPick c hub i) :=
  q2pick_spec c hub (nthPair i).1 (nthPair i).2 (nthPair_lt i) (Lfloor c hub i)

/-- The lag at every phase start is even. -/
lemma lagcur_even (i : ℕ) : Even (lagcur c hub i) := by
  cases i with
  | zero => show Even 0; exact ⟨0, rfl⟩
  | succ n => rw [lagcur_succ]; exact (sPick_spec c hub n).1

/-! ### Per-phase walk and oscillation counts

Phase `i` walks from `Dcur i` to `DPick i` (`walkSteps i` steps), then oscillates `oscPairs i`
`RL`-pairs to lift the lag from `lagcur i` to `sPick i`.  The defining identity is

  `walkSteps i + 2 * oscPairs i = (tcur (i+1)) - tcur i`,  and `tcur (i+1) = DPick i + sPick i`.

The walk-lag gain is `2 * (Dcur i ∸ DPick i)` (only leftward walks raise the lag).  The crucial
budget bound `2 * Dcur i ≤ sPick i - lagcur i` (from `Lfloor i ≤ sPick i`) makes `oscPairs i`
well-defined and the time identity hold. -/

/-- Number of walk steps in phase `i`: `|DPick i − Dcur i|`. -/
noncomputable def walkSteps (i : ℕ) : ℕ :=
  if Dcur c hub i ≤ DPick c hub i then DPick c hub i - Dcur c hub i
  else Dcur c hub i - DPick c hub i

/-- Lag gained by the walk of phase `i` (only leftward walks raise the lag). -/
noncomputable def walkLagGain (i : ℕ) : ℕ := 2 * (Dcur c hub i - DPick c hub i)

/-- Number of `RL` oscillation pairs in phase `i`. -/
noncomputable def oscPairs (i : ℕ) : ℕ := (sPick c hub i - lagcur c hub i - walkLagGain c hub i) / 2

/-- The key budget bound: `2 * Dcur i ≤ sPick i − lagcur i` (so the oscillation count is nonneg). -/
lemma budget (i : ℕ) : lagcur c hub i + 2 * Dcur c hub i ≤ sPick c hub i := by
  have := (sPick_spec c hub i).2.1
  unfold Lfloor LfloorOf at this
  omega

/-- `sPick i ≥ 2*(i+1)` — the slack grows without bound (drives the Yes obligation). -/
lemma sPick_ge (i : ℕ) : 2 * (i + 1) ≤ sPick c hub i := by
  have := (sPick_spec c hub i).2.1
  unfold Lfloor LfloorOf at this
  omega

/-- `sPick i − lagcur i − walkLagGain i` is even (so `2 * oscPairs i` recovers it). -/
lemma oscPairs_double (i : ℕ) :
    2 * oscPairs c hub i = sPick c hub i - lagcur c hub i - walkLagGain c hub i := by
  unfold oscPairs
  have hbud := budget c hub i
  have hwlg : walkLagGain c hub i ≤ 2 * Dcur c hub i := by
    unfold walkLagGain; omega
  -- s - lag - wlg ≥ 0 and even ⇒ 2 * (·/2) = ·
  have hev_s : Even (sPick c hub i) := (sPick_spec c hub i).1
  have hev_lag : Even (lagcur c hub i) := lagcur_even c hub i
  have hev_wlg : Even (walkLagGain c hub i) := by unfold walkLagGain; exact ⟨_, by ring⟩
  obtain ⟨ks, hks⟩ := hev_s
  obtain ⟨kl, hkl⟩ := hev_lag
  obtain ⟨kw, hkw⟩ := hev_wlg
  -- the quantity is even, so /2 doubles back
  have : Even (sPick c hub i - lagcur c hub i - walkLagGain c hub i) := by
    rw [hks, hkl, hkw]
    refine ⟨ks - kl - kw, ?_⟩
    omega
  omega

/-- Phase length: `walkSteps i + 2 * oscPairs i + tailRight i` (always `≥ 1`). -/
noncomputable def phaseLen (i : ℕ) : ℕ := walkSteps c hub i + 2 * oscPairs c hub i + tailRight c hub i

lemma phaseLen_pos (i : ℕ) : 1 ≤ phaseLen c hub i := by
  unfold phaseLen; have := tailRight_pos c hub i; omega

/-- The **separator-read length**: steps from phase start to the post-osc / pre-tail point where the
    separator is read.  Equals `walkSteps i + 2*oscPairs i`. -/
noncomputable def sepLen (i : ℕ) : ℕ := walkSteps c hub i + 2 * oscPairs c hub i

lemma sepLen_le_phaseLen (i : ℕ) : sepLen c hub i ≤ phaseLen c hub i := by
  unfold sepLen phaseLen; omega

/-- **Time at start of phase `i` is `Dcur i + lagcur i`** (by definition). -/
lemma tcur_eq (i : ℕ) : tcur c hub i = Dcur c hub i + lagcur c hub i := rfl

/-- **The separator-read time of phase `i`** is `tcur i + sepLen i = DPick i + sPick i`, and the
    displacement there is `DPick i`. -/
lemma sepTime_eq (i : ℕ) : tcur c hub i + sepLen c hub i = DPick c hub i + sPick c hub i := by
  have hbud := budget c hub i
  have hosc := oscPairs_double c hub i
  unfold tcur sepLen walkSteps walkLagGain at *
  by_cases hle : Dcur c hub i ≤ DPick c hub i
  · rw [if_pos hle]
    rw [Nat.sub_eq_zero_of_le hle] at hosc
    simp only [Nat.mul_zero, Nat.sub_zero] at hosc
    omega
  · rw [if_neg hle]
    omega

/-- **Time identity.**  `tcur (i+1) = tcur i + phaseLen i` (the phase advances time by its length). -/
lemma tcur_succ (i : ℕ) : tcur c hub (i + 1) = tcur c hub i + phaseLen c hub i := by
  have hsep := sepTime_eq c hub i
  have htail := Dfinal_eq c hub i
  unfold tcur phaseLen sepLen at *
  rw [Dcur_succ c hub i, lagcur_succ c hub i]
  -- Dfinal + sPick = (Dcur + lagcur) + (walkSteps + 2*oscPairs + tailRight)
  -- = sepTime + tailRight = (DPick + sPick) + tailRight = Dfinal + sPick  ✓
  omega

/-! ### The move at step `j` of phase `i`, and the displacement there

`moveAtIJ i j` is the direction emitted at step `j` (`0 ≤ j < phaseLen i`) of phase `i`:
`walk` (R if rightward else L), then `osc` (`RL`-pairs), then `tail` (R).  `dispAtIJ i j` is the
displacement at the **start** of step `j` (`0 ≤ j ≤ phaseLen i`); `dispAtIJ i 0 = Dcur i` and
`dispAtIJ i (phaseLen i) = Dfinal i`. -/

/-- Direction emitted at step `j` of phase `i`. -/
noncomputable def moveAtIJ (i j : ℕ) : Dir :=
  if j < walkSteps c hub i then
    (if Dcur c hub i ≤ DPick c hub i then Dir.right else Dir.left)
  else if j < sepLen c hub i then
    (if (j - walkSteps c hub i) % 2 = 0 then Dir.right else Dir.left)
  else Dir.right

/-- Displacement at the start of step `j` of phase `i`.  Uses STRICT `<` at both regime boundaries
    so `j = walkSteps` lands in the oscillation branch and `j = sepLen` in the tail branch (each
    boundary value agreeing, since `sepLen − walkSteps` is even and `tail` starts at `DPick`). -/
noncomputable def dispAtIJ (i j : ℕ) : ℕ :=
  if j < walkSteps c hub i then
    (if Dcur c hub i ≤ DPick c hub i then Dcur c hub i + j else Dcur c hub i - j)
  else if j < sepLen c hub i then
    DPick c hub i + ((j - walkSteps c hub i) % 2)
  else
    DPick c hub i + (j - sepLen c hub i)

lemma dispAtIJ_zero (i : ℕ) : dispAtIJ c hub i 0 = Dcur c hub i := by
  unfold dispAtIJ
  by_cases hw : 0 < walkSteps c hub i
  · rw [if_pos hw]; split <;> omega
  · rw [if_neg hw]
    -- walkSteps = 0 ⇒ Dcur = DPick.  Then either osc (DPick+0) or tail (DPick+0); both = Dcur.
    have hw0 : walkSteps c hub i = 0 := by omega
    have hdeq : Dcur c hub i = DPick c hub i := by unfold walkSteps at hw0; split at hw0 <;> omega
    have hmod : (0 - walkSteps c hub i) % 2 = 0 := by omega
    by_cases ho : 0 < sepLen c hub i
    · rw [if_pos ho, hmod]; omega
    · rw [if_neg ho]; omega

/-- The walk lands at `DPick i`: `dispAtIJ i (walkSteps i) = DPick i`. -/
lemma dispAtIJ_walkSteps (i : ℕ) : dispAtIJ c hub i (walkSteps c hub i) = DPick c hub i := by
  unfold dispAtIJ
  have hsw : walkSteps c hub i ≤ sepLen c hub i := by unfold sepLen; omega
  rw [if_neg (by omega)]
  by_cases ho : walkSteps c hub i < sepLen c hub i
  · rw [if_pos ho]; simp only [Nat.sub_self, Nat.zero_mod]; omega
  · rw [if_neg ho]; omega

/-- `dispAtIJ i (phaseLen i) = Dfinal i`. -/
lemma dispAtIJ_phaseLen (i : ℕ) : dispAtIJ c hub i (phaseLen c hub i) = Dfinal c hub i := by
  have htail := tailRight_pos c hub i
  have hsw : walkSteps c hub i ≤ sepLen c hub i := by unfold sepLen; omega
  unfold dispAtIJ phaseLen sepLen
  rw [if_neg (by omega), if_neg (by omega)]
  -- DPick + (phaseLen - sepLen) = DPick + tailRight = Dfinal
  rw [Dfinal_eq]
  unfold walkSteps tailRight at *
  omega

/-- During the walk regime, the displacement is `≥ DPick i` when leftward (so left moves are safe)
    and the increments match `moveAtIJ`.  **Within-phase continuity.**  For `j < phaseLen i`:
    `dispAtIJ i (j+1) = dispAtIJ i j + (moveAtIJ i j).delta`, *and* whenever `moveAtIJ i j = left`
    the displacement `dispAtIJ i j ≥ 1`. -/
lemma dispAtIJ_step (i j : ℕ) (_hj : j < phaseLen c hub i) :
    (dispAtIJ c hub i (j + 1) : ℤ) = (dispAtIJ c hub i j : ℤ) + (moveAtIJ c hub i j).delta
      ∧ (moveAtIJ c hub i j = Dir.left → 1 ≤ dispAtIJ c hub i j) := by
  -- boundary relations (as opaque numbers for omega).
  have hsw : walkSteps c hub i ≤ sepLen c hub i := by unfold sepLen; omega
  have hsp : sepLen c hub i ≤ phaseLen c hub i := sepLen_le_phaseLen c hub i
  have hwsR : Dcur c hub i ≤ DPick c hub i →
      walkSteps c hub i = DPick c hub i - Dcur c hub i ∧ DPick c hub i = Dcur c hub i + walkSteps c hub i :=
    fun hdir => by unfold walkSteps; rw [if_pos hdir]; omega
  have hwsL : ¬ (Dcur c hub i ≤ DPick c hub i) →
      walkSteps c hub i = Dcur c hub i - DPick c hub i ∧ DPick c hub i + walkSteps c hub i = Dcur c hub i :=
    fun hdir => by unfold walkSteps; rw [if_neg hdir]; omega
  -- Evaluate the displacement at j and j+1, and the move, per regime.
  -- We split on the three regimes for the *move* index j, then compute disp(j), disp(j+1).
  by_cases hw : j < walkSteps c hub i
  · -- walk regime: move = R/L depending on direction.
    by_cases hdir : Dcur c hub i ≤ DPick c hub i
    · -- rightward: move R, disp(j) = Dcur + j, disp(j+1) = Dcur + (j+1)
      have hmv : moveAtIJ c hub i j = Dir.right := by
        unfold moveAtIJ; rw [if_pos hw, if_pos hdir]
      have hdj : dispAtIJ c hub i j = Dcur c hub i + j := by
        unfold dispAtIJ; rw [if_pos hw, if_pos hdir]
      obtain ⟨hws, hDP⟩ := hwsR hdir
      have hdj1 : dispAtIJ c hub i (j + 1) = Dcur c hub i + (j + 1) := by
        unfold dispAtIJ
        by_cases hjw1 : j + 1 < walkSteps c hub i
        · rw [if_pos hjw1, if_pos hdir]
        · rw [if_neg hjw1]
          -- j+1 = walkSteps; either osc (DPick+0) or tail (DPick+0), both = Dcur + walkSteps
          by_cases hb : j + 1 < sepLen c hub i
          · rw [if_pos hb, show j + 1 - walkSteps c hub i = 0 by omega]; simp; omega
          · rw [if_neg hb, show j + 1 - sepLen c hub i = 0 by omega]; simp; omega
      rw [hmv, hdj, hdj1]
      refine ⟨by simp only [Dir.delta_right]; push_cast; ring, fun h => absurd h (by decide)⟩
    · -- leftward: move L, disp(j) = Dcur - j ≥ 1, disp(j+1) = Dcur - (j+1)
      have hmv : moveAtIJ c hub i j = Dir.left := by
        unfold moveAtIJ; rw [if_pos hw, if_neg hdir]
      obtain ⟨hws, hDP⟩ := hwsL hdir
      have hdj : dispAtIJ c hub i j = Dcur c hub i - j := by
        unfold dispAtIJ; rw [if_pos hw, if_neg hdir]
      have hdj1 : dispAtIJ c hub i (j + 1) = Dcur c hub i - (j + 1) := by
        unfold dispAtIJ
        by_cases hjw1 : j + 1 < walkSteps c hub i
        · rw [if_pos hjw1, if_neg hdir]
        · rw [if_neg hjw1]
          by_cases hb : j + 1 < sepLen c hub i
          · rw [if_pos hb, show j + 1 - walkSteps c hub i = 0 by omega]; simp; omega
          · rw [if_neg hb, show j + 1 - sepLen c hub i = 0 by omega]; simp; omega
      rw [hmv, hdj, hdj1]
      refine ⟨?_, fun _ => by omega⟩
      simp only [Dir.delta_left]
      push_cast [Nat.cast_sub (by omega : j + 1 ≤ Dcur c hub i),
        Nat.cast_sub (by omega : j ≤ Dcur c hub i)]; ring
  · -- not walk
    by_cases ho : j < sepLen c hub i
    · -- osc regime: walkSteps ≤ j < sepLen
      have hdj : dispAtIJ c hub i j = DPick c hub i + ((j - walkSteps c hub i) % 2) := by
        unfold dispAtIJ; rw [if_neg hw, if_pos ho]
      -- the parity at j and j+1.  sepLen - walkSteps is even, so at the boundary j+1 = sepLen the
      -- osc value (parity (sepLen-walkSteps) = 0) equals the tail value DPick + 0.
      have heven : (sepLen c hub i - walkSteps c hub i) % 2 = 0 := by
        unfold sepLen; omega
      have hdj1 : dispAtIJ c hub i (j + 1)
          = DPick c hub i + (((j - walkSteps c hub i) + 1) % 2) := by
        unfold dispAtIJ
        rw [if_neg (by omega : ¬ j + 1 < walkSteps c hub i)]
        by_cases hb : j + 1 < sepLen c hub i
        · rw [if_pos hb, show j + 1 - walkSteps c hub i = (j - walkSteps c hub i) + 1 by omega]
        · -- j + 1 = sepLen (boundary): tail branch DPick + 0; osc parity here is 0
          rw [if_neg hb]
          have hjeq : j + 1 = sepLen c hub i := by omega
          have hpar0 : ((j - walkSteps c hub i) + 1) % 2 = 0 := by
            have : (j - walkSteps c hub i) + 1 = sepLen c hub i - walkSteps c hub i := by omega
            rw [this]; exact heven
          rw [show j + 1 - sepLen c hub i = 0 by omega, hpar0]
      by_cases hpar : (j - walkSteps c hub i) % 2 = 0
      · have hmv : moveAtIJ c hub i j = Dir.right := by
          unfold moveAtIJ; rw [if_neg hw, if_pos ho, if_pos hpar]
        rw [hmv, hdj, hdj1, hpar, show ((j - walkSteps c hub i) + 1) % 2 = 1 by omega]
        refine ⟨by simp only [Dir.delta_right]; push_cast; omega, fun h => absurd h (by decide)⟩
      · have hmv : moveAtIJ c hub i j = Dir.left := by
          unfold moveAtIJ; rw [if_neg hw, if_pos ho, if_neg hpar]
        have hr1 : (j - walkSteps c hub i) % 2 = 1 := by omega
        rw [hmv, hdj, hdj1, hr1, show ((j - walkSteps c hub i) + 1) % 2 = 0 by omega]
        refine ⟨by simp only [Dir.delta_left]; push_cast; omega, fun _ => by omega⟩
    · -- tail regime: sepLen ≤ j, move R
      have hmv : moveAtIJ c hub i j = Dir.right := by
        unfold moveAtIJ; rw [if_neg hw, if_neg ho]
      have hdj : dispAtIJ c hub i j = DPick c hub i + (j - sepLen c hub i) := by
        unfold dispAtIJ; rw [if_neg hw, if_neg ho]
      have hdj1 : dispAtIJ c hub i (j + 1) = DPick c hub i + ((j - sepLen c hub i) + 1) := by
        unfold dispAtIJ
        rw [if_neg (by omega : ¬ j + 1 < walkSteps c hub i),
          if_neg (by omega : ¬ j + 1 < sepLen c hub i)]
        rw [show j + 1 - sepLen c hub i = (j - sepLen c hub i) + 1 by omega]
      rw [hmv, hdj, hdj1]
      refine ⟨by simp only [Dir.delta_right]; push_cast; ring, fun h => absurd h (by decide)⟩

/-! ### The global trajectory: concatenating phases

`gst t = (i, j)` is the global state at time `t`: phase `i`, step `j` within the phase.  It advances
by one step per tick, wrapping `(i, phaseLen i − 1) → (i+1, 0)`.  The move sequence is
`gmoves t := moveAtIJ (gst t).1 (gst t).2`, and `gdisp t := dispAtIJ (gst t).1 (gst t).2` is the
displacement at time `t`. -/

/-- Global state `(phase, step)` at time `t`. -/
noncomputable def gst : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | t + 1 =>
      let p := gst t
      if p.2 + 1 < phaseLen c hub p.1 then (p.1, p.2 + 1) else (p.1 + 1, 0)

lemma gst_succ (t : ℕ) :
    gst c hub (t + 1)
      = (if (gst c hub t).2 + 1 < phaseLen c hub (gst c hub t).1
          then ((gst c hub t).1, (gst c hub t).2 + 1) else ((gst c hub t).1 + 1, 0)) := rfl

/-- **Invariant: the step is within the phase.**  `(gst t).2 < phaseLen (gst t).1`. -/
lemma gst_step_lt (t : ℕ) : (gst c hub t).2 < phaseLen c hub (gst c hub t).1 := by
  induction t with
  | zero => exact phaseLen_pos c hub 0
  | succ n ih =>
      rw [gst_succ]
      by_cases hb : (gst c hub n).2 + 1 < phaseLen c hub (gst c hub n).1
      · rw [if_pos hb]; exact hb
      · rw [if_neg hb]; exact phaseLen_pos c hub _

/-- The global move sequence. -/
noncomputable def gmoves : ℕ → Dir := fun t => moveAtIJ c hub (gst c hub t).1 (gst c hub t).2
/-- The global displacement at time `t`. -/
noncomputable def gdisp (t : ℕ) : ℕ := dispAtIJ c hub (gst c hub t).1 (gst c hub t).2

/-- **Displacement-tracking.**  The cumulative `ℤ`-displacement of `gmoves` equals `gdisp` (a `ℕ`,
    so `≥ 0`).  Within a phase this is `dispAtIJ_step`; at a wrap it is the boundary continuity
    `dispAtIJ i (phaseLen i) = Dfinal i = Dcur (i+1) = dispAtIJ (i+1) 0`. -/
lemma cumDelta_gmoves (t : ℕ) : cumDelta (gmoves c hub) t = (gdisp c hub t : ℤ) := by
  induction t with
  | zero =>
      simp only [cumDelta, gdisp]
      rw [show gst c hub 0 = (0, 0) from rfl]
      rw [dispAtIJ_zero c hub 0]
      -- Dcur 0 = 0
      show (0 : ℤ) = (Dcur c hub 0 : ℤ)
      have : Dcur c hub 0 = 0 := rfl
      rw [this]; rfl
  | succ n ih =>
      rw [cumDelta, ih]
      -- gmoves n = moveAtIJ (gst n).1 (gst n).2; gdisp (n+1) = ...
      set i := (gst c hub n).1 with hi
      set j := (gst c hub n).2 with hj
      have hjlt : j < phaseLen c hub i := gst_step_lt c hub n
      have hstep := dispAtIJ_step c hub i j hjlt
      show (gdisp c hub n : ℤ) + (gmoves c hub n).delta = (gdisp c hub (n + 1) : ℤ)
      have hgmn : gmoves c hub n = moveAtIJ c hub i j := rfl
      have hgdn : gdisp c hub n = dispAtIJ c hub i j := rfl
      rw [hgmn, hgdn]
      -- compute gdisp (n+1)
      by_cases hb : j + 1 < phaseLen c hub i
      · -- within phase: gst (n+1) = (i, j+1)
        have hgst1 : gst c hub (n + 1) = (i, j + 1) := by
          rw [gst_succ, ← hi, ← hj, if_pos hb]
        have hgd1 : gdisp c hub (n + 1) = dispAtIJ c hub i (j + 1) := by
          unfold gdisp; rw [hgst1]
        rw [hgd1, hstep.1]
      · -- wrap: j + 1 = phaseLen i; gst (n+1) = (i+1, 0)
        have hjpl : j + 1 = phaseLen c hub i := by omega
        have hgst1 : gst c hub (n + 1) = (i + 1, 0) := by
          rw [gst_succ, ← hi, ← hj, if_neg hb]
        have hgd1 : gdisp c hub (n + 1) = dispAtIJ c hub (i + 1) 0 := by
          unfold gdisp; rw [hgst1]
        rw [hgd1, dispAtIJ_zero c hub (i + 1), Dcur_succ c hub i]
        -- LHS: dispAtIJ i j + (moveAtIJ i j).delta = dispAtIJ i (j+1) = dispAtIJ i (phaseLen i) = Dfinal i
        rw [← hstep.1, hjpl, dispAtIJ_phaseLen c hub i]

/-- `dispAtIJ i (sepLen i) = DPick i` (the tail starts at `DPick`). -/
lemma dispAtIJ_sepLen (i : ℕ) : dispAtIJ c hub i (sepLen c hub i) = DPick c hub i := by
  have hsw : walkSteps c hub i ≤ sepLen c hub i := by unfold sepLen; omega
  unfold dispAtIJ
  rw [if_neg (by omega), if_neg (by omega)]
  omega

/-! ### Connecting global time to the phase decomposition -/

/-- **Within-phase reach.**  At global time `tcur i + j` (with `j < phaseLen i`) the state is `(i, j)`,
    and the phase-start `gst (tcur i) = (i, 0)`. -/
lemma gst_within (i : ℕ) :
    (gst c hub (tcur c hub i) = (i, 0)) ∧
    (∀ j : ℕ, j < phaseLen c hub i → gst c hub (tcur c hub i + j) = (i, j)) := by
  induction i with
  | zero =>
      have hstart : gst c hub (tcur c hub 0) = (0, 0) := by
        have ht0 : tcur c hub 0 = 0 := rfl; rw [ht0]; rfl
      refine ⟨hstart, ?_⟩
      intro j
      induction j with
      | zero => intro _; simpa using hstart
      | succ k ih =>
          intro hk
          rw [show tcur c hub 0 + (k + 1) = (tcur c hub 0 + k) + 1 by ring]
          rw [gst_succ, ih (by omega)]
          rw [if_pos (by simp only []; omega : (0, k).2 + 1 < phaseLen c hub (0, k).1)]
  | succ n ihn =>
      obtain ⟨hn0, hnwithin⟩ := ihn
      have hreach : gst c hub (tcur c hub (n + 1)) = (n + 1, 0) := by
        rw [tcur_succ]
        have hpl : 1 ≤ phaseLen c hub n := phaseLen_pos c hub n
        have hlast : gst c hub (tcur c hub n + (phaseLen c hub n - 1)) = (n, phaseLen c hub n - 1) :=
          hnwithin (phaseLen c hub n - 1) (by omega)
        rw [show tcur c hub n + phaseLen c hub n = (tcur c hub n + (phaseLen c hub n - 1)) + 1 by omega]
        rw [gst_succ, hlast]
        rw [if_neg (by simp only []; omega :
          ¬ (n, phaseLen c hub n - 1).2 + 1 < phaseLen c hub (n, phaseLen c hub n - 1).1)]
      refine ⟨hreach, ?_⟩
      intro j
      induction j with
      | zero => intro _; simpa using hreach
      | succ k ih =>
          intro hk
          rw [show tcur c hub (n + 1) + (k + 1) = (tcur c hub (n + 1) + k) + 1 by ring]
          rw [gst_succ, ih (by omega)]
          rw [if_pos (by simp only []; omega : (n + 1, k).2 + 1 < phaseLen c hub (n + 1, k).1)]

/-- **Safety.**  From any start cell, the position never falls off the left edge. -/
lemma grow_safe (k₀ : ℕ+) (t : ℕ) :
    1 ≤ position c (ofMoves (gmoves c hub)) (k₀ : ℤ) t := by
  rw [position_ofMoves, cumDelta_gmoves]
  have h1 : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.pos
  have h2 : (0 : ℤ) ≤ (gdisp c hub t : ℤ) := Int.natCast_nonneg _
  linarith

/-! ### Separation -/

/-- The cumulative displacement at the separator-read time of phase `i` is `DPick i`. -/
lemma cumDelta_at_sepTime (i : ℕ) :
    cumDelta (gmoves c hub) (tcur c hub i + sepLen c hub i) = (DPick c hub i : ℤ) := by
  have hsep_lt : sepLen c hub i < phaseLen c hub i := by
    have := tailRight_pos c hub i; unfold phaseLen sepLen; omega
  have hgst := (gst_within c hub i).2 (sepLen c hub i) hsep_lt
  rw [cumDelta_gmoves]
  show (gdisp c hub (tcur c hub i + sepLen c hub i) : ℤ) = _
  unfold gdisp
  rw [hgst]
  show (dispAtIJ c hub i (sepLen c hub i) : ℤ) = (DPick c hub i : ℤ)
  rw [dispAtIJ_sepLen]

/-- **Separation for an enumerated pair.**  Phase `i` (handling `nthPair i = (a, b)`) reads, at its
    separator-read time, the slack-`sPick i` comparison, which is the `q2even` separator: the signals
    of `a` and `b` differ. -/
lemma grow_separates_pair (i : ℕ) :
    ∃ s : ℕ,
      signalOf c (position c (ofMoves (gmoves c hub)) ((nthPair i).1 : ℤ) s) s
        ≠ signalOf c (position c (ofMoves (gmoves c hub)) ((nthPair i).2 : ℤ) s) s := by
  set a := (nthPair i).1 with ha
  set b := (nthPair i).2 with hb
  set tstar := tcur c hub i + sepLen c hub i with htstar
  refine ⟨tstar, ?_⟩
  -- cumDelta at tstar = DPick i; time identity tstar = DPick i + sPick i.
  have hcum : cumDelta (gmoves c hub) tstar = (DPick c hub i : ℤ) := cumDelta_at_sepTime c hub i
  have htime : tstar = DPick c hub i + sPick c hub i := sepTime_eq c hub i
  -- both signals in slack-comparison form
  rw [signalOf_ofMoves_eq c (gmoves c hub) a tstar (DPick c hub i) hcum,
      signalOf_ofMoves_eq c (gmoves c hub) b tstar (DPick c hub i) hcum]
  rw [htime]
  -- the q2even separator at slack sPick i, displacement DPick i
  have hsep := (sPick_spec c hub i).2.2
  unfold separatorAtSlack at hsep
  -- hsep : decide ((c (cellAt a (DPick i))).val < DPick i + sPick i) ≠ decide (... b ...)
  exact hsep

/-- **Separation (any distinct pair).**  The growing-lag trajectory separates any two distinct
    start cells. -/
lemma grow_separates (a b : ℕ+) (hab : a ≠ b) :
    ∃ s : ℕ,
      signalOf c (position c (ofMoves (gmoves c hub)) (a : ℤ) s) s
        ≠ signalOf c (position c (ofMoves (gmoves c hub)) (b : ℤ) s) s := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · obtain ⟨i, hi⟩ := nthPair_surj hlt
    obtain ⟨s, hs⟩ := grow_separates_pair c hub i
    rw [hi] at hs
    exact ⟨s, hs⟩
  · obtain ⟨i, hi⟩ := nthPair_surj hgt
    obtain ⟨s, hs⟩ := grow_separates_pair c hub i
    rw [hi] at hs
    exact ⟨s, hs.symm⟩

/-! ### Yes-emitting

The lag at time `t` is `t − gdisp t` (it equals the phase's even lag).  It is non-decreasing in `t`
(an `R` keeps it, an `L` raises it by `2`) and at a phase start `tcur i` equals `lagcur i`, which
`→ ∞` (`sPick ≥ 2(i+1)`).  By the `±1`-walk IVT every displacement `D` is visited; choosing a weak
descent `D` at a time `t` past a phase with lag `> k₀.val` makes the `k₀`-signal fire. -/

/-- The displacement is a `±1` walk: `gdisp (t+1) ≤ gdisp t + 1`. -/
lemma gdisp_succ_le (t : ℕ) : gdisp c hub (t + 1) ≤ gdisp c hub t + 1 := by
  have hi : (gdisp c hub (t + 1) : ℤ) = (gdisp c hub t : ℤ) + (gmoves c hub t).delta := by
    rw [← cumDelta_gmoves, ← cumDelta_gmoves, cumDelta]
  have hd : (gmoves c hub t).delta ≤ 1 := by
    cases gmoves c hub t <;> decide
  have : (gdisp c hub (t + 1) : ℤ) ≤ (gdisp c hub t : ℤ) + 1 := by omega
  exact_mod_cast this

/-- `gdisp t ≤ t` (the displacement never exceeds elapsed time). -/
lemma gdisp_le_t (t : ℕ) : gdisp c hub t ≤ t := by
  induction t with
  | zero =>
      have h0 : gdisp c hub 0 = 0 := by
        unfold gdisp; rw [show gst c hub 0 = (0,0) from rfl]; exact dispAtIJ_zero c hub 0
      omega
  | succ n ih => have := gdisp_succ_le c hub n; omega

/-- **Lag monotonicity.**  `s ≤ t ⟹ s − gdisp s ≤ t − gdisp t` (lag never decreases). -/
lemma lag_mono {s t : ℕ} (hst : s ≤ t) :
    s - gdisp c hub s ≤ t - gdisp c hub t := by
  induction t with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge s (n + 1) with hlt | hge
      · have hsn : s ≤ n := by omega
        have hstep := gdisp_succ_le c hub n
        have hgle := gdisp_le_t c hub n
        have := ih hsn
        -- (n+1) - gdisp(n+1) ≥ n - gdisp n ≥ s - gdisp s
        omega
      · -- s = n+1
        have : s = n + 1 := by omega
        rw [this]

/-- The displacement at a phase start is `Dcur i`. -/
lemma gdisp_at_tcur (i : ℕ) : gdisp c hub (tcur c hub i) = Dcur c hub i := by
  unfold gdisp; rw [(gst_within c hub i).1]; exact dispAtIJ_zero c hub i

/-- **Lag at a phase start equals the phase's lag.**  `tcur i − gdisp (tcur i) = lagcur i`. -/
lemma lag_at_tcur (i : ℕ) : tcur c hub i - gdisp c hub (tcur c hub i) = lagcur c hub i := by
  rw [gdisp_at_tcur, tcur_eq]; omega

/-- **±1-walk IVT.**  If `D ≤ gdisp T`, then `gdisp` hits `D` at some time `t ≤ T`. -/
lemma gdisp_hits (D : ℕ) : ∀ T : ℕ, D ≤ gdisp c hub T → ∃ t : ℕ, t ≤ T ∧ gdisp c hub t = D := by
  intro T
  induction T with
  | zero =>
      intro hT
      have h0 : gdisp c hub 0 = 0 := by
        unfold gdisp; rw [show gst c hub 0 = (0,0) from rfl]; exact dispAtIJ_zero c hub 0
      refine ⟨0, le_refl _, ?_⟩
      rw [h0]; omega
  | succ n ih =>
      intro hT
      by_cases h : D ≤ gdisp c hub n
      · obtain ⟨t, ht, hgd⟩ := ih h; exact ⟨t, by omega, hgd⟩
      · refine ⟨n + 1, le_refl _, ?_⟩
        have := gdisp_succ_le c hub n
        omega

/-- **Yes-emitting.**  From every start cell, the trajectory eventually reads a "Yes". -/
lemma grow_yes (k₀ : ℕ+) :
    ∃ s : ℕ, signalOf c (position c (ofMoves (gmoves c hub)) (k₀ : ℤ) s) s = true := by
  set I := k₀.val with hI
  have hsP : I < sPick c hub I := by
    have := sPick_ge c hub I; omega
  obtain ⟨D, hDge, hwd⟩ := weak_descents_infinite c k₀ (tcur c hub (I + 1))
  have hgdT : D ≤ gdisp c hub (tcur c hub (D + 1)) := by
    rw [gdisp_at_tcur, Dcur_succ]
    have := Dfinal_ge_idx c hub D; omega
  obtain ⟨t, _, hgt⟩ := gdisp_hits c hub D (tcur c hub (D + 1)) hgdT
  have ht_ge_D : D ≤ t := by have := gdisp_le_t c hub t; omega
  have ht_ge : tcur c hub (I + 1) ≤ t := le_trans hDge ht_ge_D
  have hlag := lag_mono c hub ht_ge
  rw [lag_at_tcur, lagcur_succ] at hlag
  rw [hgt] at hlag
  refine ⟨t, ?_⟩
  rw [signalOf_ofMoves_eq c (gmoves c hub) k₀ t D (by rw [cumDelta_gmoves]; exact_mod_cast hgt)]
  rw [decide_eq_true_eq]
  have hcsd : (c (cellAt k₀ D)).val ≤ k₀.val + D := by
    rw [cellAt_val] at hwd; exact hwd
  omega

/-! ### Assembly: unbounded-above ⟹ Bob wins -/

/-- **The growing-lag separating trajectory localizes every start.**  Combining safety
    (`grow_safe`), separation (`grow_separates`), and Yes (`grow_yes`) via `ofMoves_localizes`. -/
theorem grow_localizes : ∀ k₀ : ℕ+, Localizes c (ofMoves (gmoves c hub)) k₀ :=
  ofMoves_localizes c (gmoves c hub) (grow_safe c hub) (grow_separates c hub) (grow_yes c hub)

end GrowStair

/-- **Unbounded-above ⟹ Bob wins (axiom-clean).**  If `c` is not eventually identity and is *not*
    bounded above (no `B` bounds `(c n).val ≤ n.val + B`), Bob wins via the growing-lag staircase
    `GrowStair.gmoves`, whose per-pair separators come from the axiom-clean `q2even` (`Q2Even.lean`).

    This closes the last `sorry` of `main`'s winning direction.  The non-EI hypothesis `h` is retained
    for the dispatch interface in `Answer.main`; the proof itself needs only unboundedness above (the
    growing-lag staircase is signal-independent and uses only `q2even` + `weak_descents_infinite`). -/
theorem notEI_unboundedAbove_BobWins (c : Perm) (_h : ¬ EventuallyIdentity c)
    (hub : ¬ ∃ B : ℕ, ∀ n : ℕ+, (c n).val ≤ n.val + B) : BobWins c :=
  localizes_BobWins (ofMoves_neverGuesses (GrowStair.gmoves c hub)) (GrowStair.grow_localizes c hub)

-- Axiom audit.  The unbounded-above winner is `sorry`-free: `[propext, Classical.choice, Quot.sound]`.
#print axioms notEI_unboundedAbove_BobWins

end TrolleyRetrieval
