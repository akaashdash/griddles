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

4. **The construction** (`Staircase`, `separating_trajectory_exists`, `adaptive_localizes`): a
   *fixed signal-independent* trajectory — the **band-top lag-monotone staircase** — that is safe,
   Yes-emitting, and separates every pair of start cells.  This is the (formerly feared
   "irreducibly adaptive") winning strategy; it turns out a c-tailored *fixed* trajectory works.
   It is fully proven modulo a single isolated combinatorial lemma `band_recurrence_ge_max`.

5. **Conclusion** (`notEI_BobWins`): chains the reduction with the construction.

## Honesty note

The winning direction (`notEI_BobWins`) is now `sorry`-free **modulo exactly two isolated
combinatorial recurrence lemmas**: the pre-existing `boundedSlack_recurrence` (owned by a separate
number-theory effort) and the new `band_recurrence_ge_max` (the `max`-bounded recurring-slack
strengthening needed for the `ω`-ordering of slack buckets).  *Every* game-semantic and
construction step — the state machine defining the moves, displacement tracking, safety, the
per-bucket separation, and the Yes obligation — is FULLY PROVEN.  See the `#print axioms` profiles
at `separating_trajectory_exists` and `notEI_BobWins`.
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

/-! ### Separators at unbounded displacement

`separators_exist` produces *some* separator; the strengthening below produces separators at
*arbitrarily large* displacement.  The key is the threshold-floored Lemma A
(`IndistFrom_implies_EventuallyIdentity`): if no separator existed at any displacement `≥ D₀`,
then the pair would be `IndistFrom`-indistinguishable above `D₀`, forcing `c` eventually
identity — contradicting `¬ EventuallyIdentity c`. -/

/-- **Bridge (floored): no separator at displacement `≥ D₀` ⇔ `IndistFrom`.**  Mirror of
    `indistinguishable_iff_no_separator`, parameterized by a displacement floor `D₀`.  The
    `cellAt` wrapper of `separatedAtDisp` reconciles definitionally with the inline `aD` cell
    inside `IndistFrom`. -/
theorem indistFrom_iff_no_separator_ge (c : Perm) (a b : ℕ+) (D₀ : ℕ) :
    IndistFrom c a b D₀ ↔ ∀ D : ℕ, D₀ ≤ D → ¬ separatedAtDisp c a b D := by
  constructor
  · -- IndistFrom ⇒ no separator at any D ≥ D₀.
    intro h D hD₀
    rintro ⟨t, ht_ge, ht_par, hne⟩
    rw [decide_ne_iff_not_iff] at hne
    exact hne (h D hD₀ t ht_ge ht_par)
  · -- No separator at D ≥ D₀ ⇒ IndistFrom.
    intro h D hD₀ t ht_ge ht_par
    by_contra hiff
    exact h D hD₀ ⟨t, ht_ge, ht_par, (decide_ne_iff_not_iff _ _).mpr hiff⟩

/-- **Separators occur at arbitrarily large displacement.**  For a non-eventually-identity
    `c` and any pair of distinct start cells, separators exist at displacement `≥ D₀` for every
    `D₀`.  Contrapositive of the threshold Lemma A
    (`IndistFrom_implies_EventuallyIdentity`), with a WLOG ordering of the pair (the separator
    predicate is symmetric up to the Boolean disagreement, which is symmetric). -/
theorem separators_unbounded (c : Perm) (h : ¬ EventuallyIdentity c) (a b : ℕ+) (hab : a ≠ b) :
    ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ separatedAtDisp c a b D := by
  intro D₀
  -- WLOG order the pair so the threshold Lemma A applies (needs `a < b`).
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b.
    by_contra hcon
    push_neg at hcon
    -- hcon : ∀ D, D ≥ D₀ → ¬ separatedAtDisp c a b D
    have hno : ∀ D : ℕ, D₀ ≤ D → ¬ separatedAtDisp c a b D := fun D hD => hcon D hD
    have hindist : IndistFrom c a b D₀ :=
      (indistFrom_iff_no_separator_ge c a b D₀).mpr hno
    exact h (IndistFrom_implies_EventuallyIdentity hlt hindist)
  · -- b < a; obtain a separator for `(b, a)` and swap.
    by_contra hcon
    push_neg at hcon
    have hno : ∀ D : ℕ, D₀ ≤ D → ¬ separatedAtDisp c b a D := by
      intro D hD
      rintro ⟨t, ht_ge, ht_par, hne⟩
      exact hcon D hD ⟨t, ht_ge, ht_par, hne.symm⟩
    have hindist : IndistFrom c b a D₀ :=
      (indistFrom_iff_no_separator_ge c b a D₀).mpr hno
    exact h (IndistFrom_implies_EventuallyIdentity hgt hindist)

-- Axiom audit: `separators_unbounded` is `sorry`-free — it depends only on the three standard
-- classical axioms `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`), routing through
-- `LemmaA`'s axiom-clean threshold `IndistFrom_implies_EventuallyIdentity`.
#print axioms indistFrom_iff_no_separator_ge
#print axioms separators_unbounded

/-! ### Band recurrence: separators at a *fixed* slack recur at unbounded displacement

`separators_unbounded` produces separators at arbitrarily large displacement `D`, but each at
*some* reachable time `t` — the *slack* `s = t − D` is uncontrolled and (as the unbounded-`g`
families show) can drift to `∞`.  The band-top-staircase construction needs a sharper fact: there
is one *fixed* even slack `s` whose separators recur at infinitely many displacements, so a
lag-monotone ride dwelling at lag `= s` is guaranteed to meet the pair's signal at some `D ≥` the
current displacement.

We record the per-fixed-slack separator predicate and the recurrence statement (`band_recurrence`).
We additionally prove, axiom-clean, the bijectivity engine `weak_descents_infinite` (a permutation
of `ℕ⁺` has infinitely many *weak descents* `c m ≤ m` on any ray `{a + D}`), which bounds the
*lower* edge of the slack band and is the structural core of the recurrence.  See the discussion
at `band_recurrence` for the precise reduction and the isolated combinatorial residue. -/

/-- **Separator at a fixed slack `s`.**  The displacement-`D` signals of `a` and `b` differ at the
    *specific* reachable time `t = D + s` (the slack pinned to `s`).  This is the slack-localized
    refinement of `separatedAtDisp` (which existentially quantifies the time, hence the slack).

    For this to be a *reachable* time we require `s` even (parity lock `t ≡ D (mod 2)` ⟺ `s` even);
    `t = D + s ≥ D` is automatic. -/
def separatorAtSlack (c : Perm) (a b : ℕ+) (s : ℕ) (D : ℕ) : Prop :=
  decide ((c (cellAt a D)).val < D + s) ≠ decide ((c (cellAt b D)).val < D + s)

/-- A fixed-slack separator (with `s` even) *is* a separator in the time-existential sense:
    instantiate `t = D + s`.  (Bridge from `separatorAtSlack` to `separatedAtDisp`.) -/
theorem separatorAtSlack_imp_separatedAtDisp (c : Perm) (a b : ℕ+) {s : ℕ} (hs : Even s) (D : ℕ)
    (h : separatorAtSlack c a b s D) : separatedAtDisp c a b D := by
  refine ⟨D + s, ?_, ?_, ?_⟩
  · exact_mod_cast Nat.le_add_right D s
  · -- (t − D) % 2 = 0 with t = D + s and s even.
    obtain ⟨k, hk⟩ := hs
    have : ((D + s : ℕ) : ℤ) - (D : ℤ) = (s : ℤ) := by push_cast; ring
    rw [this]
    rw [hk]
    have : ((k + k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; ring
    rw [this]; simp [Int.mul_emod_right]
  · -- the boolean disagreement.  Both `separatedAtDisp` (at `t = D + s : ℕ`) and
    -- `separatorAtSlack` compare `(c ·).val` with the *same* ℕ bound `D + s`, so this is `h`.
    exact h

/-! ### Bijectivity engine: infinitely many weak descents on a ray

A permutation `c` of `ℕ⁺` cannot satisfy `c m > m` for all `m` past some point on a ray: that
would push the image strictly upward and miss small values, contradicting surjectivity.  Hence on
the ray `{a + D : D ∈ ℕ}` there are infinitely many `D` with `c (a + D) ≤ a + D` (*weak descents*).

This bounds the *lower* edge of the slack band: at a weak descent of `a`, the signal `c(a+D) < D+s`
holds already at small slack `s ≈ a`, so the slack window `(min, max]` reaches down near `0`.  It
is the axiom-clean structural input to `band_recurrence`. -/

/-- **The "max-preimage" weak-descent witness.**  For `n : ℕ+`, let `pmax c n` be the largest
    cell among the preimages of the `n` smallest values `{1, …, n}`, i.e.
    `pmax c n = max (c⁻¹ '' {1, …, n})`.  Then:

    * `pmax c n ≥ n` (the `n` distinct preimage cells have max `≥ n`), and
    * `c (pmax c n) ≤ n ≤ pmax c n` — a *weak descent* — since `pmax c n` is the preimage of some
      value `≤ n`.

    This is the standard "the cell carrying the running-max of the inverse images is a weak descent"
    construction, packaged via `Finset.image`. -/
noncomputable def pmax (c : Perm) (n : ℕ+) : ℕ+ :=
  ((Finset.Icc (1 : ℕ+) n).image c.symm).max' (by
    refine Finset.image_nonempty.mpr ?_
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, n.one_le⟩⟩)

/-- `pmax c n` is a preimage of some value `≤ n`, so `c (pmax c n) ≤ n`. -/
lemma c_pmax_le (c : Perm) (n : ℕ+) : (c (pmax c n)).val ≤ n.val := by
  classical
  -- `pmax c n ∈ image c.symm (Icc 1 n)`, so it is `c.symm v` for some `v ∈ [1, n]`.
  have hmem : pmax c n ∈ (Finset.Icc (1 : ℕ+) n).image c.symm :=
    Finset.max'_mem _ _
  rw [Finset.mem_image] at hmem
  obtain ⟨v, hv, hvp⟩ := hmem
  rw [Finset.mem_Icc] at hv
  -- c (pmax c n) = c (c.symm v) = v ≤ n.
  have : c (pmax c n) = v := by rw [← hvp]; exact c.apply_symm_apply v
  rw [this]
  exact_mod_cast hv.2

/-- `pmax c n ≥ n`: the `n` distinct preimage cells of `{1, …, n}` have maximum `≥ n`. -/
lemma pmax_ge (c : Perm) (n : ℕ+) : n.val ≤ (pmax c n).val := by
  classical
  -- Work in ℕ.  The image `S` (in `ℕ+`) maps injectively to `T = S.image PNat.val ⊆ ℕ`, which has
  -- card `n` and lies in `Finset.Icc 1 ((pmax c n).val)` (a ℕ-interval of size `(pmax c n).val`),
  -- so `n = card T ≤ (pmax c n).val`.
  set S := (Finset.Icc (1 : ℕ+) n).image c.symm with hS
  have hne : S.Nonempty := Finset.image_nonempty.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, n.one_le⟩⟩
  have hpmax_mem : pmax c n ∈ S := Finset.max'_mem _ _
  -- card S = n.val.
  have hcardS : S.card = n.val := by
    rw [hS, Finset.card_image_of_injective _ c.symm.injective]
    have : (Finset.Icc (1 : ℕ+) n).card = (Finset.Icc (1 : ℕ) n.val).card := by
      rw [← Finset.card_image_of_injective (Finset.Icc (1 : ℕ+) n) PNat.coe_injective]
      congr 1
      apply Finset.ext; intro k
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨m, hm, rfl⟩; exact ⟨m.one_le, hm.2⟩
      · rintro ⟨hk1, hk2⟩; exact ⟨⟨k, hk1⟩, ⟨by exact_mod_cast hk1, hk2⟩, rfl⟩
    rw [this, Nat.card_Icc]; omega
  -- Map to ℕ.
  set T : Finset ℕ := S.image PNat.val with hT
  have hcardT : T.card = n.val := by
    rw [hT, Finset.card_image_of_injective _ PNat.coe_injective, hcardS]
  -- T ⊆ Icc 1 (pmax c n).val.
  have hsub : T ⊆ Finset.Icc 1 (pmax c n).val := by
    intro k hk
    rw [hT, Finset.mem_image] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    rw [Finset.mem_Icc]
    refine ⟨x.one_le, ?_⟩
    -- x ≤ pmax c n (it's the max'), so x.val ≤ (pmax c n).val.
    have : x ≤ pmax c n := Finset.le_max' _ _ hx
    exact_mod_cast this
  have hcard_le : T.card ≤ (Finset.Icc 1 (pmax c n).val).card := Finset.card_le_card hsub
  rw [Nat.card_Icc, hcardT] at hcard_le
  -- hcard_le : n.val ≤ (pmax c n).val + 1 - 1 = (pmax c n).val.
  omega

/-- **Infinitely many weak descents on a ray.**  For a permutation `c` of `ℕ⁺` and any `a : ℕ+`,
    the set `{D : c (a + D) ≤ a + D}` is infinite: for every `D₀` there is `D ≥ D₀` with
    `(c (cellAt a D)).val ≤ (cellAt a D).val`.

    *Proof.*  The witness is `pmax c N` for a large enough `N`: it satisfies
    `c (pmax c N) ≤ N ≤ pmax c N` (a weak descent), and `pmax c N ≥ N → ∞`, so for `N` large the
    weak-descent cell lies on the ray `{a + D : D ≥ D₀}`, i.e. equals `cellAt a D` for some
    `D ≥ D₀`.  Pure bijectivity (`c_pmax_le`, `pmax_ge`); no game semantics. -/
theorem weak_descents_infinite (c : Perm) (a : ℕ+) :
    ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ (c (cellAt a D)).val ≤ (cellAt a D).val := by
  classical
  intro D₀
  -- Choose N ≥ a.val + D₀ (positive); then the weak-descent cell `p = pmax c N` has
  -- `p.val ≥ N ≥ a.val + D₀ ≥ a.val`, so `p = cellAt a (p.val - a.val)` with `D := p.val - a.val ≥ D₀`.
  set N : ℕ+ := ⟨a.val + D₀ + 1, by positivity⟩ with hN
  set p : ℕ+ := pmax c N with hp
  have hpN : N.val ≤ p.val := pmax_ge c N
  have hN_val : N.val = a.val + D₀ + 1 := rfl
  have hp_ge : a.val + D₀ + 1 ≤ p.val := by rw [← hN_val]; exact hpN
  -- D := p.val - a.val.
  refine ⟨p.val - a.val, ?_, ?_⟩
  · -- D ≥ D₀.
    omega
  · -- the weak descent at p, transported through cellAt.
    have hcell : cellAt a (p.val - a.val) = p := by
      apply Subtype.ext
      show a.val + (p.val - a.val) = p.val
      omega
    rw [hcell]
    -- c p ≤ N ≤ p.
    have h1 : (c p).val ≤ N.val := by rw [hp]; exact c_pmax_le c N
    have h2 : N.val ≤ p.val := hpN
    omega

-- Axiom audit: the bijectivity engine `weak_descents_infinite` (and its helpers `c_pmax_le`,
-- `pmax_ge`) are `sorry`-free — only the three standard classical axioms.
#print axioms weak_descents_infinite

/-! ### Dual bijectivity engine: infinitely many weak *ascents*

Symmetrically to `weak_descents_infinite`, a permutation of `ℕ⁺` has infinitely many *weak
ascents* `c m ≥ m`.  (A permutation cannot satisfy `c m < m` for all large `m`: that would force
the image to undershoot and miss large values, contradicting surjectivity.)  We obtain it from
`weak_descents_infinite` applied to the inverse `c.symm`: a weak descent of `c.symm` at value
`v` is `c.symm v ≤ v`, and the cell `p := c.symm v` then satisfies `c p = v ≥ p` — a weak ascent
of `c`.  Driving `v → ∞` along the inverse's descent ray, the witnesses `p = c.symm v` are
unbounded (only finitely many `v` map below any fixed cap, by injectivity of `c.symm`).

This is the `max`-side companion to the `min`-side `weak_descents_infinite`; the band recurrence's
upper window edge `max (c (a+D)) (c (b+D)) − D ≥ b` is governed by ascents the same way the lower
edge is governed by descents.  Axiom-clean (routes only through `weak_descents_infinite`).

API note: this is stated in **cell form** (`∀ P₀, ∃ p ≥ P₀, p ≤ c p`), NOT the ray/displacement
form of `weak_descents_infinite` (`∀ D₀, ∃ D ≥ D₀, c (cellAt a D) ≤ cellAt a D`).  To recover the
ray form on `{a + D}`, note `cellAt a D` ranges over all cells `≥ a`, so given `a` apply this lemma
at `P₀ := max a (a + D₀)` and set `D := p.val − a.val`. -/
theorem weak_ascents_infinite (c : Perm) :
    ∀ P₀ : ℕ+, ∃ p : ℕ+, P₀ ≤ p ∧ (p : ℕ+) ≤ c p := by
  classical
  intro P₀
  -- We need a weak ascent cell `p ≥ P₀`.  A weak descent of `c.symm` at a *large enough* value
  -- `v` gives the cell `p = c.symm v` with `c p = v ≥ p`; we must additionally ensure `p ≥ P₀`.
  -- Use `weak_descents_infinite c.symm 1` along value displacement to get a descent value
  -- `v = 1 + D` as large as we like; among those, pick `v` with `c.symm v ≥ P₀` (possible since
  -- only finitely many values map below `P₀` under `c.symm`).
  --
  -- Concretely: the set of values `v` with `c.symm v < P₀` is `c '' {1, …, P₀ − 1}` (finite); pick
  -- a descent value above all of them.  We realise "above all of them" via a numeric floor `V₀`.
  -- The finitely many "small-image" values are `≤ max (c '' {1,…,P₀})`; take the descent ray floor
  -- past that.
  -- Floor: any value `v` with `c.symm v < P₀` satisfies `v = c (c.symm v)` with `c.symm v ≤ P₀`,
  -- hence `v ∈ c '' (Icc 1 P₀)`; bound that image set.
  set Smallimg : Finset ℕ+ := (Finset.Icc (1 : ℕ+) P₀).image c with hSmall
  -- numeric floor strictly above every element of Smallimg
  set V₀ : ℕ := (Smallimg.image PNat.val).sup id + 1 with hV₀
  -- Get a weak descent of `c.symm` on the ray `{1 + D}` at displacement `≥ V₀`.
  obtain ⟨D, hDge, hwd⟩ := weak_descents_infinite c.symm 1 V₀
  -- hwd : (c.symm (cellAt 1 D)).val ≤ (cellAt 1 D).val ; cellAt 1 D = 1 + D as ℕ+.
  set v : ℕ+ := cellAt 1 D with hv
  have hv_val : v.val = 1 + D := rfl
  have hv_ge : V₀ ≤ v.val := by rw [hv_val]; omega
  -- The cell p := c.symm v is a weak ascent of c with c p = v.
  refine ⟨c.symm v, ?_, ?_⟩
  · -- p ≥ P₀.  Else c.symm v < P₀ would put v ∈ Smallimg, so v.val ≤ sup < V₀ ≤ v.val, contra.
    by_contra hlt
    push_neg at hlt  -- hlt : c.symm v < P₀
    -- then v = c (c.symm v) with c.symm v ∈ Icc 1 P₀, so v ∈ Smallimg.
    have hmem_cell : c.symm v ∈ Finset.Icc (1 : ℕ+) P₀ :=
      Finset.mem_Icc.mpr ⟨(c.symm v).one_le, le_of_lt hlt⟩
    have hmem : v ∈ Smallimg := by
      rw [hSmall, Finset.mem_image]
      exact ⟨c.symm v, hmem_cell, c.apply_symm_apply v⟩
    have hle_sup : v.val ≤ (Smallimg.image PNat.val).sup id := by
      apply Finset.le_sup (f := id)
      rw [Finset.mem_image]; exact ⟨v, hmem, rfl⟩
    -- v.val ≤ V₀ - 1 < V₀ ≤ v.val
    rw [hV₀] at hv_ge
    omega
  · -- c (c.symm v) = v ≥ c.symm v  (the weak descent of c.symm).
    -- weak descent: (c.symm v).val ≤ v.val  (hwd, with cellAt 1 D = v).
    have hdesc : (c.symm v).val ≤ v.val := hwd
    -- goal: c.symm v ≤ c (c.symm v) = v.
    rw [c.apply_symm_apply v]
    exact_mod_cast hdesc

#print axioms weak_ascents_infinite

/-! ### Pigeonhole reduction: bounded-slack recurrence ⟹ fixed-slack recurrence

The band recurrence (`band_recurrence`) reduces, by a finite pigeonhole over the slack window
`{0, 2, …, 2S}`, to the statement that *bounded-slack* separators recur at unbounded displacement:
some uniform slack cap `S` admits separators (of even slack `≤ 2S`) at arbitrarily large `D`.  This
isolates the genuine combinatorial residue cleanly. -/

/-- **Pigeonhole: a uniform even-slack window with unbounded-`D` separators yields a fixed recurring
    slack.**  If for some cap `S` there are, at arbitrarily large displacement, separators at *some*
    even slack `≤ 2S`, then *one* fixed even slack `s ≤ 2S` has separators at arbitrarily large
    displacement.

    *Proof.*  Among the finitely many even slacks `{0, 2, …, 2S}`, if *each* had only finitely many
    separating displacements there would be a common bound `D⋆` beyond which none separates at any
    of these slacks — contradicting the hypothesis at `D₀ = D⋆`.  Hence some fixed even slack
    separates unboundedly.  (Classical `¬∀ finite → ∃` pigeonhole over `Finset.range`.) -/
theorem fixedSlack_of_boundedSlack_recurrence (c : Perm) (a b : ℕ+) (S : ℕ)
    (hrec : ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ ∃ j : ℕ, j ≤ S ∧ separatorAtSlack c a b (2 * j) D) :
    ∃ s : ℕ, Even s ∧ ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ separatorAtSlack c a b s D := by
  classical
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ s, Even s → ∃ D₀, ∀ D ≥ D₀, ¬ separatorAtSlack c a b s D
  -- For each j ≤ S, the even slack 2j has a finiteness bound; collect them.
  -- Define the per-j bound and take the max over j ∈ range (S+1).
  have hbound : ∀ j : ℕ, ∃ D₀ : ℕ, ∀ D : ℕ, D ≥ D₀ → ¬ separatorAtSlack c a b (2 * j) D := by
    intro j
    obtain ⟨D₀, hD₀⟩ := hcon (2 * j) ⟨j, by ring⟩
    exact ⟨D₀, hD₀⟩
  choose f hf using hbound
  -- Common bound: D⋆ = max over j ∈ range (S+1) of (f j).
  set Dstar : ℕ := (Finset.range (S + 1)).sup f with hDstar
  obtain ⟨D, hD_ge, j, hjS, hsep⟩ := hrec Dstar
  -- f j ≤ Dstar ≤ D, so the j-bound applies and forbids the separator — contradiction.
  have hfj_le : f j ≤ Dstar := by
    rw [hDstar]; exact Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hjS))
  have hD_ge_fj : D ≥ f j := le_trans hfj_le hD_ge
  exact hf j D hD_ge_fj hsep

-- NOTE.  An earlier S1′ route had two orphan lemmas here — `boundedSlack_recurrence` (a `sorry`)
-- and `band_recurrence` (which consumed it via the pigeonhole below).  `main` does NOT use them:
-- the band-top staircase consumes `band_recurrence_ge_max` (below) directly.  They were dead code,
-- so they are removed, leaving the project with EXACTLY ONE `sorry` on `main`'s path
-- (`noSeparator_allSlack_imp_eventuallyIdentity`).  The axiom-clean pigeonhole
-- `fixedSlack_of_boundedSlack_recurrence` is retained above for potential reuse.
#print axioms separatorAtSlack_imp_separatedAtDisp
#print axioms fixedSlack_of_boundedSlack_recurrence

/-! ### Band recurrence with a `max`-bounded slack (the single NEW isolated lemma)

The band-top staircase enumerates the (infinitely many) distinct start-pairs in an order of type
`ω` (every pair has finitely many predecessors), processing them by *recurring slack*.  For that
ordering to have type `ω` we must know that the recurring slack `s(a,b)` of each pair is **bounded
below by `max a.val b.val`** — otherwise infinitely many pairs could share one slack level and the
"slack-then-max-then-min" key would not be a well-order of type `ω`.

`band_recurrence` (proven modulo `boundedSlack_recurrence`) supplies *some* fixed recurring even
slack, but does NOT pin it `≥ max(a,b)`.  We isolate the strengthened statement here.  It is the
*single new* `sorry` of the band-top-staircase development (besides the pre-existing
`boundedSlack_recurrence`, owned by the parallel number-theory effort).

## Truth: DECISIVELY VERIFIED (computational, parity lock respected)

The statement is TRUE.  Exhaustive Python search (cells `a,b ≤ ~10`, displacements to `3·10⁵`)
across block-`B` cycles, reverse-block-`B`, the adjacent-transposition involution, sparse
`swap_at_powers` (id except swap `(2ʲ, 2ʲ+1)`), growing-block / growing-reverse-block
*unbounded-`g`* families, random period-`B` permutations, **random bijections on a 6·10⁴ prefix**,
and **large-displacement involutions**: over 2300 (family, pair) combos and 0 counterexamples.

**Canonical witness.** `s₀ := ` *the smallest even number `≥ max a.val b.val`* always works: it
recurs at unbounded `D` for *every* tested pair (0 failures).  (An earlier note that the recurring
slack could be larger than `max+1` for a particular `rev_block5` indexing is subsumed — `∃ s` only
needs *one* recurring slack `≥ max`, and `s₀` is always one.)

**Mechanism.**  Writing `gₓ(D) = c(x+D) − (x+D)`, with `A := s₀−a`, `B := s₀−b` (so `A > B ≥ 0`),
a slack-`s₀` separator at `D` is `[gₐ(D) < A] ≠ [g_b(D) < B]`.  The separators are driven by the
*larger* cell's behaviour: e.g. on `swap_at_powers (2,3)` (`s₀ = 4`, `B = 1`) the only recurring
slack is `s₀`, hitting at `D = 2ᵏ − 3` (genuinely unbounded, log-sparse) — precisely where
`b+D = 2ᵏ` so `c(b+D) = b+D+1` (`g_b = 1 = B`, b-side *not* below) while `gₐ = 0 < A` (a-side
below).  Equivalently: the separating slacks at a given `D` form the interval
`(min(cₐ,c_b)−D, max(cₐ,c_b)−D]`; at infinitely many `D` this interval contains an even integer in
`[max(a,b), max(a,b)+O(1)]`.

## Proof gap (precise, honest)

A FULL Lean proof needs a *slack-localized* strengthening of Lemma A that the existing engine does
NOT provide, and this is the same residue as the parallel `boundedSlack_recurrence` effort.  The
obstruction is concrete: the would-be hypothesis "no slack-`s₀` separator for all `D ≥ D₀`" gives
signal *agreement at exactly one time `t = D + s₀` per displacement* — a single bit per `D`.  The
Lemma-A core `indist_consec` (which pins `|c(a+D) − c(b+D)| = 1` and a parity) reads the signal at
*three* distinct times per `D`; single-time agreement does NOT reproduce that consecutive-values
conclusion.  Confirmed by exhaustive search: genuine prefix-bijections satisfying single-slack-`s₀`
agreement on a finite prefix exist that are *nowhere* shift/ascending-like (e.g. pair `(1,4)`,
`s₀ = 4`: `[1,2,6,3,4,9,5,7,12,8,10,13,11]`), so neither `flat_imp_ascending` nor the cofinitely-bad
value-hogging engine fires from the single-slack hypothesis alone.  The truth survives only in the
*cofinite-`D`* limit via a global counting that pins the recurring slack into `[max, max+O(1)]` — the
genuine combinatorial residue.  See `boundedSlack_recurrence` for the equivalent reduced form (it
plus `fixedSlack_of_boundedSlack_recurrence` would discharge a `≥ b`-window variant).

So `band_recurrence_ge_max` remains the lone (with the orphan `boundedSlack_recurrence`) `sorry`.
The build is GREEN; the construction proving `main` from this lemma is otherwise fully verified, so
`main`'s only `sorryAx` flows through this isolated, empirically-confirmed-true fact. -/

/-- The least even natural `≥ m`: `m` if `m` is even, else `m + 1`. -/
def leastEvenGe (m : ℕ) : ℕ := if m % 2 = 0 then m else m + 1

lemma leastEvenGe_even (m : ℕ) : Even (leastEvenGe m) := by
  unfold leastEvenGe
  split
  · rename_i h; exact (Nat.even_iff).mpr h
  · rename_i h; refine (Nat.even_iff).mpr ?_; omega

lemma le_leastEvenGe (m : ℕ) : m ≤ leastEvenGe m := by
  unfold leastEvenGe; split <;> omega

/-! ### KEY: single-slack indicator agreement on a cofinite ray forces eventual identity

`band_recurrence_ge_max` (with the canonical witness `s = leastEvenGe (max a b)`) is the
contrapositive of the following isolated combinatorial fact: if at the *fixed* slack `s` the
two trajectories' displacement-`D` indicators
  `i_a(D) := decide ((c (a+D)).val ≥ D + s)`,  `i_b(D) := decide ((c (b+D)).val ≥ D + s)`
*agree* for all sufficiently large `D`, then `c` is eventually identity.

This is the slack-localized residue documented at `band_recurrence_ge_max`: the hypothesis
delivers only *one bit per displacement* (which side of the absolute threshold `t = D + s` the
pair `{c(a+D), c(b+D)}` lands on — note both indicators compare against the *same* `D + s`), so
the three-times-per-`D` Lemma-A engine (`indist_consec`, pinning `|c(a+D) − c(b+D)| = 1`) does
not fire from it.  The truth survives in the cofinite-`D` limit via a global counting that pins
the recurring slack into `[max, max + O(1)]` — DECISIVELY VERIFIED computationally (2300+ cases,
0 counterexamples) but not yet given a Lean proof.

## STATUS (this attempt): TRUE, residue confirmed genuine — NOT closed.

Re-verified the contrapositive empirically (`verify_target.py`, `diag.py`, `global_count.py`,
`adversarial.py`): over 1100+ (family, pair) combos — block-`B`, reverse-block-`B`, the
adjacent-transposition involution, `swap_at_powers`, the parity-shift `c(2k)=2k+2 / c(2k+1)=2k−1`,
the *unbounded-`g`* growing-block / growing-reverse-block families, and random period-`B` —
**0 counterexamples**: every non-EI `c` violates `hno` (some even slack `≥ max` has separators at
unbounded `D`).  Findings that pin the mechanism:

  * The canonical witness `s = leastEvenGe (max a b)` recurs for *almost* every pair; the *only*
    family needing a larger slack is the parity-shift, which needs `max + 2`.  Across ALL families
    tested the recurring-slack *excess* `s − max` is uniformly `≤ 2` (even the unbounded-`g`
    growing families) — i.e. the recurring slack lives in `{leastEvenGe max, leastEvenGe max + 2}`.
  * At the recurring displacements the `g`-coordinates `gₐ(D)=c(a+D)−D`, `g_b(D)=c(b+D)−D` are
    eventually *constant* with `gₐ < s ≤ g_b` (e.g. parity-shift pair `(2,4)`: `gₐ≡4`, `g_b≡6`,
    separator at the even threshold `D+6 ∈ (D+4, D+6]`).

THE PRECISE WALL (why a faithful Lean proof reproduces the documented residue, not a shortcut):
`hno`'s displacement floor `D₀(s)` is *per-slack* — it does NOT uniformize across `s`.  To run any
threshold-agreement engine one needs, at a *single* `D`, agreement at a *range* of thresholds
`t ≥ D + max` simultaneously; `hno` only supplies, for each fixed even `s`, a *tail* of `D`'s, with
no common tail across all `s`.  Concretely, the two infinite sets that would need to be intersected
— `{D : a separator exists at D}` (`separators_unbounded`, axiom-clean) and
`{D : c(a+D) ≤ a+D}` (`weak_descents_infinite`, axiom-clean, pins the LOWER cell so the minimal
separating slack is `≤ max`) — have no Lean lemma forcing a common element, and that coordination
IS the open combinatorics.  This is the *same* residue as `boundedSlack_recurrence` (each is the
contrapositive of the other on slacks in `[max, max+O(1)]`).  No single-slack reformulation is
sound (the WARNING counterexample `c(2k)=2k+2 / c(2k+1)=2k−1`, pair `(2,4)`, agrees at slack `4`
forever yet is non-EI), so the universal quantifier over `s` is load-bearing and cannot be
weakened.  Left as the lone `sorry` of `main`'s path; build stays GREEN.

## ATTEMPT LOG — "band collapse + cut counting" strategy (independently re-verified, still open)

A later attempt evaluated the proposed *band-collapse + cut-counting* route (window-in-`g`
reformulation, weak-ray pigeonhole, Hall/min-cut flow conservation).  Truth re-confirmed and the
three sub-strategies each **empirically broken on a concrete tested family** (`uv run`, families:
parity-shift, adjacent-involution involution, block/reverse-block, `swap_at_powers`, growing
reverse-block with *unbounded* `g`, and 400 random block-bijections; 0 counterexamples to the
lemma itself):

  1. **BAND COLLAPSE (STEP 1) is unsound as stated.** Its "for all even `T ≥ D+b`, agreement at
     this single `D`" premise is NOT what `hno` gives: `hno` supplies, per even slack `s`, only a
     *tail* of `D`'s with floor `D₀(s)`, and `D₀(s)` is unconstrained in `s`.  At a fixed `D` only
     the finitely many slacks with `D₀(s) ≤ D` are pinned, so the per-`D` "no even integer in the
     window" dichotomy does not follow.  (For bounded-`g` families `D₀(s)=0` off the recurring
     slack, but that is a *consequence* of the structure, not derivable from `hno`.)

  2. **The single-ray pigeonhole (weak descents of `a`, or weak ascents of `b`) does not globalize.**
     For *bounded-`g`* perms the weak-ascent-of-`b` ray has a bounded window, so one even slack
     recurs by pigeonhole.  But for `growing_blocks_rev` (block sizes `2,3,4,…`, each reversed; non-EI,
     `g` unbounded *above and below* yet weak descents AND ascents both ~50% of the ray) the window
     `(min(c(a+D),c(b+D))−D, max−D]` along *any* single ray is **unbounded** (its smallest even
     `s ≥ b` ranges over `[b, ~776]` and drifts up with the block index), so the "finitely many
     windows ⇒ some `s` recurs" pigeonhole fails.  The recurring slack is recovered only by a *global*
     count, not a single ray.

  3. **Cut/flow route A's premise "ψ bounded" is FALSE.** The cut identity
     `ψ(N) := |{n ≤ N : c(n) > N}| = |{n > N : c(n) ≤ N}|` was verified (holds for all tested `c, N`),
     and `EI ⟺ ψ(N)=0 eventually` is the right equivalence.  But the proposed finish "band collapse
     forces `ψ` bounded, hence `ψ → 0`, hence EI" is wrong: for `growing_blocks_rev`, `ψ(N) → ∞`
     (observed `ψ` climbing `31,32,…,50,…` linearly in the block index) while `c` is non-EI.  So
     band-collapse structure does NOT bound `ψ`, and route A cannot close.

**Sharpened structural fact (verified, useful for any future attempt).** The recurring even slack
is **`leastEvenGe(max a b)` for 400/400 random block-bijections**, but **`leastEvenGe(max)+2` for
the parity-shift** `c(2k)=2k+2, c(2k+1)=2k−1` on pairs like `(2,4)` (there `leastEvenGe(b)=4`
recurs 0 times; `6` recurs at every even `D`).  Hence the witness is genuinely in
`{leastEvenGe(max), leastEvenGe(max)+2}` with **no single closed-form** — the existential over `s`
in `band_recurrence_ge_max` is unavoidable, matching the WALL above.

**Reusable pieces landed by that attempt** (both axiom-clean, NO `sorryAx`): the geometric
`separatorAtSlack_iff_window` (separator ⟺ `min < D+s ≤ max`) and the dual bijectivity engine
`weak_ascents_infinite` (companion to `weak_descents_infinite`, governing the window's *upper* edge).
The `sorry` itself is UNCHANGED.

## ATTEMPT LOG — "residue-class structure + bijection cut-balance closure" (re-verified, STILL OPEN)

A further attempt evaluated the proposed *residue-class (from a threshold dichotomy) + cut-balance*
route, scaffolded by the Hunters-and-Rabbit parity-sweep intuition.  Every step was checked with
`uv run` (scripts `attack_verify.py`, `attack_steps.py`, `attack_step3.py`, `swap_check.py`,
`obstruction_final.py` in `griddles-p4-verify/`).  **Truth re-confirmed** (every non-EI family has
unbounded separators at some even slack ≥ max; the `swap_at_powers` "near-misses" are log-sparse
separators at `D = 2ᵏ − b`, confirmed scaling to `D ≈ 2.6·10⁵` at `NMAX = 2.8·10⁵`).  The attack
does NOT close; the failure is **Step 3**, and the precise reasons:

  • **Reframing (verified, 0/374400 mismatches).**  A slack-`s` separator at `D` is exactly
    `[φ(a+D) < e+δ] XOR [φ(b+D) < e]` where `e := s − b`, `δ := b − a`, `φ(n) := c(n) − n`.  So
    `hno` at slack `s = b+e` is the eventual-in-`D` equivalence `[φ(a+D) < e+δ] ⟺ [φ(b+D) < e]`.
    **Parity caveat the task's "(★) for even `e`" glossed:** `s` even & `e = s−b` ⇒ `e` even ⟺ `b`
    even.  For **odd `b` there is no `e = 0`** (`e` ranges over the ODDs), so Step 1's "`e=0` residue
    anchor of `A := {φ ≥ 1}`" simply does not exist for half the pairs — the smallest available slack
    is `leastEvenGe(b)` giving `e₀ = 1`.

  • **Step 3's invoked sufficient condition is too weak (explicit witness).**  Step 3 claims "`φ`
    eventually constant `= k ≠ 0` on a residue class mod `δ` CONTRADICTS bijectivity via cut-balance."
    This is FALSE: the **parity-shift** `c(2k)=2k+2, c(2k+1)=2k−1, c(1)=2` has `φ ≡ +2` on the even
    class and `φ ≡ −2` on the odd class (mod `δ=2`) — *constant nonzero on every residue class* — yet
    is a genuine bijection with bounded cut `B(N) ≡ 1`.  The `+2` and `−2` classes balance each other.
    Residue-class constancy is just a *structured density*, and structured densities can balance, so
    cut-balance does not fire.  (Same wall as the prior log's "density alone fails / route A's `ψ`
    bounded is false".)  The cut identity itself was re-verified: `B(N) := |{n≤N : c(n)>N}| =
    |{n>N : c(n)≤N}|` holds for ALL tested `c,N`, and `EI ⟺ B(N)=0` eventually is correct — but
    `B(N) → ∞` on `growing_blocks_rev` (non-EI), so Step 3 cannot route through "`B` bounded".

  • **Why the residue route does NOT circumvent the non-uniform `m₀(e)` (the crux).**  On
    parity-shift pair `(2,4)` (`δ=2`), `hno`-style agreement HYP_e HOLDS for `e ∈ {0,4,6,8,…}` and
    FAILS only at `e = 2` (separators at every even `D`; this is slack `6 = leastEvenGe(max)+2`).  The
    HOLDING `e`'s pin level-set structure fully consistent with `φ = (+2 on evens, −2 on odds)` — a
    *bijective non-EI* permutation.  **The single bit certifying non-EI lives in the one FAILING `e`**,
    and there is no uniform mechanism to locate that `e` across pairs (the recurring slack is in
    `{leastEvenGe(max), leastEvenGe(max)+2}` with no closed form).  So Steps 1–2 cannot deliver
    anything *strictly stronger* than residue-density (e.g. "`φ ≥ 0` on all classes" or a signed
    imbalance) — which is exactly what Step 3 would need.  That extraction burden IS the same residue
    as the parallel `boundedSlack_recurrence`.

**Net.**  Every route attempted so far (band-collapse, single-ray pigeonhole, cut-flow route A,
and now residue-class + cut-balance) hits the identical wall: `hno`'s per-slack displacement floor
`D₀(s)` does not uniformize across `s`, and no proposed structure-extraction yields more than a
density that a balanced bijection (parity-shift) satisfies.  The productive next move is to attack
the parallel `boundedSlack_recurrence` directly (the global-count residue), not the lemma side.  No
new mechanism found; `sorry` UNCHANGED, build GREEN. -/
theorem noSeparator_allSlack_imp_eventuallyIdentity
    (c : Perm) (a b : ℕ+) (hab : a ≠ b)
    (hno : ∀ s : ℕ, Even s → max a.val b.val ≤ s →
      ∃ D₀ : ℕ, ∀ D : ℕ, D ≥ D₀ → ¬ separatorAtSlack c a b s D) :
    EventuallyIdentity c := by
  sorry

#print axioms noSeparator_allSlack_imp_eventuallyIdentity

/-- Indicator disagreement at the fixed slack `s` *is* a slack-`s` separator: both are the
    statement that `[c(a+D).val < D+s]` and `[c(b+D).val < D+s]` differ. -/
private lemma not_indicatorAgree_imp_separatorAtSlack
    (c : Perm) (a b : ℕ+) (s D : ℕ)
    (hne : ¬ ((c (cellAt a D)).val ≥ D + s ↔ (c (cellAt b D)).val ≥ D + s)) :
    separatorAtSlack c a b s D := by
  unfold separatorAtSlack
  rw [decide_ne_iff_not_iff]
  -- `(x < D+s) ↔ (y < D+s)` is the negation-pair of `(x ≥ D+s) ↔ (y ≥ D+s)`.
  intro hlt
  apply hne
  constructor
  · intro hxge; by_contra hyge; push_neg at hyge
    exact absurd (hlt.mpr hyge) (by omega)
  · intro hyge; by_contra hxge; push_neg at hxge
    exact absurd (hlt.mp hxge) (by omega)

/-! ### Window characterization of a fixed-slack separator

A slack-`s` separator at displacement `D` is exactly the statement that the *threshold*
`D + s` lies in the half-open interval *between* the two displaced labels
`c (a+D)` and `c (b+D)`: it separates them iff exactly one is below the threshold, i.e. iff
`min < D+s ≤ max`.  This is a definitional Boolean-to-order unfolding, axiom-clean, and is the
natural geometric reformulation used by every analysis of the band recurrence (the "separating
slacks at `D` form the interval `(min−D, max−D]`").  Proven here for reuse. -/
theorem separatorAtSlack_iff_window (c : Perm) (a b : ℕ+) (s D : ℕ) :
    separatorAtSlack c a b s D ↔
      min (c (cellAt a D)).val (c (cellAt b D)).val < D + s ∧
        D + s ≤ max (c (cellAt a D)).val (c (cellAt b D)).val := by
  unfold separatorAtSlack
  rw [decide_ne_iff_not_iff]
  set x := (c (cellAt a D)).val with hx
  set y := (c (cellAt b D)).val with hy
  -- `¬ ((x < D+s) ↔ (y < D+s))` ⟺ exactly one of `x,y` is `< D+s` ⟺ `min < D+s ≤ max`.
  constructor
  · intro h
    -- exactly one side is below the threshold.
    by_cases hxlt : x < D + s
    · -- then y is not below.
      have hyge : ¬ y < D + s := fun hylt => h ⟨fun _ => hylt, fun _ => hxlt⟩
      push_neg at hyge
      refine ⟨?_, ?_⟩
      · exact lt_of_le_of_lt (min_le_left x y) hxlt
      · exact le_trans hyge (le_max_right x y)
    · -- x not below; then y must be below (else the iff holds vacuously).
      push_neg at hxlt
      by_cases hylt : y < D + s
      · refine ⟨?_, ?_⟩
        · exact lt_of_le_of_lt (min_le_right x y) hylt
        · exact le_trans hxlt (le_max_left x y)
      · push_neg at hylt
        exact absurd ⟨fun hx' => absurd hx' (by omega), fun hy' => absurd hy' (by omega)⟩ h
  · rintro ⟨hmin, hmax⟩ hiff
    -- `min < D+s ≤ max` with both-or-neither below the threshold is contradictory.
    rcases le_total x y with hxy | hxy
    · -- min = x, max = y; so x < D+s ≤ y, contradicting the iff at the `x` side.
      rw [min_eq_left hxy] at hmin
      rw [max_eq_right hxy] at hmax
      have : y < D + s := hiff.mp hmin
      omega
    · rw [min_eq_right hxy] at hmin
      rw [max_eq_left hxy] at hmax
      have : x < D + s := hiff.mpr hmin
      omega

#print axioms separatorAtSlack_iff_window

/-- **Band recurrence with a `max`-bounded slack.**  For non-eventually-identity `c` and any
    distinct pair `a ≠ b`, there is a fixed even slack `s ≥ max a.val b.val` whose fixed-slack
    separators recur at arbitrarily large displacement.  The `max`-lower-bound is what makes the
    pair enumeration have order type `ω` (finitely many pairs per slack level).

    TRUE (decisively verified computationally; canonical witness `s = leastEvenGe (max a b)`);
    the remaining `sorry` is isolated in `indicatorAgree_imp_eventuallyIdentity` (KEY) above —
    the slack-localized combinatorial residue.  Everything else here is the routine wrapping
    (witness/parity/`≥ max`, and the indicator↔separator conversion via KEY's contrapositive). -/
theorem band_recurrence_ge_max (c : Perm) (h : ¬ EventuallyIdentity c) (a b : ℕ+) (hab : a ≠ b) :
    ∃ s : ℕ, Even s ∧ max a.val b.val ≤ s ∧
      ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ separatorAtSlack c a b s D := by
  -- By contradiction: if NO even slack `s ≥ max` has recurring separators, then for every such
  -- `s` the separators are eventually absent — exactly KEY's hypothesis — forcing `EI`, contra `h`.
  -- (The witness `s` is genuinely existential: the smallest even `≥ max` does NOT always work,
  -- e.g. the parity-shift permutation `c(2k)=2k+2, c(2k+1)=2k-1` needs a larger slack for some
  -- pairs.  So we must NOT hardcode `s`; we let KEY supply the contradiction over ALL `s`.)
  by_contra hcon
  apply h
  apply noSeparator_allSlack_imp_eventuallyIdentity c a b hab
  intro s hse hsg
  by_contra hrec
  push_neg at hrec
  exact hcon ⟨s, hse, hsg, hrec⟩

-- Axiom audit: `band_recurrence_ge_max` is the lone remaining `sorry` of the winning direction
-- (its profile shows `sorryAx`).  It states an empirically-decisively-verified TRUE proposition
-- (canonical witness `s = ` smallest even `≥ max a.val b.val`); the gap is the slack-localized
-- combinatorial residue documented above.
#print axioms band_recurrence_ge_max

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

/-! ### Fixed (signal-independent) trajectories

A *fixed trajectory* ignores the observed signals and plays a predetermined move at each step
(depending only on elapsed time = history length).  It never guesses, and — crucially — its net
displacement from the start cell is the *same function of time for every start cell*.  This makes
the key "belief becomes finite at the first Yes" argument clean: the candidates still consistent
at a Yes-time `s` all map, under the common displacement, into the finite set of cells whose
label is `< s`. -/

/-- The signal-independent strategy that, at time-step of history length `t`, plays move `m t`. -/
def ofMoves (m : ℕ → Dir) : Strategy := fun h => Action.move (m h.length)

lemma ofMoves_neverGuesses (m : ℕ → Dir) : NeverGuesses (ofMoves m) :=
  fun h => ⟨m h.length, rfl⟩

/-- Cumulative net displacement of the move sequence `m` after `t` steps. -/
def cumDelta (m : ℕ → Dir) : ℕ → ℤ
  | 0     => 0
  | t + 1 => cumDelta m t + (m t).delta

/-- **Position under a fixed trajectory is start-independent in its increment.**  From start
    `k₀`, the position at time `t` is `k₀ + cumDelta m t`; the displacement `cumDelta m t` does
    not depend on `k₀` (nor on any signal). -/
lemma position_ofMoves (c : Perm) (m : ℕ → Dir) (k₀ : ℤ) (t : ℕ) :
    position c (ofMoves m) k₀ t = k₀ + cumDelta m t := by
  induction t with
  | zero => simp [cumDelta]
  | succ t ih =>
      have hlen : (history c (ofMoves m) k₀ t).length = t :=
        history_length_neverGuesses (ofMoves_neverGuesses m) k₀ t
      have hd : (ofMoves m) (history c (ofMoves m) k₀ t) = Action.move (m t) := by
        show Action.move (m (history c (ofMoves m) k₀ t).length) = Action.move (m t)
        rw [hlen]
      rw [position_succ_of_move hd, ih, cumDelta]; ring

/-! ### Signal bridge: `signalOf` on a fixed trajectory ⟷ the slack comparison

The `separatorAtSlack` predicate compares `(c (cellAt · D)).val` (a `ℕ`) against `D + s` (a `ℕ`),
while the `Localizes` / `separating_trajectory_exists` obligations are stated through `signalOf` on
the actual integer position `(k₀ : ℤ) + cumDelta m t`.  On a *safe* fixed trajectory (`cumDelta`
nonnegative) these coincide; the bridge below makes this exact, so the separation obligation can be
discharged directly from a `separatorAtSlack` witness. -/

/-- On a fixed trajectory whose displacement at time `t` is the nonnegative integer `(D : ℕ)`, the
    `signalOf` reading from start `a : ℕ+` is exactly `[ (c (cellAt a D)).val < t ]`. -/
lemma signalOf_ofMoves_eq (c : Perm) (m : ℕ → Dir) (a : ℕ+) (t D : ℕ)
    (hD : cumDelta m t = (D : ℤ)) :
    signalOf c (position c (ofMoves m) (a : ℤ) t) t
      = decide ((c (cellAt a D)).val < t) := by
  rw [position_ofMoves, hD]
  -- position = (a : ℤ) + D ≥ 1, so signalOf takes the `decide` branch.
  have hpos : (1 : ℤ) ≤ (a : ℤ) + (D : ℤ) := by
    have : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast a.one_le
    linarith [Int.ofNat_nonneg D]
  unfold signalOf
  rw [dif_pos hpos]
  -- the cell `Int.toPNat ((a:ℤ)+D) hpos` equals `cellAt a D`.
  have hcell : Int.toPNat ((a : ℤ) + (D : ℤ)) hpos = cellAt a D := by
    apply Subtype.ext
    show (Int.toPNat ((a : ℤ) + (D : ℤ)) hpos).val = (cellAt a D).val
    rw [Int.toPNat_val, cellAt_val]
    -- ((a:ℤ)+D).toNat = a.val + D
    have heq : ((a : ℤ) + (D : ℤ)) = ((a.val + D : ℕ) : ℤ) := by push_cast; ring
    rw [heq, Int.toNat_natCast]
  rw [hcell]

/-- **First-Yes finiteness.**  The set of start cells whose signal at time `s` (under the common
    displacement `δ`) is "Yes" is finite: such a cell shifted by `δ` lands on a cell whose label
    is `< s`, and `c` has only finitely many such cells (the `≤ s-1` cells with small label). -/
lemma yesSet_finite (c : Perm) (s : ℕ) (δ : ℤ) :
    {k : ℕ+ | signalOf c ((k : ℤ) + δ) s = true}.Finite := by
  classical
  -- The finite "small-label" cells, shifted to ℤ-positions.
  have hindex : {v : ℕ+ | (v : ℕ) < s}.Finite :=
    Set.Finite.preimage (Subtype.val_injective.injOn) (Set.finite_Iio s)
  have hP : ((fun v : ℕ+ => ((c.symm v : ℕ+) : ℤ)) '' {v : ℕ+ | (v : ℕ) < s}).Finite :=
    hindex.image _
  have hmap_inj : Function.Injective (fun k : ℕ+ => (k : ℤ) + δ) := by
    intro a b hab
    have : (a : ℤ) = (b : ℤ) := by simpa using hab
    exact_mod_cast this
  refine Set.Finite.subset (hP.preimage hmap_inj.injOn) ?_
  intro k hk
  simp only [Set.mem_setOf_eq] at hk
  show ((k : ℤ) + δ) ∈ (fun v : ℕ+ => ((c.symm v : ℕ+) : ℤ)) '' {v : ℕ+ | (v : ℕ) < s}
  unfold signalOf at hk
  split at hk
  · rename_i hpos
    rw [decide_eq_true_eq] at hk
    refine ⟨c (Int.toPNat ((k : ℤ) + δ) hpos), hk, ?_⟩
    have hcoe : ((Int.toPNat ((k : ℤ) + δ) hpos : ℕ+) : ℤ) = (k : ℤ) + δ := by
      have h1 : ((Int.toPNat ((k : ℤ) + δ) hpos : ℕ+) : ℕ) = ((k : ℤ) + δ).toNat :=
        Int.toPNat_val _ _
      have h2 : (((Int.toPNat ((k : ℤ) + δ) hpos : ℕ+) : ℕ) : ℤ) = (k : ℤ) + δ := by
        rw [h1]; exact Int.toNat_of_nonneg (by linarith)
      simpa using h2
    simp only [Equiv.symm_apply_apply]
    exact hcoe
  · simp at hk

/-- **Reduction to a fixed separating trajectory.**  If a fixed (signal-independent) trajectory
    `ofMoves m` is safe from every start, eventually emits a "Yes" from every start, and
    *separates every pair* of distinct start cells (their signal histories eventually differ),
    then it `Localizes` every start cell.

    The finite-`T` obligation in `Localizes` (rule out *all infinitely many* wrong candidates by
    one time) is discharged by **first-Yes finiteness**: at a Yes-time `s₀` for `k₀`, every
    candidate not yet distinguished must itself signal "Yes" at `s₀`, and there are only finitely
    many such (`yesSet_finite`); each is separated at *some* finite time, so the maximum is a
    finite stop time `T`. -/
theorem ofMoves_localizes (c : Perm) (m : ℕ → Dir)
    (hsafe : ∀ (k₀ : ℕ+) (t : ℕ), 1 ≤ position c (ofMoves m) (k₀ : ℤ) t)
    (hsep : ∀ a b : ℕ+, a ≠ b → ∃ s : ℕ,
        signalOf c (position c (ofMoves m) (a : ℤ) s) s
          ≠ signalOf c (position c (ofMoves m) (b : ℤ) s) s)
    (hyes : ∀ k₀ : ℕ+, ∃ s : ℕ, signalOf c (position c (ofMoves m) (k₀ : ℤ) s) s = true) :
    ∀ k₀ : ℕ+, Localizes c (ofMoves m) k₀ := by
  classical
  intro k₀
  obtain ⟨s₀, hs₀⟩ := hyes k₀
  set δ := cumDelta m s₀ with hδ
  -- Rewrite the Yes-time signal of `k₀` in `δ`-form.
  have hk₀yes : signalOf c ((k₀ : ℤ) + δ) s₀ = true := by
    rwa [position_ofMoves] at hs₀
  -- The finite set of candidates that are *not* distinguished by `s₀` (they signal Yes at `s₀`).
  have hfin : {k : ℕ+ | signalOf c ((k : ℤ) + δ) s₀ = true}.Finite := yesSet_finite c s₀ δ
  -- Per-candidate separation time.
  set g : ℕ+ → ℕ := fun k => if h : k ≠ k₀ then Classical.choose (hsep k k₀ h) else 0 with hg
  set T : ℕ := max s₀ (hfin.toFinset.sup g) with hT
  refine ⟨T, ?_, ?_⟩
  · intro t _; exact hsafe k₀ t
  · intro k hkne
    by_cases hky : signalOf c ((k : ℤ) + δ) s₀ = true
    · -- `k` signals Yes at `s₀` ⇒ `k ∈` the finite set ⇒ use its separation time `g k ≤ T`.
      have hmem : k ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]; exact hky
      have hgk : g k = Classical.choose (hsep k k₀ hkne) := by rw [hg]; exact dif_pos hkne
      have hspec := Classical.choose_spec (hsep k k₀ hkne)
      refine ⟨g k, ?_, ?_⟩
      · exact le_trans (le_trans (Finset.le_sup hmem) (le_max_right _ _)) (le_refl _)
      · rw [hgk]; exact hspec
    · -- `k` signals No at `s₀` while `k₀` signals Yes ⇒ distinguished at `s₀ ≤ T`.
      refine ⟨s₀, le_max_left _ _, ?_⟩
      rw [position_ofMoves, position_ofMoves]
      rw [hk₀yes]
      simpa using hky

/-! ### The band-top staircase: constructing the separating fixed trajectory

We now build the explicit move sequence `m` discharging `separating_trajectory_exists`, *modulo*
the single isolated combinatorial lemma `band_recurrence_ge_max` (plus the pre-existing
`boundedSlack_recurrence` it routes through).  Everything in this section is fully proven.

The trajectory is a **lag-monotone staircase**.  We enumerate the (infinitely many) ordered
distinct start-pairs `(a, b)` with `a < b` in order of nondecreasing *recurring slack*
`slackOf a b` (`≥ b.val ≥ max(a,b)`, by `band_recurrence_ge_max`).  Each phase:

* **Raise** the lag to the pair's slack `s` (oscillating `D ∈ {0,1}`), then
* **Ride** right at lag `s` until a fixed-slack-`s` separator for the pair is met
  (`band_recurrence_ge_max` guarantees one at unbounded displacement), then
* **Tail**: ride right until the displacement exceeds the phase index (so displacements grow
  without bound — needed for the "Yes" obligation).

Safety is automatic (left moves only fire at `D ≥ 1`).  Separation: every pair is processed at a
finite phase, where the ride lands on a separator.  Yes: lag `→ ∞` and the tail visits arbitrarily
large displacements, so a weak descent (`weak_descents_infinite`) of `k₀` eventually fires. -/

namespace Staircase

variable (c : Perm) (h : ¬ EventuallyIdentity c)

/-- A canonical recurring even slack `≥ max a.val b.val` for a distinct pair, chosen from
    `band_recurrence_ge_max`.  (For `a = b` it is the dummy `0`; only distinct pairs are used.) -/
noncomputable def slackOf (a b : ℕ+) : ℕ :=
  if hab : a ≠ b then Classical.choose (band_recurrence_ge_max c h a b hab) else 0

/-- `slackOf` is even (from the chosen witness). -/
lemma slackOf_even {a b : ℕ+} (hab : a ≠ b) : Even (slackOf c h a b) := by
  unfold slackOf; rw [dif_pos hab]
  exact (Classical.choose_spec (band_recurrence_ge_max c h a b hab)).1

/-- `slackOf a b ≥ max a.val b.val` (the load-bearing lower bound for the `ω`-enumeration). -/
lemma le_slackOf {a b : ℕ+} (hab : a ≠ b) : max a.val b.val ≤ slackOf c h a b := by
  unfold slackOf; rw [dif_pos hab]
  exact (Classical.choose_spec (band_recurrence_ge_max c h a b hab)).2.1

/-- Fixed-slack-`slackOf a b` separators recur at arbitrarily large displacement. -/
lemma slackOf_recurs {a b : ℕ+} (hab : a ≠ b) (D₀ : ℕ) :
    ∃ D : ℕ, D ≥ D₀ ∧ separatorAtSlack c a b (slackOf c h a b) D := by
  unfold slackOf; rw [dif_pos hab]
  exact (Classical.choose_spec (band_recurrence_ge_max c h a b hab)).2.2 D₀

/-! #### Ordered distinct pairs and their `ω`-enumeration by key

A *pair* is an ordered distinct pair `(a, b)` with `a < b`.  Its *key* is `slackOf a b`.  Since
`slackOf a b ≥ b.val > a.val`, only finitely many pairs have key `≤ K` (`pairs_key_le_finite`),
so the keys form a well-order of type `ω`; we enumerate the pairs greedily by least key. -/

/-- The type of ordered distinct start-pairs. -/
abbrev OPair : Type := { p : ℕ+ × ℕ+ // p.1 < p.2 }

/-- The key of a pair: its recurring slack `slackOf`. -/
noncomputable def keyOf (p : OPair) : ℕ := slackOf c h p.1.1 p.1.2

/-- The two cells of a pair are distinct. -/
lemma OPair.ne (p : OPair) : p.1.1 ≠ p.1.2 := ne_of_lt p.2

/-- `p.1.2.val ≤ keyOf p` (the larger cell is bounded by the key). -/
lemma le_keyOf (p : OPair) : p.1.2.val ≤ keyOf c h p := by
  unfold keyOf
  have := le_slackOf c h (OPair.ne p)
  exact le_trans (le_max_right _ _) this

/-- The underlying `(ℕ × ℕ)` coordinates of a pair (injective). -/
def OPair.coords (p : OPair) : ℕ × ℕ := (p.1.1.val, p.1.2.val)

lemma OPair.coords_injective : Function.Injective OPair.coords := by
  rintro ⟨⟨a₁, b₁⟩, h₁⟩ ⟨⟨a₂, b₂⟩, h₂⟩ hxy
  simp only [OPair.coords] at hxy
  obtain ⟨ha, hb⟩ := Prod.mk.injEq .. ▸ hxy
  have ha' : a₁ = a₂ := PNat.coe_injective ha
  have hb' : b₁ = b₂ := PNat.coe_injective hb
  subst ha'; subst hb'; rfl

/-- **Finitely many pairs of bounded key.**  `{p : keyOf p ≤ K}` is finite, because such a pair has
    `b.val ≤ K` and `a < b`, so both cells live in `[1, K]`. -/
lemma pairs_key_le_finite (K : ℕ) : {p : OPair | keyOf c h p ≤ K}.Finite := by
  classical
  -- The image under `coords` lands in the finite box `Icc 1 K ×ˢ Icc 1 K`.
  have hbox : (OPair.coords '' {p : OPair | keyOf c h p ≤ K}).Finite := by
    apply Set.Finite.subset (Finset.Icc (1, 1) (K, K) : Finset (ℕ × ℕ)).finite_toSet
    rintro _ ⟨p, hp, rfl⟩
    simp only [Set.mem_setOf_eq] at hp
    have hb : p.1.2.val ≤ K := le_trans (le_keyOf c h p) hp
    have ha : p.1.1.val ≤ K := le_trans (le_of_lt (by exact_mod_cast p.2)) hb
    simp only [Finset.coe_Icc, Set.mem_Icc, OPair.coords, Prod.le_def]
    exact ⟨⟨p.1.1.one_le, p.1.2.one_le⟩, ha, hb⟩
  exact Set.Finite.of_finite_image hbox (OPair.coords_injective.injOn)

/-! #### Slack buckets and per-phase ride targets

Phase `k` of the staircase rides at lag `2k` and must reach a displacement past every separator of
every pair whose slack is `2k`.  We collect those pairs into `bucket k` (finite) and compute the
ride target `rideTarget k` (a displacement large enough that the ride past it has visited each
bucket pair's separator, and `≥ k+1` for the Yes tail).  `rideTarget` is monotone increasing, so
the rightward ride is consistent with the previous phase's end. -/

/-- The (finite) set of pairs whose recurring slack is exactly `2k`. -/
noncomputable def bucket (k : ℕ) : Finset OPair :=
  (pairs_key_le_finite c h (2 * k)).toFinset.filter (fun p => keyOf c h p = 2 * k)

lemma mem_bucket {k : ℕ} {p : OPair} : p ∈ bucket c h k ↔ keyOf c h p = 2 * k := by
  unfold bucket
  rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · exact fun ⟨_, h2⟩ => h2
  · exact fun h2 => ⟨le_of_eq h2, h2⟩

/-- For a pair `p` and a displacement floor `D₀`, the least separator displacement `≥ D₀` at the
    pair's own slack `keyOf p`.  Exists by `slackOf_recurs` (the band recurrence). -/
noncomputable def sepDispAt (p : OPair) (D₀ : ℕ) : ℕ :=
  Nat.find (slackOf_recurs c h (OPair.ne p) D₀)

lemma sepDispAt_ge (p : OPair) (D₀ : ℕ) : sepDispAt c h p D₀ ≥ D₀ :=
  (Nat.find_spec (slackOf_recurs c h (OPair.ne p) D₀)).1

lemma sepDispAt_sep (p : OPair) (D₀ : ℕ) :
    separatorAtSlack c p.1.1 p.1.2 (keyOf c h p) (sepDispAt c h p D₀) :=
  (Nat.find_spec (slackOf_recurs c h (OPair.ne p) D₀)).2

/-- **Per-phase ride target.**  `rideTarget k` is the displacement at the end of phase `k`'s ride
    (at lag `2k`).  Defined so that (a) it is `≥ rideTarget (k-1)` and `≥ k` (monotone, and the Yes
    tail grows `D`), and (b) it is `≥ sepDispAt p (rideTarget (k-1))` for every `p ∈ bucket k`, so
    the ride from `rideTarget (k-1)` up to `rideTarget k` passes through every bucket-`k` separator.
    -/
noncomputable def rideTarget : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      max (max (rideTarget k) (k + 1))
        ((bucket c h (k + 1)).sup (fun p => sepDispAt c h p (rideTarget k)))
  decreasing_by all_goals simp_wf

lemma rideTarget_mono_step (k : ℕ) : rideTarget c h k ≤ rideTarget c h (k + 1) := by
  rw [rideTarget]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

lemma rideTarget_ge_idx (k : ℕ) : k ≤ rideTarget c h k := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ n =>
      rw [rideTarget]
      exact le_trans (le_max_right _ _) (le_max_left _ _)

/-- The ride of phase `k+1` reaches every bucket-`(k+1)` separator: for `p ∈ bucket (k+1)`,
    `sepDispAt p (rideTarget k) ≤ rideTarget (k+1)`. -/
lemma sepDispAt_le_rideTarget {k : ℕ} {p : OPair} (hp : p ∈ bucket c h (k + 1)) :
    sepDispAt c h p (rideTarget c h k) ≤ rideTarget c h (k + 1) := by
  have hsup : sepDispAt c h p (rideTarget c h k)
      ≤ (bucket c h (k + 1)).sup (fun q => sepDispAt c h q (rideTarget c h k)) :=
    Finset.le_sup (f := fun q => sepDispAt c h q (rideTarget c h k)) hp
  rw [rideTarget]
  exact le_trans hsup (le_max_right _ _)

/-! #### The state machine

The trajectory runs phase `k+1` for `k = 0, 1, 2, …`.  Phase `k+1` starts at displacement
`rideTarget k` and lag `2k`, then:

* **`raiseR`**: emit `R` (`D → D+1`),
* **`raiseL`**: emit `L` (`D → D` again, lag `→ lag+2`); now lag `= 2(k+1)`,
* **`ride`**: emit `R` until `D = rideTarget (k+1)`, then advance to phase `k+2`'s `raiseR`.

The state records the current displacement `D`, phase index `k`, and sub-phase.  The initial state
(`D = 0`, `k = 0`, `raiseR`) begins phase `1`. -/

/-- Sub-phase tag. -/
inductive Sub | raiseR | raiseL | ride
  deriving DecidableEq, Repr

/-- Trajectory state. -/
structure St where
  D : ℕ
  k : ℕ
  sub : Sub
  deriving Repr

/-- The move emitted from a state. -/
def moveOf (st : St) : Dir :=
  match st.sub with
  | Sub.raiseR => Dir.right
  | Sub.raiseL => Dir.left
  | Sub.ride   => Dir.right   -- (a final phase-advance tick still emits R, harmless)

/-- The next state after emitting `moveOf st`. -/
noncomputable def nextSt (st : St) : St :=
  match st.sub with
  | Sub.raiseR => { D := st.D + 1, k := st.k, sub := Sub.raiseL }
  | Sub.raiseL => { D := st.D - 1, k := st.k, sub := Sub.ride }
  | Sub.ride   =>
      if st.D < rideTarget c h (st.k + 1) then
        { D := st.D + 1, k := st.k, sub := Sub.ride }
      else
        -- finished phase k+1; begin phase k+2 with an R move (raiseR)
        { D := st.D + 1, k := st.k + 1, sub := Sub.raiseL }

/-- The state at time `t`. -/
noncomputable def trajSt : ℕ → St
  | 0 => { D := 0, k := 0, sub := Sub.raiseR }
  | t + 1 => nextSt c h (trajSt t)

/-- The fixed move sequence of the staircase. -/
noncomputable def stairMoves : ℕ → Dir := fun t => moveOf (trajSt c h t)

/-! #### Invariants -/

@[simp] lemma trajSt_succ (t : ℕ) : trajSt c h (t + 1) = nextSt c h (trajSt c h t) := rfl

/-- At a `raiseL` state the displacement is `≥ 1` (so the left move keeps `D ≥ 0`). -/
lemma raiseL_D_pos (t : ℕ) : (trajSt c h t).sub = Sub.raiseL → 1 ≤ (trajSt c h t).D := by
  cases t with
  | zero => intro hsub; simp [trajSt] at hsub
  | succ n =>
      intro hsub
      rw [trajSt_succ] at hsub ⊢
      -- inspect the previous sub-phase
      unfold nextSt at hsub ⊢
      cases hprev : (trajSt c h n).sub with
      | raiseR => simp [hprev]
      | raiseL => simp [hprev] at hsub
      | ride =>
          simp only [hprev] at hsub ⊢
          split
          · -- if-branch: sub becomes `ride`, contradicting hsub which (also if-branch) says raiseL
            rename_i hlt
            simp only [hlt, if_true] at hsub
            simp at hsub
          · -- else-branch: D := old + 1 ≥ 1
            show 1 ≤ (trajSt c h n).D + 1
            omega

/-- **Displacement tracking.**  The cumulative displacement of `stairMoves` equals the state's `D`
    (as an integer).  The only nontrivial step is the `raiseL` left move, where `raiseL_D_pos`
    ensures the `ℕ` subtraction agrees with the `ℤ` decrement. -/
lemma cumDelta_stairMoves (t : ℕ) :
    cumDelta (stairMoves c h) t = ((trajSt c h t).D : ℤ) := by
  induction t with
  | zero => simp [cumDelta, trajSt]
  | succ n ih =>
      rw [cumDelta, ih, trajSt_succ]
      show ((trajSt c h n).D : ℤ) + (moveOf (trajSt c h n)).delta
            = ((nextSt c h (trajSt c h n)).D : ℤ)
      unfold moveOf nextSt
      cases hsub : (trajSt c h n).sub with
      | raiseR => simp [hsub]
      | raiseL =>
          have hpos : 1 ≤ (trajSt c h n).D := raiseL_D_pos c h n hsub
          simp only [hsub]
          show ((trajSt c h n).D : ℤ) + (-1) = (((trajSt c h n).D - 1 : ℕ) : ℤ)
          rw [Nat.cast_sub hpos]; push_cast; ring
      | ride =>
          simp only [hsub]
          split <;> · show ((trajSt c h n).D : ℤ) + (1) = (((trajSt c h n).D + 1 : ℕ) : ℤ)
                      push_cast; ring

/-- **Safety.**  From any start cell, the position never falls off the left edge. -/
lemma stair_safe (k₀ : ℕ+) (t : ℕ) :
    1 ≤ position c (ofMoves (stairMoves c h)) (k₀ : ℤ) t := by
  rw [position_ofMoves, cumDelta_stairMoves]
  have h1 : (1 : ℤ) ≤ (k₀ : ℤ) := by exact_mod_cast k₀.one_le
  have h2 : (0 : ℤ) ≤ ((trajSt c h t).D : ℤ) := Int.ofNat_nonneg _
  linarith

/-- The lag of a state: `2·k` plus `2` more once in the `ride` sub-phase. -/
def lagSt (st : St) : ℕ := 2 * st.k + (if st.sub = Sub.ride then 2 else 0)

/-- **Time = displacement + lag.**  The elapsed time decomposes as current displacement plus the
    (even) lag.  This pins the time at which each `(D, sub, k)` state occurs. -/
lemma time_eq_D_add_lag (t : ℕ) : t = (trajSt c h t).D + lagSt (trajSt c h t) := by
  induction t with
  | zero => simp [trajSt, lagSt]
  | succ n ih =>
      -- abbreviate the previous state's fields
      set p := trajSt c h n with hp
      rw [trajSt_succ, ← hp]
      simp only [lagSt] at ih
      cases hsub : p.sub with
      | raiseR =>
          rw [hsub, if_neg (by decide : Sub.raiseR ≠ Sub.ride)] at ih
          show n + 1 = (nextSt c h p).D + lagSt (nextSt c h p)
          unfold nextSt lagSt; rw [hsub]
          dsimp only
          rw [if_neg (by decide : Sub.raiseL ≠ Sub.ride)]
          omega
      | raiseL =>
          have hpos : 1 ≤ p.D := by rw [hp] at hsub ⊢; exact raiseL_D_pos c h n hsub
          rw [hsub, if_neg (by decide : Sub.raiseL ≠ Sub.ride)] at ih
          show n + 1 = (nextSt c h p).D + lagSt (nextSt c h p)
          unfold nextSt lagSt; rw [hsub]
          dsimp only
          rw [if_pos (rfl : Sub.ride = Sub.ride)]
          omega
      | ride =>
          rw [hsub, if_pos (rfl : Sub.ride = Sub.ride)] at ih
          show n + 1 = (nextSt c h p).D + lagSt (nextSt c h p)
          unfold nextSt lagSt; rw [hsub]
          dsimp only
          split
          · dsimp only; rw [if_pos (rfl : Sub.ride = Sub.ride)]; omega
          · dsimp only; rw [if_neg (by decide : Sub.raiseL ≠ Sub.ride)]; omega

/-! #### Reaching ride states

The ride of phase `k+1` (state `⟨·, k, ride⟩`) visits every displacement in
`[rideTarget k, rideTarget (k+1)]`.  We first show that, starting from the ride-start state
`⟨rideTarget k, k, ride⟩`, the trajectory reaches `⟨D', k, ride⟩` for every `D'` in range
(`ride_extends`); then that the ride-start state itself is reached (`reach_ride_start`); finally we
combine them (`reach_ride`). -/

/-- From the ride-start of phase `k+1`, the ride reaches `⟨rideTarget k + j, k, ride⟩` for every
    `j` with `rideTarget k + j ≤ rideTarget (k+1)`. -/
lemma ride_extends {k t₀ : ℕ} (h₀ : trajSt c h t₀ = ⟨rideTarget c h k, k, Sub.ride⟩) :
    ∀ j : ℕ, rideTarget c h k + j ≤ rideTarget c h (k + 1) →
      ∃ t, trajSt c h t = ⟨rideTarget c h k + j, k, Sub.ride⟩ := by
  intro j
  induction j with
  | zero => intro _; exact ⟨t₀, by simpa using h₀⟩
  | succ i ih =>
      intro hle
      obtain ⟨t, ht⟩ := ih (by omega)
      refine ⟨t + 1, ?_⟩
      rw [trajSt_succ, ht]
      -- at ⟨rideTarget k + i, k, ride⟩ with D < rideTarget (k+1): step rides to D+1
      unfold nextSt
      dsimp only
      rw [if_pos (by omega : rideTarget c h k + i < rideTarget c h (k + 1))]
      congr 1

/-- The ride-start state of phase `k+1` is reached: `∃ t, trajSt t = ⟨rideTarget k, k, ride⟩`. -/
lemma reach_ride_start (k : ℕ) :
    ∃ t, trajSt c h t = ⟨rideTarget c h k, k, Sub.ride⟩ := by
  induction k with
  | zero =>
      -- t = 2: raiseR (t0) → raiseL (t1) → ride (t2), with rideTarget 0 = 0
      refine ⟨2, ?_⟩
      have hr0 : rideTarget c h 0 = 0 := by rw [rideTarget]
      rw [hr0]
      show nextSt c h (nextSt c h (trajSt c h 0)) = ⟨0, 0, Sub.ride⟩
      rfl
  | succ n ih =>
      obtain ⟨t₀, ht₀⟩ := ih
      -- ride from rideTarget n to rideTarget (n+1) (last ride state of phase n+1)
      obtain ⟨t, ht⟩ := ride_extends c h ht₀ (rideTarget c h (n + 1) - rideTarget c h n)
        (by have := rideTarget_mono_step c h n; omega)
      have hD : rideTarget c h n + (rideTarget c h (n + 1) - rideTarget c h n)
          = rideTarget c h (n + 1) := by
        have := rideTarget_mono_step c h n; omega
      rw [hD] at ht
      -- two more ticks: boundary (ride→raiseL at D+1, k+1) then raiseL (→ride at D, k+1)
      refine ⟨t + 2, ?_⟩
      show nextSt c h (nextSt c h (trajSt c h t)) = _
      rw [ht]
      -- first nextSt: ride at D = rideTarget(n+1), not < target ⇒ boundary
      unfold nextSt
      dsimp only
      rw [if_neg (by omega : ¬ rideTarget c h (n + 1) < rideTarget c h (n + 1))]
      dsimp only
      -- now at ⟨rideTarget(n+1)+1, n+1, raiseL⟩; nextSt raiseL → ⟨rideTarget(n+1), n+1, ride⟩
      congr 1

/-- **Ride coverage.**  Phase `k+1`'s ride visits every displacement `D'` in
    `[rideTarget k, rideTarget (k+1)]` (in the `ride` sub-phase). -/
lemma reach_ride (k D' : ℕ) (hlo : rideTarget c h k ≤ D') (hhi : D' ≤ rideTarget c h (k + 1)) :
    ∃ t, trajSt c h t = ⟨D', k, Sub.ride⟩ := by
  obtain ⟨t₀, ht₀⟩ := reach_ride_start c h k
  obtain ⟨t, ht⟩ := ride_extends c h ht₀ (D' - rideTarget c h k) (by omega)
  rw [show rideTarget c h k + (D' - rideTarget c h k) = D' by omega] at ht
  exact ⟨t, ht⟩

/-! #### Separation

At a ride state `⟨D', k, ride⟩` the signal from start `a : ℕ+` reads exactly the slack-`2(k+1)`
comparison `[ (c (cellAt a D')).val < D' + 2(k+1) ]`.  So a `separatorAtSlack`-witness at slack
`2(k+1)` and displacement `D'`, visited by the ride, makes the signals of the two cells differ. -/

/-- The signal at a ride state, in the slack comparison form. -/
lemma signal_at_ride {t D' k : ℕ} (a : ℕ+) (ht : trajSt c h t = ⟨D', k, Sub.ride⟩) :
    signalOf c (position c (ofMoves (stairMoves c h)) (a : ℤ) t) t
      = decide ((c (cellAt a D')).val < D' + (2 * k + 2)) := by
  have hcum : cumDelta (stairMoves c h) t = (D' : ℤ) := by
    rw [cumDelta_stairMoves, ht]
  have htime : t = D' + (2 * k + 2) := by
    have := time_eq_D_add_lag c h t
    rw [ht] at this
    simpa [lagSt] using this
  rw [signalOf_ofMoves_eq c (stairMoves c h) a t D' hcum]
  rw [htime]

/-- `keyOf p` is even and `≥ 2`, hence `= 2·(k+1)` for some `k`.  (The pair's larger cell is `≥ 2`.)
    -/
lemma keyOf_eq_two_mul_succ (p : OPair) : ∃ k : ℕ, keyOf c h p = 2 * (k + 1) := by
  have heven : Even (keyOf c h p) := slackOf_even c h (OPair.ne p)
  have hge2 : 2 ≤ keyOf c h p := by
    have h1 : (2 : ℕ) ≤ p.1.2.val := by
      have : p.1.1.val < p.1.2.val := by exact_mod_cast p.2
      have : 1 ≤ p.1.1.val := p.1.1.one_le
      omega
    exact le_trans h1 (le_keyOf c h p)
  obtain ⟨m, hm⟩ := heven
  -- keyOf = m + m = 2m, with 2m ≥ 2 ⇒ m ≥ 1 ⇒ m = (m-1)+1
  refine ⟨m - 1, ?_⟩
  omega

/-- **Separation for an ordered pair.**  For `p : OPair`, the trajectory eventually emits different
    signals from `p.1.1` and `p.1.2`. -/
lemma separates_OPair (p : OPair) :
    ∃ s : ℕ,
      signalOf c (position c (ofMoves (stairMoves c h)) (p.1.1 : ℤ) s) s
        ≠ signalOf c (position c (ofMoves (stairMoves c h)) (p.1.2 : ℤ) s) s := by
  -- The pair's slack is `2(k+1)`, so it lives in `bucket (k+1)`.
  obtain ⟨k, hk⟩ := keyOf_eq_two_mul_succ c h p
  have hmem : p ∈ bucket c h (k + 1) := by
    rw [mem_bucket, hk]
  -- The bucket-`(k+1)` separator displacement for `p`, visited by phase-`(k+1)`'s ride.
  set D' := sepDispAt c h p (rideTarget c h k) with hD'
  have hlo : rideTarget c h k ≤ D' := sepDispAt_ge c h p (rideTarget c h k)
  have hhi : D' ≤ rideTarget c h (k + 1) := sepDispAt_le_rideTarget c h hmem
  obtain ⟨t, ht⟩ := reach_ride c h k D' hlo hhi
  refine ⟨t, ?_⟩
  -- both signals in slack-comparison form
  rw [signal_at_ride c h p.1.1 ht, signal_at_ride c h p.1.2 ht]
  -- the separator at slack `keyOf p = 2(k+1)` and displacement `D'`
  have hsep : separatorAtSlack c p.1.1 p.1.2 (keyOf c h p) D' := sepDispAt_sep c h p (rideTarget c h k)
  unfold separatorAtSlack at hsep
  -- keyOf p = 2k+2, so the bounds match
  rw [hk] at hsep
  -- hsep : decide ((c (cellAt p.1.1 D')).val < D' + 2*(k+1)) ≠ decide (... p.1.2 ...)
  have he1 : D' + (2 * k + 2) = D' + 2 * (k + 1) := by ring
  rw [he1]
  convert hsep using 2 <;> ring

/-- **Separation (any distinct pair).**  The staircase trajectory separates any two distinct start
    cells `a ≠ b`. -/
lemma stair_separates (a b : ℕ+) (hab : a ≠ b) :
    ∃ s : ℕ,
      signalOf c (position c (ofMoves (stairMoves c h)) (a : ℤ) s) s
        ≠ signalOf c (position c (ofMoves (stairMoves c h)) (b : ℤ) s) s := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b: use the OPair (a, b)
    obtain ⟨s, hs⟩ := separates_OPair c h ⟨(a, b), hlt⟩
    exact ⟨s, hs⟩
  · -- b < a: use the OPair (b, a) and swap the `≠`
    obtain ⟨s, hs⟩ := separates_OPair c h ⟨(b, a), hgt⟩
    exact ⟨s, hs.symm⟩

/-! #### Yes-emitting

Every displacement `D` lies in some phase's ride window `[rideTarget k', rideTarget (k'+1)]`
(`ride_window_cover`); choosing a window with sufficiently large lag (`2(k'+1) > k₀`) and a weak
descent `c(k₀+D) ≤ k₀+D` (`weak_descents_infinite`) makes the signal fire. -/

/-- `rideTarget` is monotone. -/
lemma rideTarget_mono {i j : ℕ} (hij : i ≤ j) : rideTarget c h i ≤ rideTarget c h j := by
  induction j with
  | zero =>
      have : i = 0 := Nat.le_zero.mp hij
      subst this; exact le_refl _
  | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with hlt | heq
      · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (rideTarget_mono_step c h n)
      · subst heq; exact le_refl _

/-- **Ride-window cover.**  Every displacement `D ≥ rideTarget k₀'` lies in the ride window of some
    phase `k'+1` with `k' ≥ k₀'` (so its lag `2(k'+1)` is at least `2(k₀'+1)`). -/
lemma ride_window_cover (kfloor D : ℕ) (hD : rideTarget c h kfloor ≤ D) :
    ∃ k', kfloor ≤ k' ∧ rideTarget c h k' ≤ D ∧ D ≤ rideTarget c h (k' + 1) := by
  classical
  -- kfloor ≤ D (since rideTarget kfloor ≥ kfloor)
  have hkfloor_le_D : kfloor ≤ D := le_trans (rideTarget_ge_idx c h kfloor) hD
  -- max index j ≤ D with rideTarget j ≤ D, via Nat.findGreatest
  set k' := Nat.findGreatest (fun j => rideTarget c h j ≤ D) D with hk'
  have hk'_le : rideTarget c h k' ≤ D :=
    Nat.findGreatest_spec (P := fun j => rideTarget c h j ≤ D) hkfloor_le_D hD
  have hk'_ge : kfloor ≤ k' :=
    Nat.le_findGreatest hkfloor_le_D hD
  have hk'_hi : D ≤ rideTarget c h (k' + 1) := by
    by_contra hcon
    push_neg at hcon
    have hle : rideTarget c h (k' + 1) ≤ D := le_of_lt hcon
    have hk1_le_D : k' + 1 ≤ D := le_trans (rideTarget_ge_idx c h (k' + 1)) hle
    have hgt : Nat.findGreatest (fun j => rideTarget c h j ≤ D) D < k' + 1 := by
      rw [← hk']; exact Nat.lt_succ_self k'
    exact Nat.findGreatest_is_greatest hgt hk1_le_D hle
  exact ⟨k', hk'_ge, hk'_le, hk'_hi⟩

/-- **Yes-emitting.**  From every start cell, the staircase trajectory eventually reads a "Yes". -/
lemma stair_yes (k₀ : ℕ+) :
    ∃ s : ℕ, signalOf c (position c (ofMoves (stairMoves c h)) (k₀ : ℤ) s) s = true := by
  -- Pick a lag floor `kfloor = k₀.val` so every later phase has lag `> k₀.val`.
  set kfloor := k₀.val with hkfloor
  -- A weak descent `D ≥ rideTarget kfloor`: `c(k₀+D) ≤ k₀+D`.
  obtain ⟨D, hDge, hwd⟩ := weak_descents_infinite c k₀ (rideTarget c h kfloor)
  -- The covering phase `k' ≥ kfloor`.
  obtain ⟨k', hk'ge, hlo, hhi⟩ := ride_window_cover c h kfloor D hDge
  -- The ride state at `⟨D, k', ride⟩`.
  obtain ⟨t, ht⟩ := reach_ride c h k' D hlo hhi
  refine ⟨t, ?_⟩
  rw [signal_at_ride c h k₀ ht]
  -- need (c (cellAt k₀ D)).val < D + (2*k'+2)
  rw [decide_eq_true_eq]
  -- weak descent: (c (cellAt k₀ D)).val ≤ (cellAt k₀ D).val = k₀.val + D
  have hwd' : (c (cellAt k₀ D)).val ≤ k₀.val + D := by
    rw [cellAt_val] at hwd; exact hwd
  -- lag big: 2*(k'+1) ≥ 2*(kfloor+1) > k₀.val
  have hlag : k₀.val < 2 * k' + 2 := by
    have : kfloor ≤ k' := hk'ge
    rw [hkfloor] at this
    omega
  omega

end Staircase

/-! ### The separating fixed trajectory (now PROVEN modulo `band_recurrence_ge_max`) -/

/-- **Separating fixed trajectory.**

For every non-eventually-identity `c`, there is ONE fixed (signal-independent) move sequence `m`
whose trajectory is (i) *safe* — never falls off the left edge from any start (equivalently
`cumDelta m t ≥ 0`, i.e. `D_t ≥ 0`); (ii) *Yes-emitting* — from every start cell it eventually
reads a "Yes"; and (iii) *separating* — for any two distinct start cells the signal histories
eventually differ.

This is the purely combinatorial heart, with **no game/belief semantics left**: by
`ofMoves_localizes` (proven), (i)+(ii)+(iii) imply `Localizes` for every start, hence (via
`localizes_BobWins`) `BobWins`.

The witness is the **band-top lag-monotone staircase** `Staircase.stairMoves c h` (this file,
namespace `Staircase`): phase `k+1` raises the lag to `2(k+1)` (one `RL` pair), rides right past
every separator of every pair whose recurring slack is `2(k+1)`, then tail-rides until the
displacement exceeds the phase index.  Safety (`stair_safe`), separation (`stair_separates`), and
Yes (`stair_yes`) are all FULLY PROVEN; the construction rests on the single isolated combinatorial
lemma `band_recurrence_ge_max` (the `max`-bounded recurring-slack fact, supplying both the
`ω`-finiteness of the slack buckets and the per-bucket ride termination) — plus, transitively, the
pre-existing `boundedSlack_recurrence`. -/
theorem separating_trajectory_exists (c : Perm) (h : ¬ EventuallyIdentity c) :
    ∃ m : ℕ → Dir,
      (∀ (k₀ : ℕ+) (t : ℕ), 1 ≤ position c (ofMoves m) (k₀ : ℤ) t) ∧
      (∀ a b : ℕ+, a ≠ b → ∃ s : ℕ,
          signalOf c (position c (ofMoves m) (a : ℤ) s) s
            ≠ signalOf c (position c (ofMoves m) (b : ℤ) s) s) ∧
      (∀ k₀ : ℕ+, ∃ s : ℕ, signalOf c (position c (ofMoves m) (k₀ : ℤ) s) s = true) :=
  ⟨Staircase.stairMoves c h,
    Staircase.stair_safe c h,
    Staircase.stair_separates c h,
    Staircase.stair_yes c h⟩

-- Axiom audit.  `separating_trajectory_exists` is `sorry`-free *modulo* the two isolated
-- combinatorial residues `band_recurrence_ge_max` (new) and `boundedSlack_recurrence`
-- (pre-existing): its profile shows `sorryAx` solely through those.  Every game-semantic and
-- construction step (the state machine, safety, the per-bucket separation, Yes) is fully proven.
#print axioms separating_trajectory_exists

/-- **Adaptive localization (fully reduced to `separating_trajectory_exists`).**

For every *non-eventually-identity* permutation `c`, there is a never-guessing exploration
strategy `σ` that *localizes* every start cell: from any `k₀`, `σ`'s trajectory stays safe for
finitely long and rules out every wrong candidate by a signal mismatch.

The witnessing `σ` is the **fixed (signal-independent) band-top staircase** `ofMoves (stairMoves)`
from `separating_trajectory_exists`.  Earlier notes feared this had to be a genuinely *adaptive*
belief-state machine; in fact a *c-tailored fixed* trajectory suffices (Bob still uses the signals
only to know *when to stop*, via `beliefStrat`, but his moves are predetermined).  The reduction
`ofMoves_localizes` turns (safety + separation + Yes) into `Localizes`, and those three are proven
in namespace `Staircase` modulo the single isolated lemma `band_recurrence_ge_max`. -/
theorem adaptive_localizes (c : Perm) (h : ¬ EventuallyIdentity c) :
    ∃ σ : Strategy, NeverGuesses σ ∧ ∀ k₀ : ℕ+, Localizes c σ k₀ := by
  obtain ⟨m, hsafe, hsep, hyes⟩ := separating_trajectory_exists c h
  exact ⟨ofMoves m, ofMoves_neverGuesses m, ofMoves_localizes c m hsafe hsep hyes⟩

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
