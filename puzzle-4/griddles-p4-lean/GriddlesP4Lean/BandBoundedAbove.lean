import GriddlesP4Lean.BoundedAbove
import GriddlesP4Lean.WinningAdaptive

/-!
# Bounded-above ⟹ band recurrence (the bounded-above regime of the winning direction)

This file proves the **band recurrence** — the per-pair recurring-slack guarantee packaged as
`BandProvider c` and consumed by the band-top staircase in `WinningAdaptive` — under the assumption
that `c` is *bounded above*: `∃ B, ∀ n, (c n).val ≤ n.val + B`.  This is the bounded-above half of
`main`'s winning-direction dichotomy (the unbounded-above half is handled separately by `GrowStair`,
where no single fixed slack recurs).  No general band recurrence is claimed: the band genuinely
recurs only in this bounded-above regime.

The argument follows the integer-displacement contrapositive (`f n := (c n).val − n.val : ℤ`):

* **(⋆) reformulation** (`signals_agree_of_no_separator`).  If the band *fails*, then for every
  even slack `s ≥ b.val` there is a finite floor `N_s` past which the two displaced signals
  *agree*: `[(c (a+D)).val ≥ D+s] ↔ [(c (b+D)).val ≥ D+s]`.  Pure consequence of
  `separatorAtSlack_iff_window`.

* **Value extraction** (`exists_top_recurring_value`).  Bounded above + infinitely many weak
  ascents (`weak_ascents_infinite`) gives a top value `v⋆ ≥ 0` that recurs infinitely often while
  `f n ≤ v⋆` cofinitely.

* **`v⋆ = 0`** ⟹ `f n ≤ 0` cofinitely ⟹ `descent_cofinite_imp_EI` ⟹ `EventuallyIdentity c`,
  contradicting the non-EI hypothesis.

The final theorem is `band_of_boundedAbove`.
-/

namespace TrolleyRetrieval

variable {c : Perm}

/-! ### Integer displacement -/

/-- The integer displacement `f n = (c n).val − n.val`. -/
def fdisp (c : Perm) (n : ℕ+) : ℤ := (c n).val - n.val

@[simp] lemma fdisp_def (c : Perm) (n : ℕ+) : fdisp c n = (c n).val - n.val := rfl

/-- `(c n).val ≥ k` (as a ℤ-threshold on the displacement). -/
lemma fdisp_ge_iff (c : Perm) (n : ℕ+) (k : ℤ) :
    k ≤ fdisp c n ↔ (n.val : ℤ) + k ≤ (c n).val := by
  unfold fdisp; constructor <;> intro h <;> omega

/-! ### (⋆) The signal-agreement reformulation of band-failure -/

/-- **No separator ⟹ the two displaced signals agree.**  If there is no slack-`s` separator at
    displacement `D`, then the threshold indicators `[(c (a+D)).val ≥ D+s]` and
    `[(c (b+D)).val ≥ D+s]` coincide.

    *Proof.*  By `separatorAtSlack_iff_window`, a separator is `min < D+s ≤ max`; its negation says
    either both labels are `≥ D+s` (when `D+s ≤ min`) or both are `< D+s` (when `max < D+s`). -/
lemma signals_agree_of_no_separator (c : Perm) (a b : ℕ+) (s D : ℕ)
    (hns : ¬ separatorAtSlack c a b s D) :
    ((D + s ≤ (c (cellAt a D)).val) ↔ (D + s ≤ (c (cellAt b D)).val)) := by
  rw [separatorAtSlack_iff_window] at hns
  push_neg at hns
  -- hns : min < D+s → max < D+s  (i.e. ¬(min < D+s ∧ D+s ≤ max))
  set x := (c (cellAt a D)).val with hx
  set y := (c (cellAt b D)).val with hy
  constructor
  · intro hxge
    -- x ≥ D+s.  If y < D+s then min ≤ y < D+s, so by hns max < D+s ≤ x ≤ max, contra.
    by_contra hyge
    push_neg at hyge -- hyge : y < D+s
    have hmin : min x y < D + s := lt_of_le_of_lt (min_le_right x y) hyge
    have hmax := hns hmin -- max x y < D+s
    have : x ≤ max x y := le_max_left x y
    omega
  · intro hyge
    by_contra hxge
    push_neg at hxge
    have hmin : min x y < D + s := lt_of_le_of_lt (min_le_left x y) hxge
    have hmax := hns hmin
    have : y ≤ max x y := le_max_right x y
    omega

/-! ### Value extraction: the top recurring displacement value -/

/-- "`f ≥ v` infinitely often" along all of `ℕ+`. -/
def InfGe (c : Perm) (v : ℤ) : Prop := ∀ N : ℕ+, ∃ n : ℕ+, N ≤ n ∧ v ≤ fdisp c n

/-- Weak ascents give `f ≥ 0` infinitely often. -/
lemma infGe_zero (c : Perm) : InfGe c 0 := by
  intro N
  obtain ⟨p, hp, hwa⟩ := weak_ascents_infinite c N
  refine ⟨p, hp, ?_⟩
  -- p ≤ c p ⟹ p.val ≤ (c p).val ⟹ 0 ≤ fdisp c p
  have : (p.val : ℤ) ≤ (c p).val := by exact_mod_cast (PNat.coe_le_coe p (c p)).2 hwa
  unfold fdisp; omega

/-- `InfGe` is antitone in the threshold. -/
lemma infGe_mono (c : Perm) {v w : ℤ} (hvw : v ≤ w) (h : InfGe c w) : InfGe c v := by
  intro N; obtain ⟨n, hn, hf⟩ := h N; exact ⟨n, hn, le_trans hvw hf⟩

/-- Under bounded above by `B`, `f n ≤ B` always, so `InfGe c (B+1)` fails (it never even holds). -/
lemma not_infGe_of_bddAbove (c : Perm) {B : ℕ} (hB : ∀ n : ℕ+, (c n).val ≤ n.val + B) :
    ¬ InfGe c ((B : ℤ) + 1) := by
  intro h
  obtain ⟨n, _, hf⟩ := h 1
  have := hB n
  unfold fdisp at hf
  have hcast : (c n).val ≤ n.val + B := this
  omega

/-- **Top recurring value.**  For `c` bounded above by `B` (and any permutation, via weak ascents),
    there is `v⋆ : ℕ` with `v⋆ ≤ B` such that:
    * `f n = v⋆` for infinitely many `n` (it recurs), and
    * `f n ≤ v⋆` cofinitely (some `N` past which `f n ≤ v⋆`). -/
lemma exists_top_recurring_value (c : Perm) {B : ℕ} (hB : ∀ n : ℕ+, (c n).val ≤ n.val + B) :
    ∃ v : ℕ, v ≤ B ∧
      (∀ N : ℕ+, ∃ n : ℕ+, N ≤ n ∧ fdisp c n = (v : ℤ)) ∧
      (∃ N : ℕ+, ∀ n : ℕ+, N ≤ n → fdisp c n ≤ (v : ℤ)) := by
  classical
  -- S = { j ∈ {0,…,B} : InfGe c j }.
  set S : Finset ℕ := (Finset.range (B + 1)).filter (fun j => InfGe c (j : ℤ)) with hS
  have h0mem : 0 ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.succ_pos B), by simpa using infGe_zero c⟩
  have hSne : S.Nonempty := ⟨0, h0mem⟩
  set v : ℕ := S.max' hSne with hv
  have hvmem : v ∈ S := Finset.max'_mem _ _
  rw [hS, Finset.mem_filter, Finset.mem_range] at hvmem
  obtain ⟨hvB, hvInf⟩ := hvmem
  have hvBle : v ≤ B := Nat.lt_succ_iff.mp hvB
  -- ¬ InfGe c (v+1).
  have hnot : ¬ InfGe c ((v : ℤ) + 1) := by
    intro hcon
    -- then v+1 ∈ S, contradicting maximality.
    have hv1B : v + 1 ≤ B := by
      by_contra hlt
      push_neg at hlt -- B < v+1, so B = v (since v ≤ B)
      have : v = B := by omega
      -- InfGe c (v+1) = InfGe c (B+1), impossible.
      rw [this] at hcon
      exact not_infGe_of_bddAbove c hB (by exact_mod_cast hcon)
    have hmem1 : v + 1 ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have : ((v + 1 : ℕ) : ℤ) = (v : ℤ) + 1 := by push_cast; ring
      rw [this]; exact hcon
    have : v + 1 ≤ v := Finset.le_max' S (v + 1) hmem1
    omega
  -- Cofinite cap: ¬ InfGe c (v+1) gives N with ∀ n ≥ N, ¬ (v+1 ≤ f n), i.e. f n ≤ v.
  have hcap : ∃ N : ℕ+, ∀ n : ℕ+, N ≤ n → fdisp c n ≤ (v : ℤ) := by
    unfold InfGe at hnot
    push_neg at hnot
    obtain ⟨N, hN⟩ := hnot
    exact ⟨N, fun n hn => by have := hN n hn; omega⟩
  obtain ⟨Ncap, hNcap⟩ := hcap
  refine ⟨v, hvBle, ?_, ⟨Ncap, hNcap⟩⟩
  -- Recurs: f ≥ v infinitely + f ≤ v cofinitely ⟹ f = v infinitely.
  intro N
  set M : ℕ+ := max N Ncap with hM
  obtain ⟨n, hn, hge⟩ := hvInf M
  have hnN : N ≤ n := le_trans (le_max_left N Ncap) hn
  have hnNcap : Ncap ≤ n := le_trans (le_max_right N Ncap) hn
  have hle := hNcap n hnNcap
  exact ⟨n, hnN, le_antisymm hle hge⟩

/-! ### Transporting "infinitely often" onto the ray from `a` -/

/-- `cellAt b D = cellAt a (D + (b.val − a.val))` when `a ≤ b` (both have value `b.val + D`). -/
lemma cellAt_b_eq_a_shift {a b : ℕ+} (hab : a ≤ b) (D : ℕ) :
    cellAt b D = cellAt a (D + (b.val - a.val)) := by
  apply Subtype.ext
  show b.val + D = a.val + (D + (b.val - a.val))
  have : a.val ≤ b.val := hab
  omega

/-- If a value `v` recurs (infinitely often) over all of `ℕ+`, it recurs along the ray from `a`:
    for every `D₀` there is `D ≥ D₀` with `fdisp c (cellAt a D) = v`. -/
lemma recurs_on_ray {c : Perm} {v : ℤ} (a : ℕ+)
    (hrec : ∀ N : ℕ+, ∃ n : ℕ+, N ≤ n ∧ fdisp c n = v) :
    ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ fdisp c (cellAt a D) = v := by
  intro D₀
  obtain ⟨n, hn, hf⟩ := hrec (cellAt a D₀)
  -- n ≥ cellAt a D₀, so n.val ≥ a.val + D₀ ≥ a.val; set D = n.val - a.val.
  have hnval : a.val + D₀ ≤ n.val := by
    have := (PNat.coe_le_coe _ _).2 hn; simpa [cellAt_val] using this
  refine ⟨n.val - a.val, by omega, ?_⟩
  have hcell : cellAt a (n.val - a.val) = n := by
    apply Subtype.ext; show a.val + (n.val - a.val) = n.val; omega
  rw [hcell]; exact hf

/-! ### (⋆_p) on the ray: the band-failure recurrence in displacement form -/

/-- **(⋆_p) ray form.**  Given band-failure at the *specific* even slack `s` (i.e. there is `N` past
    which there is no slack-`s` separator), with `p := (s : ℤ) − a.val`, `δ := (b.val − a.val : ℤ)`,
    and `δnat := b.val − a.val`, the displacement signals satisfy: for all `D ≥ N`,
    `[p ≤ fdisp c (cellAt a D)] ↔ [p − δ ≤ fdisp c (cellAt a (D + δnat))]`.

    *Proof.*  `signals_agree_of_no_separator` gives the ℕ-threshold agreement; rewrite each side as a
    ℤ-displacement threshold and use `cellAt b D = cellAt a (D + δnat)`. -/
lemma starP_ray {c : Perm} {a b : ℕ+} (hab : a < b) {s : ℕ} {N : ℕ}
    (hN : ∀ D : ℕ, N ≤ D → ¬ separatorAtSlack c a b s D) (D : ℕ) (hD : N ≤ D) :
    (((s : ℤ) - a.val) ≤ fdisp c (cellAt a D)) ↔
      (((s : ℤ) - a.val) - ((b.val : ℤ) - a.val) ≤
        fdisp c (cellAt a (D + (b.val - a.val)))) := by
  have hagree := signals_agree_of_no_separator c a b s D (hN D hD)
  -- LHS in ℕ-threshold form.
  have hLHS : (((s : ℤ) - a.val) ≤ fdisp c (cellAt a D)) ↔ (D + s ≤ (c (cellAt a D)).val) := by
    unfold fdisp; rw [cellAt_val]; constructor <;> intro h <;>
      · push_cast at h ⊢; omega
  -- RHS in ℕ-threshold form (via cellAt b D).
  have hcellb : cellAt a (D + (b.val - a.val)) = cellAt b D :=
    (cellAt_b_eq_a_shift (le_of_lt hab) D).symm
  have hRHS : (((s : ℤ) - a.val) - ((b.val : ℤ) - a.val) ≤
        fdisp c (cellAt a (D + (b.val - a.val)))) ↔ (D + s ≤ (c (cellAt b D)).val) := by
    rw [hcellb]; unfold fdisp; rw [cellAt_val]
    have hab' : a.val ≤ b.val := le_of_lt hab
    constructor <;> intro h <;>
      · push_cast at h ⊢; omega
  rw [hLHS, hRHS]; exact hagree

/-! ### Downward closure ⟹ cofinitely constant (used in the δ = 1 endgame) -/

/-- **Downward propagation.**  If a predicate `Q` on `ℕ` is *backward-closed* past a floor `N₀`
    (`Q (D+1) → Q D` for `D ≥ N₀`) and holds at points `D + Δ` for every `Δ` reachable, then it
    holds at `D`.  Stated as the workhorse: `Q (D + Δ) → Q D` for `D ≥ N₀`. -/
lemma downward_from_above {Q : ℕ → Prop} {N₀ : ℕ}
    (hbc : ∀ D : ℕ, N₀ ≤ D → Q (D + 1) → Q D) :
    ∀ Δ : ℕ, ∀ D : ℕ, N₀ ≤ D → Q (D + Δ) → Q D := by
  intro Δ
  induction Δ with
  | zero => intro D _ h; simpa using h
  | succ Δ ih =>
    intro D hD h
    -- Q (D + (Δ+1)) = Q ((D+1) + Δ); push to Q (D+1) via IH, then hbc.
    have h' : Q ((D + 1) + Δ) := by
      have : D + (Δ + 1) = (D + 1) + Δ := by omega
      rwa [this] at h
    have hD1 : Q (D + 1) := ih (D + 1) (by omega) h'
    exact hbc D hD hD1

/-- **Backward-closed + recurring ⟹ cofinitely true.**  If `Q` is backward-closed past `N₀` and
    holds at arbitrarily large arguments, then `Q D` holds for *all* `D ≥ N₀`. -/
lemma cofinite_of_backward_closed {Q : ℕ → Prop} {N₀ : ℕ}
    (hbc : ∀ D : ℕ, N₀ ≤ D → Q (D + 1) → Q D)
    (hrec : ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ Q D) :
    ∀ D : ℕ, N₀ ≤ D → Q D := by
  intro D hD
  obtain ⟨D', hD'ge, hQ⟩ := hrec D
  -- D' ≥ D, write D' = D + (D' - D).
  have : Q (D + (D' - D)) := by
    have : D + (D' - D) = D' := by omega
    rwa [this]
  exact downward_from_above hbc (D' - D) D hD this

/-! ### The main theorem -/

/-- **Bounded above ⟹ band recurrence.**  If `c` is not eventually identity and is bounded above
    (`∃ B, ∀ n, (c n).val ≤ n.val + B`), then for any distinct ordered pair `a < b` there is a
    fixed even slack `s ≥ max a.val b.val` whose separators recur at unbounded displacement.

    This is the per-pair content of `BandProvider c` for the bounded-above regime; assembled over
    all pairs by `bandProvider_of_boundedAbove` and consumed by `BobWins_of_bandProvider`. -/
theorem band_of_boundedAbove (c : Perm) (h : ¬ EventuallyIdentity c) (a b : ℕ+) (hab : a < b)
    (hbdd : ∃ B : ℕ, ∀ n : ℕ+, (c n).val ≤ n.val + B) :
    ∃ s : ℕ, Even s ∧ max a.val b.val ≤ s ∧
      ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ separatorAtSlack c a b s D := by
  classical
  obtain ⟨B, hB⟩ := hbdd
  have hmax : max a.val b.val = b.val := max_eq_right (le_of_lt hab)
  have habval : a.val < b.val := by exact_mod_cast hab
  set δnat : ℕ := b.val - a.val with hδnat
  have hδpos : 1 ≤ δnat := by omega
  by_contra hcon
  push_neg at hcon
  rw [hmax] at hcon
  -- hcon : ∀ s, Even s → b.val ≤ s → ∃ N, ∀ D ≥ N, ¬ separatorAtSlack c a b s D
  -- Top recurring value.
  obtain ⟨v, hvB, hrec, hcap0⟩ := exists_top_recurring_value c hB
  obtain ⟨Ncap, hNcap⟩ := hcap0
  -- v = 0 ⟹ descent-cofinite ⟹ EI ⟹ contradiction.
  rcases Nat.eq_zero_or_pos v with hv0 | hvpos
  · subst hv0
    apply h
    apply descent_cofinite_imp_EI c Ncap
    intro n hn
    have hfn := hNcap n hn
    unfold fdisp at hfn
    -- (c n).val - n.val ≤ 0
    have hz : ((c n).val : ℤ) ≤ (n.val : ℤ) := by push_cast at hfn ⊢; omega
    exact_mod_cast hz
  -- v ≥ 1.  Choose q̄ = largest ≡ b.val mod 2 with 0 ≤ q̄ ≤ v.
  set qbar : ℕ := if v % 2 = b.val % 2 then v else v - 1 with hqbar
  have hq_le : qbar ≤ v := by rw [hqbar]; split <;> omega
  have hq_ge : v - 1 ≤ qbar := by rw [hqbar]; split <;> omega
  have hq_par : (qbar + b.val) % 2 = 0 := by
    rw [hqbar]; split
    · rename_i hpar; omega
    · rename_i hpar; omega
  -- The slack s = qbar + b.val (even, ≥ b.val).
  set s : ℕ := qbar + b.val with hs
  have hs_even : Even s := by rw [hs]; exact (Nat.even_iff).mpr hq_par
  have hs_ge : b.val ≤ s := by rw [hs]; omega
  -- Band-failure at this s: a no-separator floor N.
  obtain ⟨N, hN⟩ := hcon s hs_even hs_ge
  -- p := (s:ℤ) - a.val = qbar + δ ; p - δ = qbar.   (δ = b.val - a.val)
  -- (⋆_p): for D ≥ N, [p ≤ g D] ↔ [qbar ≤ g (D + δnat)].
  -- g D := fdisp c (cellAt a D).
  set g : ℕ → ℤ := fun D => fdisp c (cellAt a D) with hg
  have hstar : ∀ D : ℕ, N ≤ D →
      (((s : ℤ) - a.val) ≤ g D ↔ (qbar : ℤ) ≤ g (D + δnat)) := by
    intro D hD
    have := starP_ray hab hN D hD
    -- rewrite RHS threshold (s - a.val) - (b.val - a.val) = qbar and the shift index δnat.
    have hpm : ((s : ℤ) - a.val) - ((b.val : ℤ) - a.val) = (qbar : ℤ) := by
      rw [hs]; push_cast; ring
    rw [hpm] at this
    -- the shift index inside cellAt: (b.val - a.val) = δnat (ℕ)
    have : (((s : ℤ) - a.val) ≤ fdisp c (cellAt a D) ↔
        (qbar : ℤ) ≤ fdisp c (cellAt a (D + δnat))) := by
      rw [hδnat]; exact this
    exact this
  -- p ≤ g D in the canonical form: p = (s:ℤ) - a.val = qbar + δ.
  -- value δ = b.val - a.val ; p - δnat-as-ℤ = qbar. Establish p ≥ v + something:
  have hp_val : (s : ℤ) - a.val = (qbar : ℤ) + δnat := by rw [hs, hδnat]; push_cast; omega
  -- Recurrence of v on the ray.
  have hrayrec : ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ g D = (v : ℤ) := recurs_on_ray a hrec
  -- Common floor: cells past Mfloor are ≥ Ncap (so cap applies) and indices ≥ N.
  -- Ncap as a displacement on the ray: any D with cellAt a D ≥ Ncap. Use a numeric floor.
  -- We need: for D ≥ Ncapd, fdisp c (cellAt a D) ≤ v.  Take Ncapd := Ncap.val.
  have hcap_ray : ∀ D : ℕ, Ncap.val ≤ a.val + D → g D ≤ (v : ℤ) := by
    intro D hD
    have hcell : Ncap ≤ cellAt a D := by
      apply (PNat.coe_le_coe _ _).1; rw [cellAt_val]; exact hD
    exact hNcap (cellAt a D) hcell
  -- Now split on δ.
  rcases Nat.lt_or_ge δnat 2 with hδ1 | hδ2
  · -- δnat = 1.
    have hδeq : δnat = 1 := by omega
    -- Backward closure: for D ≥ floor, g (D+1) = v → g D = v.
    set N₀ : ℕ := max N Ncap.val with hN₀
    have hbc : ∀ D : ℕ, N₀ ≤ D → g (D + 1) = (v : ℤ) → g D = (v : ℤ) := by
      intro D hD hgsucc
      have hDN : N ≤ D := le_trans (le_max_left _ _) hD
      have hDcap : Ncap.val ≤ a.val + D := by
        have : Ncap.val ≤ D := le_trans (le_max_right _ _) hD
        omega
      -- RHS: qbar ≤ g (D + δnat) = g (D+1) = v.
      have hRHS : (qbar : ℤ) ≤ g (D + δnat) := by
        rw [hδeq]; rw [hgsucc]; exact_mod_cast hq_le
      have hLHS : ((s : ℤ) - a.val) ≤ g D := (hstar D hDN).mpr hRHS
      -- p = qbar + δnat = qbar + 1 ≥ v (since qbar ≥ v-1, v ≥ 1).
      have hp_ge_v : (v : ℤ) ≤ (s : ℤ) - a.val := by
        rw [hp_val, hδeq]; push_cast
        have hqz : (v : ℤ) - 1 ≤ (qbar : ℤ) := by
          have := hq_ge; have := hvpos; omega
        omega
      have hge : (v : ℤ) ≤ g D := le_trans hp_ge_v hLHS
      have hle : g D ≤ (v : ℤ) := hcap_ray D hDcap
      omega
    -- Recurrence of v on the ray as a `Q`-recurrence.
    have hrecQ : ∀ D₀ : ℕ, ∃ D : ℕ, D ≥ D₀ ∧ g D = (v : ℤ) := hrayrec
    -- Cofinite: g D = v for all D ≥ N₀.
    have hcofin : ∀ D : ℕ, N₀ ≤ D → g D = (v : ℤ) :=
      cofinite_of_backward_closed hbc hrecQ
    -- Translate to ascent-cofinite on cells, then EI.
    apply h
    -- ascent floor: cell N₀cell := cellAt a N₀.
    apply ascent_cofinite_imp_EI c (cellAt a N₀)
    intro n hn
    -- n ≥ cellAt a N₀, so n = cellAt a D with D ≥ N₀.
    have hnval : a.val + N₀ ≤ n.val := by
      have := (PNat.coe_le_coe _ _).2 hn; simpa [cellAt_val] using this
    set D : ℕ := n.val - a.val with hD
    have hcell : cellAt a D = n := by apply Subtype.ext; show a.val + D = n.val; omega
    have hDN₀ : N₀ ≤ D := by omega
    have hcof := hcofin D hDN₀
    simp only [hg] at hcof
    rw [hcell] at hcof
    -- fdisp c n = v ⟹ (c n).val = n.val + v ≥ n.val.
    unfold fdisp at hcof
    have hge : (n.val : ℤ) ≤ (c n).val := by omega
    exact_mod_cast hge
  · -- δnat ≥ 2.  Derive g D ≥ v+1 infinitely, contradicting the cap.
    -- Pick a recurring D' (large) with g D' = v; set D = D' - δnat ≥ N, cap-floor.
    -- p - δnat = qbar ≤ v ⟹ LHS p ≤ g D, and p = qbar + δnat ≥ (v-1)+δnat ≥ v+1.
    -- Need one cell past Ncap with fdisp ≥ v+1.
    set D₀ : ℕ := max (N + δnat) (Ncap.val + δnat) with hD₀
    obtain ⟨D', hD'ge, hgD'⟩ := hrayrec D₀
    set D : ℕ := D' - δnat with hD
    have hDplus : D + δnat = D' := by omega
    have hDN : N ≤ D := by
      have : N + δnat ≤ D' := le_trans (le_max_left _ _) hD'ge
      omega
    have hDcap : Ncap.val ≤ a.val + D := by
      have : Ncap.val + δnat ≤ D' := le_trans (le_max_right _ _) hD'ge
      omega
    -- RHS qbar ≤ g (D + δnat) = g D' = v.
    have hRHS : (qbar : ℤ) ≤ g (D + δnat) := by
      rw [hDplus, hgD']; exact_mod_cast hq_le
    have hLHS : ((s : ℤ) - a.val) ≤ g D := (hstar D hDN).mpr hRHS
    -- p = qbar + δnat ≥ (v-1) + 2 = v+1.
    have hp_ge : (v : ℤ) + 1 ≤ (s : ℤ) - a.val := by
      rw [hp_val]
      have hqz : (v : ℤ) - 1 ≤ (qbar : ℤ) := by
        have := hq_ge; have := hvpos; omega
      have hδz : (2 : ℤ) ≤ (δnat : ℤ) := by exact_mod_cast hδ2
      omega
    have hge : (v : ℤ) + 1 ≤ g D := le_trans hp_ge hLHS
    -- But cap says g D ≤ v.
    have hle : g D ≤ (v : ℤ) := hcap_ray D hDcap
    omega

-- Axiom audit.  Every contributing lemma and the main theorem are `sorry`-free: they depend only
-- on the three standard classical axioms `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`).
#print axioms signals_agree_of_no_separator
#print axioms exists_top_recurring_value
#print axioms starP_ray
#print axioms cofinite_of_backward_closed
#print axioms band_of_boundedAbove

/-! ### Dispatch into the staircase winner -/

/-- **A `BandProvider` from bounded-above.**  For non-EI `c` that is bounded above, the axiom-clean
    `band_of_boundedAbove` supplies the band recurrence for every distinct *ordered* pair `a < b`;
    the `a ≠ b` interface of `BandProvider` is met by dispatching on `lt_or_gt_of_ne` and, in the
    `b < a` half, swapping the (symmetric) `separatorAtSlack` Boolean disagreement (`max` is
    symmetric). -/
theorem bandProvider_of_boundedAbove (c : Perm) (h : ¬ EventuallyIdentity c)
    (hbdd : ∃ B : ℕ, ∀ n : ℕ+, (c n).val ≤ n.val + B) : BandProvider c := by
  intro a b hab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b : directly.
    exact band_of_boundedAbove c h a b hlt hbdd
  · -- b < a : obtain for (b, a) and swap the separator's Boolean disagreement.
    obtain ⟨s, hse, hsM, hpin⟩ := band_of_boundedAbove c h b a hgt hbdd
    refine ⟨s, hse, by rw [max_comm]; exact hsM, fun D₀ => ?_⟩
    obtain ⟨D, hD, hsep⟩ := hpin D₀
    exact ⟨D, hD, by unfold separatorAtSlack at hsep ⊢; exact hsep.symm⟩

/-- **Bounded-above ⟹ Bob wins (axiom-clean).**  If `c` is not eventually identity and is bounded
    above (`∃ B, ∀ n, (c n).val ≤ n.val + B`), then Bob wins.  Routes through the parameterized
    band-top staircase `BobWins_of_bandProvider` fed by `bandProvider_of_boundedAbove` — entirely
    `sorry`-free.  This is the bounded-above branch of `main`'s winning-direction dispatch. -/
theorem notEI_boundedAbove_BobWins (c : Perm) (h : ¬ EventuallyIdentity c)
    (hbdd : ∃ B : ℕ, ∀ n : ℕ+, (c n).val ≤ n.val + B) : BobWins c :=
  BobWins_of_bandProvider c h (bandProvider_of_boundedAbove c h hbdd)

-- Axiom audit.  The bounded-above winner is `sorry`-free: `[propext, Classical.choice, Quot.sound]`.
#print axioms bandProvider_of_boundedAbove
#print axioms notEI_boundedAbove_BobWins

-- **Unbounded-above ⟹ Bob wins** is now proven (axiom-clean) in `GriddlesP4Lean.GrowStair` as
-- `notEI_unboundedAbove_BobWins`, via the **growing-lag staircase** whose per-pair separators come
-- from the axiom-clean `q2even` (the unbounded-above counterpart of `band_of_boundedAbove`).  This
-- file deliberately no longer defines it: `GrowStair` imports `Q2Even`, which imports this file, so
-- the theorem must live downstream of `q2even`.  `Answer.main` dispatches the unbounded-above
-- branch to `GrowStair.notEI_unboundedAbove_BobWins`.

end TrolleyRetrieval
