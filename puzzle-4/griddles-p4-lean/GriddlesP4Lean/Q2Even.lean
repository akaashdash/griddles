import GriddlesP4Lean.WinningAdaptive
import GriddlesP4Lean.BandBoundedAbove

/-!
# The "Q2-even" lemma: unbounded-above ⟹ separators at arbitrarily large even lag

For a permutation `c` of `ℕ⁺` that is **unbounded above** (no constant `B` bounds
`(c n).val ≤ n.val + B`), every ordered pair `a < b` has a slack-`s` separator at *some*
displacement, with `s` even and `≥ L` for **every** prescribed lag floor `L`:

  `q2even : ∃ s, Even s ∧ L ≤ s ∧ ∃ D, separatorAtSlack c a b s D`.

This is the unbounded-above counterpart of `band_of_boundedAbove`.

## The proof (contrapositive)

Suppose the conclusion fails for some `L`: **no even `s ≥ L` separates at any `D`** — the "bad
adversary" `(⋆)`.  Via `separatorAtSlack_iff_window`, writing `va := a.val + φ(a+D)` and
`vb := b.val + φ(b+D)` (where `φ n := (c n).val − n.val`), a separator at even slack `s` at
displacement `D` is exactly `min va vb < s ≤ max va vb`.  So `(⋆)` says: for every `D`, the
half-open window `(min va vb, max va vb]` contains *no even integer `≥ L`*.

Because `c` is injective, `va ≠ vb`, so the window is non-degenerate.  Whenever the window's top
edge `max va vb ≥ L + 1`, the absence of an even integer `≥ L` forces **width exactly 1** and
**`max va vb` odd** (`width1_of_no_even_in_window`).  Width 1 at the link of displacement `D`
reads `|c(a+D).val − c(b+D).val| = 1`, and since `b + D = a + (D + δ)` with `δ := b.val − a.val`,
this gives `φ(a+D) = φ(a + D + δ) + δ ± 1 ≥ φ(a + D + δ)` — i.e. **φ does not decrease going left
by `δ`** at any high link.

Unboundedness above provides, for any `M`, a **spike** cell `a + D₀` on the `a`-ray with
`φ(a+D₀) ≥ M` (`phi_spike_on_a_ray`).  Walking left in steps of `δ` from the spike
(`leftward_walk`), every link is high (its right endpoint carries the maintained `φ ≥ M`), so φ
stays `≥ M` all the way down to a **chain-start** `a + r` with `r < δ` — one of the `δ` fixed cells
`{a, a+1, …, a+δ−1}`.  But `φ` on those cells is bounded by a fixed `C` (`phi_le_on_initial`);
choosing `M > C` (and `M ≥ L+1`) yields `C ≥ φ(a+r) ≥ M > C`, a contradiction.  Hence `(⋆)` is
impossible and the conclusion holds. ∎
-/

namespace TrolleyRetrieval

variable {c : Perm}

/-! ### Lemma 1 — the width-1 window arithmetic (pure ℤ) -/

/-- **No even integer `≥ L` in a non-degenerate window forces width 1 and an odd top.**

    Let `x ≠ y` be integers and `L` a natural.  Suppose the half-open window `(min x y, max x y]`
    contains **no even integer `≥ L`**, and its top edge satisfies `max x y ≥ L + 1`.  Then
    `max x y − min x y = 1` and `max x y` is odd.

    *Proof.*  If the top `max x y` were even it would itself be an even integer `≥ L+1 > L` in the
    window (it lies in `(min, max]` since `min < max`), contradiction; so `max x y` is odd.  If the
    width were `≥ 2`, then `max x y − 1` is even, `≥ L` (as `max ≥ L+1`), and `> min x y`, hence in
    the window — contradiction; so the width is `≤ 1`.  As `x ≠ y` the width is `≥ 1`; thus `= 1`. -/
lemma width1_of_no_even_in_window (x y : ℤ) (L : ℕ) (hxy : x ≠ y)
    (htop : (L : ℤ) + 1 ≤ max x y)
    (hno : ∀ s : ℤ, Even s → (L : ℤ) ≤ s → min x y < s → s ≤ max x y → False) :
    max x y - min x y = 1 ∧ Odd (max x y) := by
  have hminlt : min x y < max x y := by
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)]; exact h
    · rw [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)]; exact h
  -- `max` is odd: otherwise it is an even integer ≥ L in the window.
  have hodd : Odd (max x y) := by
    rcases Int.even_or_odd (max x y) with hev | hodd
    · exact absurd (hno (max x y) hev (by omega) hminlt (le_refl _)) (by simp)
    · exact hodd
  -- width ≤ 1: otherwise `max - 1` is even, ≥ L, and in the window.
  have hwle : max x y - min x y ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    -- max - 1 even (since max odd), ≥ L (max ≥ L+1), > min (width ≥ 2), ≤ max.
    have hev : Even (max x y - 1) := by
      rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
    exact hno (max x y - 1) hev (by omega) (by omega) (by omega)
  exact ⟨by omega, hodd⟩

/-! ### Lemma 2 — φ spikes arbitrarily high on the `a`-ray (from unboundedness above)

`hub` says no `B` bounds `(c n).val ≤ n.val + B` for all `n`.  `push_neg` turns it into
`∀ B, ∃ n, n.val + B < (c n).val`, i.e. `∀ B, ∃ n, (B : ℤ) < fdisp c n + 1`, equivalently
`fdisp c n ≥ B` for some `n`.  We additionally need the spike to lie on the `a`-ray; the finitely
many cells `n < a.val` have `fdisp` bounded, so pushing `M` past that bound forces the spike onto
the ray. -/

/-- A finite upper bound for `fdisp c` over the initial segment `1 ≤ n < a` (cells *below* `a`). -/
private noncomputable def initFdispBound (c : Perm) (a : ℕ+) : ℤ :=
  (Finset.Icc (1 : ℕ+) a).sup' (by exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, a.one_le⟩⟩)
    (fun n => fdisp c n)

private lemma le_initFdispBound (c : Perm) (a : ℕ+) {n : ℕ+} (hn : n ≤ a) :
    fdisp c n ≤ initFdispBound c a := by
  apply Finset.le_sup' (fun n => fdisp c n)
  exact Finset.mem_Icc.mpr ⟨n.one_le, hn⟩

/-- **Unbounded-above gives a φ-spike on the `a`-ray.**  For every `M : ℤ` there is a displacement
    `D₀` with `(M : ℤ) ≤ fdisp c (cellAt a D₀)`. -/
lemma phi_spike_on_a_ray (c : Perm) (a : ℕ+)
    (hub : ¬ ∃ B : ℕ, ∀ n : ℕ+, (c n).val ≤ n.val + B) :
    ∀ M : ℤ, ∃ D₀ : ℕ, (M : ℤ) ≤ fdisp c (cellAt a D₀) := by
  classical
  intro M
  -- push_neg the unbounded-above hypothesis to the ℕ-threshold form.
  push_neg at hub
  -- hub : ∀ B : ℕ, ∃ n : ℕ+, n.val + B < (c n).val
  -- Take a numeric bound `B` past which fdisp ≥ M is forced, *and* past the initial-segment bound.
  -- Choose B so large that any witnessing n must be on the ray and have fdisp ≥ M.
  set C : ℤ := initFdispBound c a with hC
  -- Pick a natural threshold T ≥ max(M, C) + a.val so the witness `n` has `fdisp ≥ M` and `n ≥ a`.
  set T : ℕ := (max M C).toNat + a.val with hT
  obtain ⟨n, hn⟩ := hub T
  -- hn : n.val + T < (c n).val ⟹ fdisp c n = (c n).val - n.val > T ≥ max M C ≥ M (as ℤ).
  have hfn : (T : ℤ) < fdisp c n := by
    unfold fdisp
    have : (n.val : ℤ) + (T : ℤ) < (c n).val := by exact_mod_cast hn
    omega
  -- `n` is on the ray: `n ≥ a`.  Otherwise `fdisp c n ≤ C`, but `fdisp c n > T ≥ C`.
  have hna : a ≤ n := by
    by_contra hlt
    push_neg at hlt  -- hlt : n < a
    have hle : fdisp c n ≤ C := le_initFdispBound c a (le_of_lt hlt)
    have hTC : (C : ℤ) ≤ (T : ℤ) := by
      rw [hT]; push_cast
      have hCmax : C ≤ max M C := le_max_right _ _
      have hself : max M C ≤ ((max M C).toNat : ℤ) := Int.self_le_toNat _
      have hav : (0 : ℤ) ≤ (a.val : ℤ) := by positivity
      omega
    omega
  -- Convert `n ≥ a` to a displacement on the ray: D₀ := n.val - a.val.
  refine ⟨n.val - a.val, ?_⟩
  have hcell : cellAt a (n.val - a.val) = n := by
    apply Subtype.ext; show a.val + (n.val - a.val) = n.val
    have : a.val ≤ n.val := (PNat.coe_le_coe _ _).2 hna
    omega
  rw [hcell]
  -- M ≤ T < fdisp c n.
  have hMT : (M : ℤ) ≤ (T : ℤ) := by
    rw [hT]; push_cast
    have hMmax : M ≤ max M C := le_max_left _ _
    have hself : max M C ≤ ((max M C).toNat : ℤ) := Int.self_le_toNat _
    have hav : (0 : ℤ) ≤ (a.val : ℤ) := by positivity
    omega
  omega

/-! ### Lemma 3 — φ is bounded on the chain-start cells `{a, a+1, …, a+δ−1}` -/

/-- A finite upper bound for `fdisp c` over the chain-start window `a ≤ n ≤ a + δ` (which contains
    every chain-start `a + r`, `0 ≤ r < δ`). -/
private noncomputable def chainStartBound (c : Perm) (a : ℕ+) (δ : ℕ) : ℤ :=
  (Finset.Icc (1 : ℕ+) (a + ⟨δ + 1, Nat.succ_pos δ⟩)).sup'
    (by exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, (a + _).one_le⟩⟩)
    (fun n => fdisp c n)

private lemma fdisp_le_chainStartBound (c : Perm) (a : ℕ+) (δ : ℕ) {r : ℕ} (hr : r ≤ δ) :
    fdisp c (cellAt a r) ≤ chainStartBound c a δ := by
  apply Finset.le_sup' (fun n => fdisp c n)
  rw [Finset.mem_Icc]
  refine ⟨(cellAt a r).one_le, ?_⟩
  apply (PNat.coe_le_coe _ _).1
  rw [cellAt_val]
  show a.val + r ≤ (a + ⟨δ + 1, Nat.succ_pos δ⟩).val
  rw [PNat.add_coe]
  show a.val + r ≤ a.val + (δ + 1)
  omega

/-! ### Lemma 4 — the leftward walk: φ stays high all the way to the chain-start

Under the bad adversary `(⋆)` (no even `s ≥ L` separates at any `D`), starting from a spike
`fdisp c (cellAt a D₀) ≥ M` with `M ≥ L + 1`, walking left in steps of `δ` keeps `fdisp ≥ M`:
each link is high (its right endpoint carries the maintained `fdisp ≥ M`), so the width-1 lemma
gives `φ(left) = φ(right) + δ ± 1 ≥ φ(right) ≥ M`.

We package `(⋆)` as `hbad` and feed it the (already proven, axiom-clean)
`signals_agree_of_no_separator` window engine through `separatorAtSlack_iff_window`. -/

/-- **Single leftward step.**  Under `(⋆)`, if the right endpoint `a + (D + δ)` has `fdisp ≥ M`
    (with `M ≥ L+1` and `δ = b.val − a.val ≥ 1`), then the left endpoint `a + D` has
    `fdisp c (cellAt a D) ≥ fdisp c (cellAt a (D + δ)) ≥ M`.

    The link of displacement `D` is the separator pair `(a, b)` at `D` (since `b + D = a + (D+δ)`).
    `(⋆)` forbids even `s ≥ L` separators there, so by `separatorAtSlack_iff_window` no even integer
    `≥ L` lies in the window `(min va vb, max va vb]`.  The right endpoint gives
    `vb = b.val + φ(a+(D+δ)) ≥ b.val + M ≥ L + 1 ≤ max`, so `width1_of_no_even_in_window` yields
    `|va − vb| = 1`, whence `va ≥ vb − 1`, i.e. `φ(a+D) ≥ φ(a+(D+δ)) + δ − 1 ≥ M`. -/
lemma leftward_step {a b : ℕ+} (hab : a < b) {L : ℕ} {M : ℤ} (hML : (L : ℤ) + 1 ≤ M)
    (hbad : ∀ s : ℕ, Even s → L ≤ s → ∀ D : ℕ, ¬ separatorAtSlack c a b s D)
    (D : ℕ) (hright : (M : ℤ) ≤ fdisp c (cellAt a (D + (b.val - a.val)))) :
    (M : ℤ) ≤ fdisp c (cellAt a D) := by
  classical
  set δ : ℕ := b.val - a.val with hδ
  have habval : a.val < b.val := by exact_mod_cast hab
  have hδpos : 1 ≤ δ := by omega
  -- The two displaced labels at the link of displacement D, as integers.
  set x : ℤ := ((c (cellAt a D)).val : ℤ) with hx
  set y : ℤ := ((c (cellAt b D)).val : ℤ) with hy
  -- va = x - D, vb = y - D.
  set va : ℤ := x - D with hva
  set vb : ℤ := y - D with hvb
  -- Injectivity: x ≠ y, hence va ≠ vb.
  have hne_cell : cellAt a D ≠ cellAt b D := by
    intro heq
    have : (cellAt a D).val = (cellAt b D).val := by rw [heq]
    rw [cellAt_val, cellAt_val] at this; omega
  have hxy : x ≠ y := by
    intro heq
    rw [hx, hy] at heq
    apply hne_cell
    apply c.injective
    apply PNat.coe_injective
    exact_mod_cast heq
  have hvavb : va ≠ vb := by rw [hva, hvb]; omega
  -- Right endpoint controls vb: cellAt a (D+δ) = cellAt b D.
  have hcellb : cellAt a (D + δ) = cellAt b D := (cellAt_b_eq_a_shift (le_of_lt hab) D).symm
  -- fdisp c (cellAt b D) = vb - b.val  (since (cellAt b D).val = b.val + D and vb = y - D).
  have hvb_eq : fdisp c (cellAt b D) = vb - b.val := by
    rw [hvb, hy]; unfold fdisp; rw [cellAt_val]; push_cast; ring
  -- right hyp transported: M ≤ vb - b.val.
  have hright_b : (M : ℤ) ≤ vb - b.val := by rw [← hvb_eq, ← hcellb]; exact hright
  -- and hence M ≤ vb (b.val ≥ 0).
  have hright' : (M : ℤ) ≤ vb := by
    have : (0 : ℤ) ≤ (b.val : ℤ) := by positivity
    omega
  -- top edge: max va vb ≥ vb ≥ M ≥ L+1.
  have htop : (L : ℤ) + 1 ≤ max va vb := le_trans hML (le_trans hright' (le_max_right _ _))
  -- (⋆): no even integer ≥ L in the window (min va vb, max va vb].
  -- ℕ labels and their ℤ images (folded by the earlier `set x`/`set y`).
  set xn : ℕ := (c (cellAt a D)).val with hxn
  set yn : ℕ := (c (cellAt b D)).val with hyn
  have hxn_eq : (xn : ℤ) = x := hx.symm
  have hyn_eq : (yn : ℤ) = y := hy.symm
  -- va = ↑xn - ↑D, vb = ↑yn - ↑D (subtracting the common D preserves order).
  have hva_xn : va = (xn : ℤ) - D := by rw [hva, hxn_eq]
  have hvb_yn : vb = (yn : ℤ) - D := by rw [hvb, hyn_eq]
  -- Cast min/max to ℤ.
  have hcast_min : (min xn yn : ℤ) = min (xn : ℤ) (yn : ℤ) := by push_cast; rfl
  have hcast_max : (max xn yn : ℤ) = max (xn : ℤ) (yn : ℤ) := by push_cast; rfl
  -- The ℤ window edges as shifts of the ℕ min/max (subtracting the common D commutes with min/max).
  have hmin_shift : (min xn yn : ℤ) - D = min va vb := by
    rw [hcast_min, hva_xn, hvb_yn]
    rcases le_total (xn : ℤ) (yn : ℤ) with hle | hle
    · rw [min_eq_left hle, min_eq_left (by omega : (xn : ℤ) - D ≤ (yn : ℤ) - D)]
    · rw [min_eq_right hle, min_eq_right (by omega : (yn : ℤ) - D ≤ (xn : ℤ) - D)]
  have hmax_shift : (max xn yn : ℤ) - D = max va vb := by
    rw [hcast_max, hva_xn, hvb_yn]
    rcases le_total (xn : ℤ) (yn : ℤ) with hle | hle
    · rw [max_eq_right hle, max_eq_right (by omega : (xn : ℤ) - D ≤ (yn : ℤ) - D)]
    · rw [max_eq_left hle, max_eq_left (by omega : (yn : ℤ) - D ≤ (xn : ℤ) - D)]
  have hno : ∀ s : ℤ, Even s → (L : ℤ) ≤ s → min va vb < s → s ≤ max va vb → False := by
    intro s hev hLs hmin hmax
    -- s ≥ L ≥ 0, so s is a natural; recover sN with (sN:ℤ) = s.
    have hs0 : 0 ≤ s := le_trans (by positivity) hLs
    set sN : ℕ := s.toNat with hsN
    have hsNeq : (sN : ℤ) = s := Int.toNat_of_nonneg hs0
    have hsN_even : Even sN := by
      rcases hev with ⟨k, hk⟩
      have hk0 : 0 ≤ k := by omega
      refine ⟨k.toNat, ?_⟩
      have hkt : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
      have heq : (sN : ℤ) = (k.toNat : ℤ) + (k.toNat : ℤ) := by rw [hsNeq, hk, hkt]
      exact_mod_cast heq
    have hsN_ge : L ≤ sN := by
      have hcast : (L : ℤ) ≤ (sN : ℤ) := by rw [hsNeq]; exact hLs
      exact_mod_cast hcast
    -- The separator at slack sN, displacement D, would exist via the window characterization.
    apply hbad sN hsN_even hsN_ge D
    rw [separatorAtSlack_iff_window]
    refine ⟨?_, ?_⟩
    · -- min xn yn < D + sN
      have hkey : (min xn yn : ℤ) < (D : ℤ) + sN := by rw [hsNeq]; omega
      have : (min xn yn : ℤ) < ((D + sN : ℕ) : ℤ) := by push_cast; omega
      exact_mod_cast this
    · -- D + sN ≤ max xn yn
      have hkey : (D : ℤ) + sN ≤ (max xn yn : ℤ) := by rw [hsNeq]; omega
      have : ((D + sN : ℕ) : ℤ) ≤ (max xn yn : ℤ) := by push_cast; omega
      exact_mod_cast this
  -- width 1 + odd top.
  obtain ⟨hwidth, _hodd⟩ := width1_of_no_even_in_window va vb L hvavb htop hno
  -- width 1: max - min = 1, so |va - vb| = 1, so va ≥ vb - 1.
  have hva_ge : vb - 1 ≤ va := by
    rcases le_total va vb with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hwidth; omega
    · rw [min_eq_right hle, max_eq_left hle] at hwidth; omega
  -- φ(a+D) = va - a.val  (since fdisp c (cellAt a D) = x - (a.val + D) = va - a.val).
  have hfdisp_a : fdisp c (cellAt a D) = va - a.val := by
    rw [hva, hx]; unfold fdisp; rw [cellAt_val]; push_cast; ring
  -- goal: M ≤ fdisp c (cellAt a D) = va - a.val.
  rw [hfdisp_a]
  -- va ≥ vb - 1, and vb - b.val ≥ M, with b.val - a.val ≥ 1:
  --   va - a.val ≥ (vb - 1) - a.val = (vb - b.val) + (b.val - a.val) - 1 ≥ M + 1 - 1 = M.
  have hba : (1 : ℤ) ≤ (b.val : ℤ) - a.val := by
    have : a.val < b.val := habval; push_cast; omega
  -- hva_ge : vb - 1 ≤ va ; hright_b : M ≤ vb - b.val ; hba : 1 ≤ b.val - a.val.
  omega

/-- **The leftward walk (induction).**  Under `(⋆)`, from a spike at displacement `D₀ = r + k·δ`
    (with `M ≥ L+1`, `δ ≥ 1`) walking left `k` steps of `δ` keeps `fdisp ≥ M`: in particular the
    chain-start `a + r` (`r = D₀ mod δ`) carries `fdisp c (cellAt a r) ≥ M`. -/
lemma leftward_walk {a b : ℕ+} (hab : a < b) {L : ℕ} {M : ℤ} (hML : (L : ℤ) + 1 ≤ M)
    (hbad : ∀ s : ℕ, Even s → L ≤ s → ∀ D : ℕ, ¬ separatorAtSlack c a b s D)
    (r : ℕ) (k : ℕ) (hspike : (M : ℤ) ≤ fdisp c (cellAt a (r + k * (b.val - a.val)))) :
    (M : ℤ) ≤ fdisp c (cellAt a r) := by
  set δ : ℕ := b.val - a.val with hδ
  induction k with
  | zero => simpa using hspike
  | succ k ih =>
    -- spike at r + (k+1)δ = (r + kδ) + δ.  One leftward step gives spike at r + kδ.
    apply ih
    have heq : r + (k + 1) * δ = (r + k * δ) + δ := by ring
    rw [heq] at hspike
    exact leftward_step hab hML hbad (r + k * δ) hspike

/-! ### Assembly: the Q2-even lemma -/

/-- **Q2-even.**  For an unbounded-above permutation `c`, every ordered pair `a < b` has separators
    at *arbitrarily large even lag*: for every `L` there is an even `s ≥ L` and a displacement `D`
    with a slack-`s` separator at `D`. -/
theorem q2even (c : Perm)
    (hub : ¬ ∃ B : ℕ, ∀ n : ℕ+, (c n).val ≤ n.val + B)
    (a b : ℕ+) (hab : a < b) (L : ℕ) :
    ∃ s : ℕ, Even s ∧ L ≤ s ∧ ∃ D : ℕ, separatorAtSlack c a b s D := by
  classical
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ s, Even s → L ≤ s → ∀ D, ¬ separatorAtSlack c a b s D  (the bad adversary ⋆)
  have hbad : ∀ s : ℕ, Even s → L ≤ s → ∀ D : ℕ, ¬ separatorAtSlack c a b s D := hcon
  set δ : ℕ := b.val - a.val with hδ
  have habval : a.val < b.val := by exact_mod_cast hab
  have hδpos : 1 ≤ δ := by omega
  -- chain-start bound C, and choose M = max(L+1, C+1).
  set C : ℤ := chainStartBound c a δ with hC
  set M : ℤ := max ((L : ℤ) + 1) (C + 1) with hM
  have hML : (L : ℤ) + 1 ≤ M := le_max_left _ _
  have hMC : C + 1 ≤ M := le_max_right _ _
  -- spike at displacement D₀.
  obtain ⟨D₀, hspike⟩ := phi_spike_on_a_ray c a hub M
  -- write D₀ = r + k·δ with r = D₀ % δ < δ.
  set r : ℕ := D₀ % δ with hr
  set k : ℕ := D₀ / δ with hk
  have hrk : D₀ = r + k * δ := by
    rw [hr, hk]; rw [Nat.mod_add_div']  -- (D₀%δ) + (D₀/δ)*δ = D₀
  have hr_lt : r < δ := Nat.mod_lt _ (by omega)
  -- transport the spike to the (r + k·δ) form.
  have hspike' : (M : ℤ) ≤ fdisp c (cellAt a (r + k * δ)) := by rw [← hrk]; exact hspike
  -- leftward walk to the chain-start.
  have hstart : (M : ℤ) ≤ fdisp c (cellAt a r) := leftward_walk hab hML hbad r k hspike'
  -- but fdisp at chain-start ≤ C < M.
  have hbound : fdisp c (cellAt a r) ≤ C := fdisp_le_chainStartBound c a δ (le_of_lt hr_lt)
  -- contradiction: M ≤ fdisp ≤ C < C + 1 ≤ M.
  omega

-- Axiom audit.  Every contributing lemma and the main theorem are `sorry`-free: they depend only on
-- the three standard classical axioms `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`).
#print axioms width1_of_no_even_in_window
#print axioms phi_spike_on_a_ray
#print axioms fdisp_le_chainStartBound
#print axioms leftward_step
#print axioms leftward_walk
#print axioms q2even

end TrolleyRetrieval
