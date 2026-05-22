import GriddlesP4Lean.Defs
import Mathlib.Tactic

/-!
# The Restricted Separation Lemma (corrected winning-direction crux)

The abstract `Indistinguishable`/`LemmaA` route is the *wrong* vehicle for the winning
direction: it rules out discriminators at every reachable `t ≥ D`, but a real strategy can
only use a discriminator at `t ≥ T₁ + D` (after Phase 1 ends at `T₁ ≈ c k₀`).

The **monotone-right** Phase 2 fixes this: after Phase 1 brackets `k₀` to two candidates at
even time `T₁ = 2m+2`, Bob moves *right every turn*, so at displacement `D` he observes at
time exactly `t = T₁ + D` — the usable boundary — with safety automatic (`D ≥ 0` ⇒ position
`≥ k₀ ≥ 1`).  The winning direction then needs only the **separation** statement below.

It is the contrapositive of "a *twin* candidate pair forces `c` to be eventually identity".
This is *parity-free* (no `min ≡ D (mod 2)` condition), so it sidesteps the genuinely open
`Δ`-odd good-pair gap of the old `LemmaA`.  Empirically certified: zero twin pairs across
hundreds of non-eventually-identity permutations (N up to 20000); see `puzzle-4/notes.md`.

The proof is the one remaining mathematical crux: it reduces to elementary surjectivity
bookkeeping (`Σ_{n≤M} (c n − n) ≥ 0`; a permutation cannot stay below the diagonal on a
tail).  `Δ = 1` is *not* a shortcut (Δ≥2 twins exist, only in eventually-identity perms).
-/

namespace TrolleyRetrieval

/-- Cell at displacement `D ≥ 0` to the right of `p`. -/
def shiftR (p : ℕ+) (D : ℕ) : ℕ+ := ⟨p.val + D, by have := p.pos; omega⟩

@[simp] lemma shiftR_val (p : ℕ+) (D : ℕ) : (shiftR p D).val = p.val + D := rfl

@[simp] lemma shiftR_zero (p : ℕ+) : shiftR p 0 = p := by
  apply Subtype.ext; show p.val + 0 = p.val; omega

/-- **Restricted Separation Lemma (separation form).**

If `c` is not eventually the identity, then the two Phase-1 candidates `p₁, p₂` — the cells
whose labels are the consecutive integers `2m` and `2m+1` — are separated by some rightward
probe `D`, observed at time exactly `T₁ + D` with `T₁ = 2m+2`.  The probe signal in world
`k₀ = pᵢ` is `[c (pᵢ + D) < T₁ + D]`; separation means the two worlds give different signals,
so Bob learns which candidate is the true start and can guess its current cell.

The contrapositive ("for all `D` the probes agree" ⇒ eventually identity) is the *twin ⇒ EI*
lemma; this form is what the monotone-right strategy consumes directly. -/
theorem restricted_separation (c : Perm) (hne : ¬ EventuallyIdentity c)
    (m : ℕ) (p₁ p₂ : ℕ+)
    (hp₁ : (c p₁).val = 2 * m) (hp₂ : (c p₂).val = 2 * m + 1) :
    ∃ D : ℕ,
      ((c (shiftR p₁ D)).val < 2 * m + 2 + D) ≠ ((c (shiftR p₂ D)).val < 2 * m + 2 + D) := by
  sorry

end TrolleyRetrieval
