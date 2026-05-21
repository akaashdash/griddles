import GriddlesP4Lean.Defs

/-!
# Lemma A: distinguishability lemma

For a permutation `c : ℕ+ ≃ ℕ+` and two starting cells `a < b`, we say the pair is
*indistinguishable* if, at every reachable `(D, t)`, the signals from the two trajectories
agree.  In terms of `c` alone this is equivalent to:

* `c (a + D)` and `c (b + D)` are consecutive integers for every `D ≥ 0`, and
* `min(c (a + D), c (b + D)) ≡ D (mod 2)`.

**Lemma A.**  An indistinguishable pair exists iff `c` is eventually identity (and then
necessarily `b = a + 1`).

The forward direction is the heart of the winning argument: contrapositively, *if `c` is
not eventually identity, every pair of cells is distinguishable*.

## Proof sketch

Set `Δ = b − a` and `σ(D) = sign(c(b+D) − c(a+D)) ∈ {−1, +1}` (well-defined since the two
values are consecutive integers).  Indistinguishability gives `c(n + Δ) = c(n) + σ(n−a)`
for `n ≥ a`.

1. **`σ` is `Δ`-periodic.**  Iterating: `c(n + 2Δ) − c(n) = σ(n−a) + σ(n−a+Δ)`.  If this
   were `0`, `c` would not be injective.  Hence `σ(n−a) = σ(n−a+Δ)`.

2. **`σ ≡ +1`.**  Iterating further: `c(n + kΔ) = c(n) + k · σ(n−a)`.  If `σ < 0`
   anywhere, the values would tend to `−∞`, impossible for `c : ℕ+ → ℕ+`.

3. **`Δ ≥ 2` is impossible.**  From `c(n + Δ) = c(n) + 1`, the image of `c` on `{n ≥ a}`
   is the union of `Δ` arithmetic rays of step `1`.  The largest initial value `v_max` is
   contained in all `Δ` rays, so it is hit `Δ` times — contradicting injectivity once
   `Δ ≥ 2`.

4. **`Δ = 1` ⇒ `c` is eventually identity.**  Then `c(n + 1) = c(n) + 1` for `n ≥ a`, so
   `c(n) = n + (c(a) − a)` on `{n ≥ a}`.  Bijectivity of `c : ℕ+ → ℕ+` forces the offset
   to be `0`, i.e. `c(n) = n` for all `n ≥ a`.

## Status

This file states the predicate `Indistinguishable` and the main Lemma A.  The proof is
deferred. -/

namespace TrolleyRetrieval

/-- Two cells `a < b` are *indistinguishable* (relative to `c`) if for every displacement
    `D ≥ 0` and every time `t ≥ D` with `t ≡ D (mod 2)`, the signals at positions
    `a + D` and `b + D` at time `t` are equal. -/
def Indistinguishable (c : Perm) (a b : ℕ+) : Prop :=
  ∀ D : ℕ, ∀ t : ℕ, (t : ℤ) ≥ D → ((t : ℤ) - D) % 2 = 0 →
    ((c ⟨a.val + D, Nat.lt_of_lt_of_le a.property (Nat.le_add_right _ _)⟩).val < t ↔
     (c ⟨b.val + D, Nat.lt_of_lt_of_le b.property (Nat.le_add_right _ _)⟩).val < t)

/-- **Lemma A (forward).**  If a pair `(a, b)` with `a < b` is indistinguishable, then
    `b = a + 1` and `c` is eventually identity from position `a`. -/
theorem Indistinguishable_implies_eventually_identity
    {c : Perm} {a b : ℕ+} (hab : a < b)
    (h : Indistinguishable c a b) :
    (b = a + 1) ∧ (∀ n : ℕ+, a ≤ n → c n = n) := by
  sorry

/-- **Lemma A (corollary used by the winning direction).**  If `c` is not eventually
    identity, then *no* pair of starting cells is indistinguishable. -/
theorem not_eventually_identity_implies_distinguishable
    {c : Perm} (h : ¬ EventuallyIdentity c) :
    ∀ a b : ℕ+, a < b → ¬ Indistinguishable c a b := by
  intro a b hab h_indist
  obtain ⟨_, h_ei⟩ := Indistinguishable_implies_eventually_identity hab h_indist
  exact h ⟨a, h_ei⟩

end TrolleyRetrieval
