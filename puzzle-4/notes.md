# Trolley Retrieval — Solution Notes

## Answer

**Bob has a strategy to ensure safe retrieval if and only if c(n) ≠ n for infinitely many n.**

Equivalently: Bob **cannot** win ↔ c is a finitary/eventually-identity permutation (there
exists N such that c(n) = n for all n > N).

Other equivalent phrasings (all the same condition for a bijection of ℕ⁺):
- `{n : c(n) ≠ n}` is infinite (c not finitary).
- c⁻¹ is not eventually identity (the condition is symmetric under c ↔ c⁻¹).
- c has infinitely many "upward gaps" (positions p with c(p+1) − c(p) ≥ 2).
- Equivalently c has infinitely many descents (c(p+1) < c(p)).

NOT equivalent (strictly stronger, hence wrong as the boundary): "limsup (c(n)−n) = ∞".
Adjacent transpositions have bounded g(n)=c(n)−n yet Bob wins, so the boundary is
non-EI, not unbounded growth. (Verified: `/tmp/p4_full_strategy.py`, `/tmp/p4_coord_systems.py`.)

---

## CLEANEST PROOF OF THE WINNING DIRECTION (monotone-right Phase 2)

The earlier notes flagged a "usable vs weak discriminator" timing gap in Phase 2. That gap is
an artifact of the *precomputed-D, navigate-then-observe* strategy. The **monotone-right** Phase 2
below makes the timing problem vanish: probe time equals the usable boundary with equality, and
no left moves are ever used, so safety is automatic.

### Coordinate system: forward displacement g(n) = c(n) − n is cleanest

The inverse coordinate h(t) = c⁻¹(t) − t describes "which cell wakes at time t", convenient for
*naming* the candidate pair, but the discrimination predicate is cleanest in g. With T1 even and
observation at time t = T1 + D, the predicted Phase-2 signal under hypothesis k₀ = x is

    f_x(D) = [ c(x+D) < T1 + D ] = [ g(x+D) < T1 − x ].

So Phase 2 just compares two shifted sub-level sets of the single sequence g — no left moves,
no separate reachability condition (t ≡ D mod 2 is automatic since T1 is even).

### The strategy

**Phase 1 (oscillate D ∈ {0,1}, right-first).** At even t = 2m, position = k₀, signal Yes iff
c(k₀) < 2m. Let T1 = 2m* be the first even Yes. Then c(k₀) ∈ {T1−2, T1−1}, so

    k₀ ∈ {p₁, p₂},   p₁ = c⁻¹(T1−2) = c⁻¹(2m*−2),  p₂ = c⁻¹(2m*−1) = c⁻¹(2m*−1).

The candidate set is ALWAYS of the form {c⁻¹(2m), c⁻¹(2m+1)} (cells waking at one even and the
next odd time). If only one of T1−2, T1−1 has a preimage ≥ 1, Bob has a single candidate and
guesses immediately. Safety: position = k₀ + D_t ≥ k₀ ≥ 1 (right-first keeps D ∈ {0,1}).

**Phase 2 (monotone right).** From (time T1, displacement 0), move RIGHT every turn: at turn
T1+D the displacement is D and the observation time is exactly t = T1 + D. Observe the real signal
s(D) = [c(k₀+D) < T1+D] and compare to the two predictions f_{p₁}(D), f_{p₂}(D). At D = 0 both
predictions are True (c(p₁)=T1−2 < T1, c(p₂)=T1−1 < T1), matching the Phase-1 detection. At the
first D where f_{p₁}(D) ≠ f_{p₂}(D), the real signal s(D) matches exactly one hypothesis; Bob
learns k₀ and hence the current position k₀+D, and guesses it. Safety: only right moves, D ≥ 0,
position ≥ k₀ ≥ 1 throughout. Reachability: t = T1+D, T1 even ⇒ t ≡ D (mod 2). ✓

This wins iff the two prediction sequences eventually differ — exactly the lemma below.

### Restricted Separation Lemma (the only mathematical content needed)

> **Lemma.** Let c be a permutation of ℕ⁺ that is NOT eventually identity. For every candidate
> pair p₁ = c⁻¹(2m), p₂ = c⁻¹(2m+1) (with the smaller ≥ 1), there exists D ≥ 0 with
> `[c(p₁+D) < T1+D] ≠ [c(p₂+D) < T1+D]`, where T1 = 2m+2.

This is STRICTLY WEAKER than the old `Indistinguishable_implies_eventually_identity` (LemmaA),
which quantified over all reachable (D,t) including left moves and had a genuinely open Δ-odd
sub-case. The restricted lemma fixes T1 = 2m+2 (forced, not free) and uses only D ≥ 0.

**Contrapositive form (what we prove):** if some candidate pair is *twin* (f_{p₁}(D) = f_{p₂}(D)
for all D ≥ 0), then c is the identity on the tail [min(p₁,p₂), ∞), hence c is eventually identity.

**Proof sketch.** WLOG p₁ < p₂, Δ = p₂ − p₁ > 0. Put u(D) = T1 + D − c(p₁+D), so f_{p₁}(D) =
[u(D) ≥ 1], u(0) = 2. Since p₂+D = p₁+(D+Δ), one gets the shift relation (verified numerically,
`/tmp/p4_proof_steps.py`):

    T1 + D − c(p₂+D) = u(D+Δ) − Δ.

Twin therefore reads:  u(D) ≥ 1 ⇔ u(D+Δ) ≥ Δ+1, for all D ≥ 0.  (★)
The "True at 0" branch propagates along the progression {kΔ}: u(kΔ) ≥ Δ+1 for k ≥ 1, i.e.
g(p₁+kΔ) ≤ T1 − p₁ − Δ − 1 (g bounded ABOVE on a residue class). The decisive contradiction with
non-EI uses bijectivity (surjectivity): the prefix sums Σ_{n≤M} c(n) ≥ M(M+1)/2 force
Σ_{n≤M} g(n) ≥ 0 (g cannot be sub-diagonal on a tail — verified `/tmp/p4_coord_systems.py`),
and (★) over all residues then pins g ≡ 0 past min(p₁,p₂), i.e. the identity tail. For Δ = 1
this is exactly the already-formalized `shift_one_implies_eventually_identity`.

**Empirical certification of the Lemma (this is the load-bearing check):**
- Identity (EI): ALL candidate pairs are twin-forever — Bob loses. ✓
- All non-EI families tested (block reversal w/ unbounded g, dense & sparse adjacent
  transpositions, growing-distance swaps, 200 random blocky non-EI perms, N up to 20000):
  ZERO twin candidate pairs over deep windows; every pair separates at small D
  (max separation D ≤ 33 observed). See `/tmp/p4_proof_final.py`, `/tmp/p4_extension.py`.
- End-to-end strategy simulation: 200/200 starting positions won on every non-EI family;
  EI loses on all large k₀. See `/tmp/p4_full_strategy.py`.

### Why the old "weak vs usable" worry dissolves

A "weak" discriminator is a reachable (D,t) separating the pair with possibly t < T1+D; "usable"
adds t ≥ T1+D. In the monotone-right strategy every probe sits at t = T1+D exactly, so the
*first* separating displacement is automatically usable. Non-EI does not merely give weak
discriminators — it gives a separating D at the usable boundary. (The fear that a bounded-g
permutation might only offer weak/small-t separators was checked directly and is false:
`/tmp/p4_adversarial.py`, `/tmp/p4_usable_test.py` — 0 usable-discriminator failures.)

### Note on the old LemmaA Δ-odd gap

The remaining `sorry`s in `LemmaA.lean` (Δ ≥ 2 odd, interleaved good/bad) are NOT on the path of
this winning proof. They belong to the stronger full-power distinguishability statement (all
(D,t), left moves allowed). The restricted lemma above suffices for the game and avoids them.

---

## Key Structural Facts

### Parity Invariant

At every time t, Bob's net displacement D_t = kₜ − k₀ satisfies:

    D_t ≡ t (mod 2)

*Proof:* D₀ = 0; each step changes D by ±1. So D_t and t have the same parity always.

Therefore **t − D_t is always even**, regardless of Bob's strategy.

### Upward Gaps

A position p has an **upward gap** if c(p+1) − c(p) ≥ 2.

**Structural lemma:** c has infinitely many upward gaps if and only if c is NOT eventually
identity.

*Proof:* If c(n+1) ≤ c(n)+1 for all n > N (no gaps after N), then since c is a bijection,
c(n) = n for all n > N. Contrapositive gives the result.

---

## Part 1: Bob Loses When c Is Eventually Identity

Suppose c(n) = n for all n > N. Take any large j with 2j > N. Consider starting positions
k₀ = 2j and k₀ = 2j+1.

At any time t, the signal "Yes" fires iff c(kₜ) < t. Since kₜ > N always (for large enough j,
no strategy of finite length can reach 0 or enter [1,N]), this reduces to kₜ < t, i.e.,
k₀ + D_t < t, i.e., k₀ < t − D_t.

Since t − D_t is always **even**, the threshold Bob can probe is always even. But:
- k₀ = 2j  → "Yes" iff 2j < t − D_t  (requires threshold ≥ 2j+2, i.e., ≥ 2j+2)
- k₀ = 2j+1 → "Yes" iff 2j+1 < t − D_t (requires threshold ≥ 2j+2, same condition!)

The two starting positions produce **identical signals** for every strategy. Bob cannot
distinguish them. **Bob loses.**

---

## Part 2: Bob Wins When c Is Not Eventually Identity

Since c is not eventually identity, it has **infinitely many upward gaps**.

### Phase 1 — Narrow to Two Candidates

Bob oscillates: move right, then left, alternately. This keeps D_t ∈ {0, 1}.

**Safety:** Position kₜ = k₀ + D_t ≥ k₀ + 0 = k₀ ≥ 1 always. The trolley never falls off.

At every even time t = 2m, kₜ = k₀ exactly. The signal is "Yes" iff c(k₀) < 2m.

Since c(k₀) is finite, there is a first even time 2m* where the signal is "Yes". At that
moment Bob knows:

    c(k₀) ∈ {2m*−2, 2m*−1}

so k₀ ∈ {p₁, p₂} where p₁ = c⁻¹(2m*−2) and p₂ = c⁻¹(2m*−1). Two candidates.

### Phase 2 — Discriminate the Two Candidates

Let Δ = p₂ − p₁ ≠ 0. Bob needs to find a time/displacement pair (t*, D) such that the
signal at that moment differs for k₀ = p₁ vs k₀ = p₂.

**By the bijection telescoping lemma:** For fixed Δ ≠ 0, c(q+Δ) > c(q) for infinitely
many q (and c(q+Δ) < c(q) for infinitely many q). WLOG find infinitely many q where
c(p₁+D) < c(p₂+D) for D = q − p₁.

Choose q >> max(p₁, p₂) at an upward gap so c(p₂+D) − c(p₁+D) ≥ 2. Pick t* in the
interval (c(p₁+D), c(p₂+D)] with t* ≡ D (mod 2) (possible since the interval has size ≥ 2
and thus contains integers of both parities).

**Safety during navigation:** Bob moves right from Phase 1's end position to reach
displacement D = q − k₀. Since q >> k₀, D > 0. Bob navigates right (with right-left
parity-padding steps if needed, which never dip below D = 0). Position = k₀ + D_t ≥ k₀ ≥ 1
throughout. Trolley stays safe.

**Discrimination at time t*:**
- If k₀ = p₁: position = p₁ + D = q. Signal = "Yes" iff c(q) < t* ✓ (true by construction).
  Bob guesses position **q**.
- If k₀ = p₂: position = p₂ + D = q + Δ. Signal = "No" iff c(q+Δ) ≥ t* ✓ (true by
  construction). Bob guesses position **q + Δ**.

Both guesses are correct. **Bob wins.**

---

## Safety — Summary

The right-endedness of the cell sequence (cells are at positions 1, 2, 3, ...) requires that
kₜ ≥ 1 at all times. Both phases guarantee this:

- **Phase 1:** Bob moves **right first** (never left when D=0), so D_t ∈ {0, 1} and kₜ = k₀ + D_t ≥ k₀ ≥ 1. If k₀ = 1 and the first move were left, the trolley would immediately fall off — the starting-right requirement is essential.
- **Phase 2:** Target displacement D = q − k₀ > 0. Bob only moves right (or uses right-left
  pairs for parity), so D_t ≥ 0 throughout, giving kₜ ≥ k₀ ≥ 1.

The half-infinite nature of the sequence (no left end) does NOT affect the losing direction:
for large k₀ = 2j, no finite-time strategy can reach position 0, so the safety condition is
vacuous for the indistinguishability argument.

---

## Tightened Phase 2 — Lemma A (replaces hand-wave above)

The Phase 2 argument above invokes "upward gaps" (consecutive c-differences ≥ 2), which
properly applies only to Δ = 1. For general Δ = p₂ − p₁, here is a clean argument that ALL
pairs are distinguishable when c is not eventually identity.

**Lemma A.** A pair (a, b) with a < b is indistinguishable (in the sense that for every
D ≥ 0, the discrimination interval contains no integer of parity D) **if and only if**
b = a+1 and c restricted to {a, a+1, …} is the identity-up-to-shift (forcing c eventually
identity).

*Proof of Lemma A.* Set Δ = b − a > 0. Indistinguishability means:
1. |c(a+D) − c(b+D)| = 1 for every D ≥ 0
2. min(c(a+D), c(b+D)) ≡ D (mod 2)

Define σ(D) = sign(c(b+D) − c(a+D)) ∈ {−1, +1}. From (1):
c(b+D) = c(a+D) + σ(D). Replacing D ↦ D+Δ via b+D = a + (D+Δ):
**c(a + D + Δ) = c(a+D) + σ(D)**, i.e., c(n+Δ) − c(n) = σ(n−a) for all n ≥ a.

**σ is Δ-periodic.** Iterating: c(n+2Δ) − c(n) = σ(n−a) + σ(n−a+Δ). If σ(n−a) +
σ(n−a+Δ) = 0 then c(n+2Δ) = c(n), violating injectivity. So σ(n−a) = σ(n−a+Δ).

**σ ≡ +1.** Iterating, c(n + kΔ) = c(n) + k · σ(n−a). If σ < 0 anywhere, c → −∞, but
c maps to positive integers. Contradiction. So σ ≡ +1, i.e., c(n+Δ) = c(n) + 1 for all
n ≥ a.

**Δ ≥ 2 is impossible.** With c(n+Δ) = c(n)+1, the image c({n ≥ a}) is the union of Δ
arithmetic rays of step 1 starting at c(a), c(a+1), …, c(a+Δ−1). The largest of these
starting values, say v_max, lies in every ray of the form [v_i, ∞) for v_i ≤ v_max — that is,
in all Δ rays. So v_max is hit Δ times. With Δ ≥ 2 this violates injectivity.

**Δ = 1 forces eventually identity.** c(n+1) = c(n) + 1 for n ≥ a gives c(n) = n + C for
n ≥ a (some constant C = c(a) − a). For c to remain a bijection of ℕ⁺, no value can be
double-counted. If C > 0, the values 1, 2, …, C are missing from c({n ≥ a}) and must be
in c({1,…,a−1}), giving a−1 ≥ C; the surjective constraint then traps c into c(n) = n for
n ≥ a (C = 0). So **c is eventually identity** from position a onwards. ∎

**Consequence.** If c is NOT eventually identity, no pair (a, b) is indistinguishable, so
Phase 2 succeeds against any (p₁, p₂) emerging from Phase 1.

---

## Lean 4 Formalization

The proof is formalized in `griddles-p4-lean/` (mirror of `puzzle-1/griddles-p1-lean/`
layout).  Build with `lake build`.

### Status

**Fully proven:**

| File | Content |
|------|---------|
| `Defs.lean` | Game semantics: `Perm`, `Strategy`, `Action`, `state`/`position`/`history`/`displacement`, `WinsFrom`, `BobWins`, `EventuallyIdentity`. |
| `Parity.lean` | Parity invariant `(t − D_t) % 2 = 0` while Bob has not guessed.  Also `position_lower_bound`. |
| `Losing.lean` | Entire losing direction: `parallel_evolution`, `cBound`, static `signal_match`, `parallel_for_eventually_identity`, and the headline theorem `EventuallyIdentity_loses : EventuallyIdentity c → ¬ BobWins c`. |
| `Answer.lean` | The main `iff`: `BobWins c ↔ ¬ EventuallyIdentity c` (winning direction still via the `Δ≥2` sorry in LemmaA). |
| `WinningRestricted.lean` | **Complete, axiom-clean winning theorem** for a natural class. Builds the full adaptive strategy (oscillation Phase 1 + first-even/odd-Yes detectors + decode + guess + safety + timing) and proves `LocallyDecodable_BobWins : LocallyDecodable c → BobWins c`. Concrete worked examples `adjPerm_BobWins` (adjacent transpositions) and `cyc3Perm_BobWins` (3-cycles). `#print axioms` shows only `propext, Classical.choice, Quot.sound` — no `sorryAx`. The trolley never leaves `{k₀, k₀+1}`, so safety is automatic. Covers the "locally 2-distinguishable" class. Wild permutations with large jumps fall outside it and need more probes / navigation. |
| `WinningKProbe.lean` | **Axiom-clean K=3 generalization.** `LocallyK3Decodable_BobWins : LocallyK3Decodable c → BobWins c`, using a period-4 triangle-wave sweep (displacements 0,1,2,1,…) and three detectors (first-Yes at displacements 0, 1, 2). Strictly wider class than K=2 (can use a third probed label). Worked example `blkPerm_BobWins` (block 3-cycle). Safety still automatic (displacement ∈ [0,2]). |
| `Answer.lean` (capstone) | `locallyDecodable_main : LocallyDecodable c → BobWins c ∧ ¬ EventuallyIdentity c`, tying the losing direction to the restricted winning theorem (and confirming locally-decodable ⇒ not eventually identity). Axiom-clean. |

**Remaining gaps (research-level, confirmed by parallel sub-agent investigation):**
- `LemmaA.sigma_eq_pos_one` (Δ≥2): `σ≡+1` is genuinely false at "bad" displacements, so the
  shift-relation route is structurally dead. The Δ-**even** sub-case is tractable (~100 lines:
  parity forces a step reversal → injectivity via `sigma_no_flip`); the Δ-**odd** sub-case is
  genuine global value-hogging needing full ℕ⁺ surjectivity bookkeeping across bad regions.
- `Winning.NotEventuallyIdentity_wins` (general navigation): a uniform navigation strategy
  cannot meet the Phase-1 timing `t ≥ T₁+D` (would require `c(n)−n` unbounded above, false for
  e.g. `adjPerm`). The real proof must **adaptively** switch between local-decode (bounded
  growth) and navigation (unbounded growth) — substantial new mathematics.

### Deep-dive on the Δ≥2 contradiction (precise characterization of the crux)

Call displacement `D` *good* iff `c(a+D) ≥ D` (symmetric in a/b by `good_symm`). The parity
kill needs a **good pair** `(D, D+Δ)` (both `D` and `D+Δ` good). Two regimes:

1. **A good pair exists.** Then `c(a+D+Δ)` is consecutive to both `c(a+D)` and `c(a+D+2Δ)`,
   and injectivity gives `{c(a+D), c(a+D+2Δ)} = {c(a+D+Δ) ± 1}`.
   - **Δ even**: the two minima are both `≡ D`, pinning `c(a+D+Δ)` to both parities →
     contradiction. *Formalized* as `indist_Delta_even_good`.
   - **Δ odd**: the two minima are `≡ D` and `≡ D+1`; both arrangements are *consistent*
     (`Y ≡ D+1` either way). **Parity cannot kill odd Δ** — this is the essential reason
     the odd case is genuinely harder.

2. **No good pair.** Then every good `p` has `p+Δ` bad, and `indist_consec` + consecutiveness
   yield the sharp bound **`c(p) ≤ (p − a) + Δ` for all `p ≥ a`** (i.e. `c(p) − p ≤ Δ − a`).

**Why regime 2 resists a clean kill.** The bound `c(p) − p ≤ Δ − a` is *necessary but
sum-consistent* with bijectivity: `Σ_{p∈[a,a+N]} c(p) ≥ (N+1)(N+2)/2` together with the bound
gives only `1 ≤ Δ` (true). It also does **not** forbid "bad" cells (large `p`, small `c(p)`),
which let `c⁻¹([1,M])` contain arbitrarily large positions — defeating every pigeonhole. So the
genuine odd-Δ contradiction must combine the *full* "consecutive at every good `D`" structure
with global ℕ⁺ surjectivity bookkeeping across unboundedly many bad regions; no finite-window,
parity, or simple-counting form survives. This is the precise research-level gap.

### UPDATE — regime 2 *is* killable; Δ-even fully closed (formalized)

The sub-diagonal bound is the wrong lever, but a sharper one works. In the *no good pair*
regime, `good D → (D+Δ) bad` (no-good-pair) **and** `bad D → (D+Δ) bad` (`bad_D_propagates`),
so **every** displacement `≥ Δ` is bad: `c(p) < p−a` for all `p ≥ a+Δ`. Then for `N` large,
`c` maps the whole segment `[1,N]` into `[1, N−a−1]` (small positions bounded by their finite
`Finset.range` sup; large positions by `p−a−1`) — injecting `N` into `N−a−1`, a clean
pigeonhole. Formalized as **`regime2_impossible`** (no new sorry/axiom).

Consequently the `Δ ≥ 2` story is now:
- **Δ even** — *fully closed* (`indist_Delta_even`): good pair ⇒ parity kill
  (`indist_Delta_even_good_at`); no good pair ⇒ `regime2_impossible`.
- **Δ odd** — no-good-pair ⇒ `regime2_impossible`; the sole remaining `sorry`
  (`odd_good_pair_gap`) is **Δ odd with a good pair present**.

Refined picture of that last gap, by the good set `G = {D : c(a+D) ≥ D}`:
- `G` cofinite ⇒ consecutive on a tail ⇒ `flat_imp_ascending` ⇒ ray overlap (closeable);
- `G` with `≤ a` good displacements `≥ a+Δ` ⇒ the `regime2_impossible` over-stuffing still bites;
- `G` infinite-but-not-cofinite (**interleaved** good/bad runs) ⇒ the true barrier: ascending
  runs are finite (length `~c(a)/(Δ−1)`, never reaching a ray) and `≥ a+1` good positions absorb
  the pigeonhole slack. This interleaved Δ-odd case is the sole research-level remainder.

**LemmaA.lean** has three sub-lemmas proven:

* `c_shift_iter` — if `c(n+1) = c n + 1` past `N`, then `c(N + k) = c N + k`.
* `c_shift_implies_cN_eq_N` — bijectivity of `c` forces `(c N).val = N.val` under the
  shift property (proved via the bijection `m < c N ↔ c.symm m < N` and Finset
  cardinality on `Iio`).
* `shift_one_implies_eventually_identity` — combining the above, `c` is the identity
  on `[N, ∞)`.

**Two sorries remain:**

1. `LemmaA.Indistinguishable_implies_eventually_identity`.  Combines the case analysis
   on `Δ = b − a`:
   - Derive σ-equation `c(a + D + Δ) = c(a + D) + σ(D)` from `Indistinguishable`.
   - σ is Δ-periodic (iterating gives `c(n + 2Δ) − c(n) = σ + σ(•+Δ)`; injectivity
     rules out `σ(•) + σ(• + Δ) = 0`).
   - σ ≡ +1 (else c-values tend to `−∞`).
   - Δ = 1 (else `Δ` arithmetic rays of step 1 overlap at `v_max`).
   - Apply `shift_one_implies_eventually_identity`.

2. `Winning.NotEventuallyIdentity_wins`.  Construct an explicit strategy:
   - Phase 1: alternating right-left moves; track time of first "Yes" at even t.
   - Phase 2: use `LemmaA.not_eventually_identity_implies_distinguishable` to extract
     a discriminator `(D, t)` for the candidate pair, navigate there, observe, guess.

Both sorries are isolated and well-documented; the math is laid out fully in this
file and in the Lean file comments.

---

## Computational Verification of LemmaA (D ≥ 0 definition)

A search (`/tmp/indist_*.py`, see git history) settled two questions that the prose proof
glossed over:

1. **The signal-based `Indistinguishable` definition with `D ≥ 0` is correct.**  Moving
   left (`D < 0`) gives Bob no extra power: reaching cell `p` costs time `t ≥ |D|`, by
   which point the signal `c(p) < t` is saturated.  The losing direction already handles
   `D < 0` via `position_lower_bound`.

2. **LemmaA holds for all Δ (no infinite counterexample).**  Enumerating every permutation
   of `{1,…,7}` (all eventually-identity): the *only* indistinguishable pairs have `Δ = 1`
   — the identity tail discriminates every `Δ ≥ 2` pair.  Backtracking construction of an
   infinite `Δ ≥ 2` indistinguishable bijection:
   - **`Δ = 2`** (even): dies at depth 5 — killed by the parity argument (`D=0` and `D=Δ`
     over-constrain `c(b)`'s parity; the bad sub-case forces `c(a) ≤ 0`).
   - **`Δ = 3`** (odd): a depth-30 prefix exists but is a *dead end* — its residue-0 chain
     `c(3),c(6),… = 22,23,…` ascends with large values, hogging the ray `[22,∞)` and
     leaving only finitely many values for the other two residue classes (value-hogging /
     ray-overlap contradiction).  Extending past depth ~32 explodes the search (no
     solution), confirming impossibility.

So the rigorous `Δ ≥ 2` contradiction is **ray overlap** (an ascending `Δ`-ray covers a
cofinite set), exactly `shift_Delta_ge_2_contradiction`.  The Lean gap is establishing the
ascending shift on a cofinite tail despite finitely-interrupting "bad" displacements.

## Notes on Corner Cases

- **c = identity exactly:** Covered by the "eventually identity" case (N = 0). Bob loses.
- **c = finitary non-identity (e.g., a 3-cycle on {1,2,3}, identity elsewhere):** This IS
  eventually identity (c(n) = n for n ≥ 4). Bob loses for large k₀.
- **c with finite support transpositions only:** Still eventually identity. Bob loses.
- **Any c that rearranges arbitrarily large values:** Bob wins.

## REASSESSMENT (2026-05) — answer re-confirmed empirically; proof approach corrected

Triggered by skepticism that the answer itself might be wrong. Source check: this is
G-Research GRiddles Series A Puzzle 4; the competition is **OPEN with no published answer**,
so the answer below is our own derivation, now stress-tested three independent ways.

**Answer (re-confirmed): Bob wins ⟺ c is NOT eventually the identity** (c(n) ≠ n for
infinitely many n). Evidence: (1) an empirical pattern-zoo over 14 families — the
game-theoretic distinguishability predicate matches non-EI exactly, with eventually-identity
families always exhibiting a persistent indistinguishable tail pair and non-EI families none;
(2) a true belief-state AND/OR game solver (with real safety) — eventually-identity → LOSE,
non-EI → WIN from full ignorance, stable as the universe grows; (3) the identity stress-test
below.

**The clean core mechanic (the "Yes ⟺ k₀ < 2L" identity).** Let `L_t` = number of LEFT moves
Bob has made by time `t`. Then `t − D_t = 2 L_t`, so the signal is
`Yes ⟺ c(k₀ + D_t) < t ⟺ c(k₀+D_t) − (k₀+D_t) < 2L_t − k₀`, i.e. **the walk reads
`g(m) := c(m) − m` against a threshold controlled by Bob's left-move count.** For the
identity `g ≡ 0`, so `Yes ⟺ k₀ < 2L_t`: Bob can only ever compare `k₀` against **even**
thresholds, and `2j < 2L ⟺ 2j+1 < 2L` always — so `(2j, 2j+1)` produce *identical signals
under every strategy* and can never be separated. (Verified: a "move left until Yes" strategy
gives `k₀=10` and `k₀=11` the byte-identical history `N N N N N Y …`.) This is the whole
obstruction: flat labels ⇒ only even thresholds ⇒ the parity bit of `k₀` is unrecoverable.

**Losing direction (rigorous, general).** For c eventually identity (c(n)=n for n>N), take
`2j > 2N`. The pair `(2j, 2j+1)` is indistinguishable: while both worlds stay in the identity
region the `k₀ < 2L` argument gives identical signals; if Bob drives them left into `[1,N]`,
that costs time `t ≥ 2j−N > N ≥ c(position)` so the signal is saturated "Yes" in both worlds.
Either way signals agree forever ⇒ Bob cannot guarantee the guess ⇒ LOSE. (This matches the
existing `Losing.lean`.)

**Winning direction — corrected architecture.** Safety is FREE: a strategy that only ever
oscillates and moves RIGHT keeps positions ≥ k₀ ≥ 1, so it never falls off. Strategy:
- *Phase 1 (bracket):* oscillate displacement 0↔1; the first even/odd "Yes" brackets
  `c(k₀), c(k₀+1)` to two values each ⇒ narrows `k₀` to two candidate cells.
- *Phase 2 (resolve), adaptive:* either **local-decode** (resolve from c's behavior in a
  bounded window — works when the local labels are non-identity, e.g. transpositions, block
  cycles), or **navigate right** to a *landmark* — an adjacent pair `(m,m+1)` with a gap
  `|c(m+1)−c(m)| ≥ 2` whose window contains both parities — and read off the answer.

**CRUCIAL methodological correction.** The abstract `Indistinguishable`/`LemmaA` route
(no-discriminator-at-any `t ≥ D`) is the WRONG vehicle for the winning direction: a real
strategy needs a discriminator at `t ≥ T₁ + D` (after Phase 1 ends at `T₁ ≈ c(k₀)`), not
merely `t ≥ D`. So even a fully-completed `LemmaA` (closing `odd_good_pair_gap`) would NOT
prove the main winning direction. Empirically confirmed: the naive "oscillate-then-navigate"
strategy genuinely fails (does not fix with budget) on block-cycle / reverse-block / sparse
families — those need local-decode instead. **No single uniform strategy works; the win is
local-decode-OR-navigate, chosen adaptively.**

**The single crux lemma to prove (timing-aware "landmark" lemma).** non-EI ⟹ for every
candidate pair there is a *reachably-timed* discriminator (`t ≥ T₁+D`) — concretely, a
rightward landmark gap `(m,m+1)` with `max(c(m),c(m+1)) ≥ m − a`. Follows morally from
surjectivity (a permutation cannot stay below the diagonal on a whole tail), being nailed
down precisely (possibly cleaner in the inverse coordinate `c⁻¹(t) − t`).

**Formalization plan going forward:** keep `Losing.lean` (done) and the concrete
`WinningRestricted`/`WinningKProbe` local-decoders (done, axiom-clean); the `regime2_impossible`
/ `odd_good_pair_gap` LemmaA work is a valid characterization of the *abstract* Indist relation
but is OFF the critical path — the winning direction should instead be built from the
timing-aware landmark lemma + the right-only adaptive strategy.

## Restricted Separation Lemma — precise gap characterization (dedicated proof attempt)

A focused proof attempt (math, no game) confirmed the **monotone-right reformulation is no
easier** than the old `odd_good_pair_gap`: it is a *stronger conclusion from a weaker
hypothesis*. Clean coordinates and what is airtight vs open:

Let `a = min(p₁,p₂)`, `Δ = |p₂−p₁| ≥ 1`, `C = (2m+2) − a`. Set `u(D) := a+D+C − c(a+D)`
(so `u(0)=2`) and `w(D) := u(D) − D = a+C − c(a+D)` (**injective** in `D`, since `c` is).

**Reduction (airtight, 0 mismatches incl. non-EI):** twin ⟺
`(U)  ∀D≥0: [u(D) ≥ 1] ⟺ [u(D+Δ) ≥ Δ+1]`  (equivalently `[w(D) ≥ 1−D] ⟺ [w(D+Δ) ≥ 1−D]`).

**Airtight structural facts (all elementary, Lean-formalizable):**
- `B(n) ⟹ B(n+Δ)` is **NOT** a free permutation fact (fails ~95% generically); it holds
  *only as a consequence of twin* — via `B(n) ⟹ c(n+Δ)<n+C ⟹ c(n+Δ)<(n+Δ)+C = B(n+Δ)`.
- (M1) GOOD `={u≥1}` propagates forward by `+Δ`; (M2) "stuck" `={u≤0}` propagates *backward*
  by `+Δ`. ⇒ on each residue mod `Δ`, the sign of `u` is bad-prefix / good-suffix.
- Eventual **upper** bound: once GOOD, `g(m)=c(m)−m ≤ C−Δ−1`.

**The open core (genuine, research-level):** EI needs `g≡0` on a tail, but twin gives only an
upper bound. Two subcases: (A) all residues eventually GOOD ⇒ `g ≤ C−Δ−1` — a pure upper
bound, and *upper-bound + bijection ≠ EI* (adjacent transpositions have `g∈{±1}`, non-EI);
(B) some residue "stuck" (`c(n) ≥ n+C` on an AP) = value-hogging of large values, which
surjectivity does NOT kill in isolation. A bounded-lag stuck-residue twin prefix survives to
depth 69 ⇒ **no finite/local/parity obstruction**; the contradiction must come from the
*interaction* of `(U)` on the other residues with global ℕ⁺ surjectivity across infinitely
many interleaved bad positions. (Empirically certain: 0 twins in non-EI, N ≤ 20000.)

**Status:** `restricted_separation` stays a single, precisely-characterized, true-but-hard
`sorry`. The monotone-right *strategy* around it (safety + timing + Phase-1/2 plumbing) is
fully formalizable and is being built (`WinningGeneral.lean`).

## CRITICAL CORRECTION (2026-05) — monotone-right route RETRACTED (was unsound)

`restricted_separation` and the `WinningGeneral` "monotone-right" strategy were **FALSE / incomplete**
and have been **deleted**. Counterexample: **`blkPerm`** (block 3-cycle `c(3k+1)=3k+2, c(3k+2)=3k+3,
c(3k+3)=3k+1`), which is non-EI and a genuine Bob-win. Its candidate pair `(1,2)` (`T₁=4`) is a
"twin" under rightward probes: since `c(n) ≤ n+1`, both `[c(1+D) < 4+D]` and `[c(2+D) < 4+D]` are
*always true*, so no rightward displacement `D` separates them. Hence `restricted_separation`
(∃ separating `D`) is false, and the monotone-right strategy does NOT win `blkPerm`.

**Root-cause of the earlier mis-step.** I had claimed the abstract `LemmaA` route was "the wrong
vehicle because of timing (`t ≥ T₁+D`)". That was backwards. Bob catches **early-wake
discriminators** by *oscillating from `t=0`* (he need not finish a Phase 1 first): for `blkPerm`,
cell 3 wakes at `t=3`, distinguishing `k₀=1` from `k₀=2` — this is exactly what the K=2/K=3 local
decoders use. The monotone-right restriction `t = T₁+D` *discarded* these early discriminators,
making the strategy strictly weaker and, in fact, incomplete.

**Corrected understanding.** The right winning-direction lemma is the **abstract `LemmaA`**
(`Indistinguishable c a b → b=a+1 ∧ EventuallyIdentity`), which quantifies over ALL reachable
`(D,t)` with `t ≥ |D|` (early wakes included). Its contrapositive gives: non-EI ⇒ every candidate
pair has *some* reachable discriminator; Bob reaches it by going to displacement `D` and padding
with oscillation to the required time `t` (`t ≥ |D|`, parity `t ≡ D`). Any reachable discriminator
is therefore usable — there is **no** `t ≥ T₁+D` obstruction. So:
- the genuine open crux is `LemmaA`'s `Δ≥2` case (`odd_good_pair_gap`) — true, research-level; and
- the winning strategy is "oscillate-to-narrow + reach-the-discriminator" (the WinningRestricted /
  WinningKProbe local decoders are the correct, axiom-clean special cases; the general uniform
  strategy plumbing is the remaining engineering).

Still PROVEN & axiom-clean: losing direction; WinningRestricted (K=2); WinningKProbe (K=3) with
worked examples (adjPerm, cyc3Perm, blkPerm — note blkPerm IS won, via the K-decoder, NOT
monotone-right). The answer (Bob wins ⟺ not eventually identity) is unchanged and still confirmed.

## BREAKTHROUGH (2026-05) — the Δ≥2 distinguishability lemma is PROVEN (was "research-level")

Stepping back per "do the research", the supposedly research-level crux fell to an ELEMENTARY
argument. The wrong mental model was "good/bad displacements interleave"; in fact:

1. `bad_D_propagates` (already proven): `c(a+D)<D ⟹ c(a+D+Δ)<D`. So "bad" is **forward-closed**
   on each residue mod Δ ⇒ active (good) displacements form a **prefix**, never interleaved.
2. On the active prefix, `indist_consec` gives `|c(a+D)−c(a+D+Δ)|=1`, so by triangle inequality
   `c(a+r+kΔ) ≤ c(a+r)+k`  (`chain_bound`).
3. Active means `c(a+r+kΔ) ≥ r+kΔ`. Combine: `k(Δ−1) ≤ c(a+r)`. **For Δ≥2 the prefix is finite.**
4. Δ residues × finite prefixes ⇒ cofinitely many displacements bad ⇒ `c` maps `[1,N]` into
   `[1,N−a−1]` for large `N` ⇒ injectivity contradiction (`cofinitely_bad_impossible`).

This subsumes BOTH parities (no even/odd split, no parity argument, no good-pair gap, no
value-hogging bookkeeping). Lean: `indist_Delta_ge_2_impossible`. Result:
`Indistinguishable_implies_eventually_identity` and `not_eventually_identity_implies_distinguishable`
are now **axiom-clean** (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). LemmaA.lean is
fully `sorry`-free.

**Status now:** losing direction ✓; abstract LemmaA (the combinatorial heart) ✓ axiom-clean;
WinningRestricted K=2 / WinningKProbe K=3 ✓. The ONLY remaining gap for `Answer.main`'s winning
direction is the *uniform winning strategy* turning "no indistinguishable pair" into `BobWins`
(oscillate-to-narrow + reach-the-discriminator; intricate but NOT research-level — discriminators
at any reachable `t≥|D|`, including early wakes caught during oscillation, are usable).

## VALIDATED winning strategy design (for Answer.main ← direction)

Simulation across all non-EI families + a deep-identity-with-far-gap stress test (100/100
deep pairs where K=2 fails are resolved by navigation; ZERO total failures):

**Strategy = K=2-decode ELSE navigate.**
- Phase 1: oscillate D∈{0,1}; firstEvenYes ⇒ T₁=2m+2 and candidates {p₁,p₂}=c⁻¹(2m),c⁻¹(2m+1);
  firstOddYes gives the second detector.
- If (firstEvenYes@k₀, firstOddYes@k₀+1) uniquely decodes k₀ (K=2 / LocallyDecodable):
  guess. This catches LOCAL / early-wake discriminators (D∈{0,1}, t<T₁) — e.g. blkPerm's
  (D=1,t=3) — which the monotone-right strategy missed.
- Else navigate right; the first discriminator at t ≥ T₁+D resolves the pair. This catches
  FAR-GAP discriminators (deep identity regions ⇒ navigate to the next gap; e.g. (50,51)
  resolved at (D=102,t=154)). This is exactly the (correct-for-this-case) monotone-right probe.

Why the union is complete (validated, to be formalized): every candidate pair of a non-EI c
is distinguished by K=2 OR by a t≥T₁+D navigation probe. The retracted `restricted_separation`
was FALSE only because it demanded the *navigation* discriminator universally; the K=2 half
covers exactly the pairs (like blkPerm) where navigation can't.

**Remaining Lean work:** formalize this combined strategy + the correctness lemma
"non-EI candidate pair ⇒ (K=2 ∨ navigation) distinguishes". WinningRestricted already proves
the K=2 half (LocallyDecodable → BobWins); the navigation half is the (correctly-scoped,
non-universal) monotone-right machinery. NOT research-level — pure game-trajectory engineering.

## CORRECTED winning strategy: the STAIRCASE SWEEP (correctness = the proven lemma)

Two earlier designs were INCOMPLETE (caught by simulation before formalizing — important):
- monotone-right (nav only): misses local discriminators (blkPerm, D=1).
- K2 ∨ nav: misses mid-range local discriminators (block-5-cycle has 56 pairs distinguishable
  only at D=2,3,4 with small t — neither D=1 nor t≥T₁+D).

**Correct strategy — staircase sweep.** Tight-oscillate at displacement D=0,1,2,… (positions
k₀+D, k₀+D+1 — forward only, so safety is automatic), catching the PRECISE wake
firstYes@(k₀+D) at each D (resolution 2). D=0 gives firstEvenYes ⇒ T₁ and narrows k₀ to the two
candidates {c⁻¹(2m), c⁻¹(2m+1)}. Continue to D* = least D where firstYes@(k₀+D) differs between
the two candidate worlds, i.e. a "D-discriminator": ∃ t≥D, t≡D mod2, [c(p₁+D)<t] ≠ [c(p₂+D)<t].
Guess the matching candidate's cell.

**Why complete & terminating — and why no new lemma is needed:** a D-discriminator at the
precise wake is caught directly by the tight oscillation at displacement D (it gives both
parities' brackets at each cell, resolution 2). The existence of a finite D-discriminator for
every non-EI candidate pair is EXACTLY `not_eventually_identity_implies_distinguishable`
(¬Indistinguishable, D≥0) — already PROVEN, axiom-clean. Verified: every non-EI candidate pair
has a finite D* (1–4 for block cycles / reverse blocks / id-even-swap-odd; larger but finite for
deep-identity-with-far-gap, where the sweep simply reaches the gap displacement).

This is the right target to formalize for Answer.main's ← direction: define the growing-D
staircase-sweep strategy, prove it catches firstYes@(k₀+D) at each D, narrow via D=0, and
discharge WinsFrom using the proven D-discriminator existence. Engineering (sizeable, like
WinningKProbe generalized to growing window) but NOT research-level, and CORRECTNESS-CLEAN.

## STRATEGY IS GENUINELY HARD — three incomplete designs, the real obstruction

Correction to the previous note: the sequential staircase is ALSO incomplete. Simulated exact
dynamics: on blkPerm, doing D=0 first (oscillate until firstYes@k₀ at t=4) means Bob reaches
D=1 only at t≥4, AFTER cell 3's wake at t=3 — so both worlds give the identical observed vector
{0:4,1:5,2:6,3:7}. NOT distinguished. (K=2 succeeds precisely because it monitors D=0 AND D=1
*simultaneously* from t=0, catching the early t=3 wake.)

**Three incomplete designs, all caught by simulation before formalizing:**
1. monotone-right (nav only): misses local D=1 (blkPerm).
2. K=2 ∨ nav: misses mid-range local D=2,3,4 (block-5-cycle).
3. sequential staircase: misses EARLY wakes at D≥1 (does D=0 first, arrives at D≥1 too late).

**The real obstruction (timing/resolution/reach tension):** Bob is at ONE displacement per
tick, so he can finely monitor (period ~2) only O(1) displacements at once. Monitoring D=0..K
simultaneously (triangle wave) costs resolution ~2K, which can blur a discriminator's O(1)
window for large K. Catching an EARLY wake at displacement D requires fine monitoring of D from
t=0 (can't be reached later). Catching a FAR wake requires reaching large D (can't fine-monitor
all small D meanwhile). So: small-D discriminators with early wakes need fine simultaneous
monitoring (small-K triangle wave); far discriminators need navigation. The "complete" strategy
must combine these AND its completeness lemma must rule out the pairs that fall in the gap
(distinguishable only by a mid/large-D early-wake discriminator that neither fine-K nor nav
catches). This is the genuine remaining difficulty — research-adjacent engineering, not routine.

**Honest status:** answer SOLVED & confirmed; losing direction + the research-level
distinguishability crux (LemmaA) + K=2/K=3 winning classes all PROVEN & axiom-clean. The general
uniform winning strategy (one sorry in Answer.main) is a genuinely hard open formalization with a
real timing/resolution/reach tension; the existence of *some* winning strategy is confirmed by
the belief-state game solver, but an explicit, provably-complete uniform strategy remains open.

## STRATEGY DIFFICULTY — corrected analysis (simulation bug found & fixed)

Found a bug in earlier triangle-wave sims: displacement must satisfy D_t ≡ t (mod 2) (parity
lock; D changes by ±1 each step). My tri_displacement used (t-1)%2K, putting D=0 at odd t —
physically impossible. Conclusions from those sims were invalid. Redone with the correct
reflecting walk D_t = reflect(t mod 2K).

**Corrected findings (these are solid):**
- Every non-EI candidate pair IS distinguished by some fixed amplitude-K triangle run from t=0
  (confirms winnability, consistent with the proven LemmaA), but the required K varies per pair
  (≈ local structure size; far gaps need large K).
- A LARGE fixed K does NOT distinguish SMALL structure (block-3 fails at K=5,10,30: resolution
  ~2K too coarse for an O(1) discriminator window). So K must roughly MATCH each pair's
  discriminator displacement D*.
- K=2 (amplitude 1) handles block-3 but misses block-5 (needs K up to 5); etc.

**The genuine obstruction:** to catch a pair's discriminator, Bob must finely (period ~2K,
K≈D*) monitor displacement D* from BEFORE its wake. K* = the right amplitude varies per pair;
Bob can't know it in advance, can't restart from t=0, and time-sharing across amplitudes
coarsens resolution (so dovetailing is subtle). Targeted "narrow-to-2 then navigate to D*"
misses because the wake lands ~2 steps before arrival (t* < T₁+D*).

**Designs tried and rejected by exact-dynamics simulation (6):** monotone-right; K2∨nav;
sequential staircase; slow growing-triangle; large-fixed-K; targeted-navigate. Each fails a
concrete family. The likely-correct design (dovetail of fixed-amplitude triangles) is intricate
and its completeness under epoch-timing-vs-wake-timing is unverified.

**Honest conclusion:** the explicit uniform winning strategy is a genuinely hard,
research-adjacent formalization — almost certainly the intended hard core of the puzzle. The
DISTINGUISHABILITY crux (LemmaA) — the part everyone called impossible — is PROVEN & axiom-clean,
along with the losing direction and K=2/K=3 winning classes. The remaining Answer.main sorry
(turning distinguishability into an explicit uniform BobWins strategy) is the hard open piece;
the EXISTENCE of a winning strategy is confirmed by the belief-state game solver.

---

## Definitive characterization of the winning-strategy obstacle (this session)

> **SUPERSEDED IN PART — read the "Q-ANSWER" section below.** Result #1 here is about a SINGLE
> trajectory **universal over all `c`** (which indeed cannot exist). The different question — a
> trajectory **tailored to each `c`** (Bob knows `c`) — is answered **YES** in the Q-ANSWER
> section: a c-tailored signal-independent monotone-lag staircase separates all start cells with
> finite per-`k₀` `T(k₀)`. So the win is NOT "irreducibly adaptive" for the *fixed-per-c* question;
> adaptivity was only ever needed for a *universal* (c-independent) strategy.

Three NEGATIVE results, each by exact-dynamics simulation, jointly prove the *universal* (one
trajectory for all `c`) winning strategy is **irreducibly adaptive with foresight** — no shortcut
survives:

1. **No fixed trajectory is universal.** Tested fixed displacement schedules `D_t`: fixed-K
   triangle, growing triangle, slow "dwelling sweep" (oscillate {D,D+1} then advance), and
   sawtooth "right a / left b". The sawtooth `a=2,b=1` (a slow rightward staircase revisiting
   each displacement ~3× near `t≈3D`) distinguishes all `k₀≤40` for block-5, rev-block-5,
   block-3, swap-2 — but **collides on 71 / 1247 random period-B non-EI permutations**. So a
   single "sweep + decode" strategy provably cannot win all non-EI c.

2. **Two-phase fails on timing/slack.** "Localise `c(k₀)` to two candidates via the `D=0`
   oscillation, then navigate to a discriminator": the `D=0` oscillation fixes `c(k₀)∈{τ-2,τ-1}`
   only at first-Yes time `τ` (even), leaving a consecutive-`c`-value pair. block-5 `(1,2)`'s
   discriminators all sit at **slack `t-D ≤ 2`** (e.g. D=3,t=3; D=4,t=4) and have EXPIRED by
   `τ=4`. Bob can't navigate back in time.

3. **"Finite belief ⇒ winnable" is FALSE** as a standalone induction. A 2-element belief at a
   late state whose only discriminators are in the past is genuinely lost. Winnability is a
   property of *reachable, non-stranding* states, not of belief size.

**Root cause.** Catching low-slack discriminators requires Bob riding the diagonal `D≈t`;
bounding `k₀` requires Bob near the origin (small `D`, large slack). These conflict at every
instant. Only belief-guided interleaving (genuine foresight: "never enter a stranding state")
reconciles them. The adaptive belief-state minimax solver wins EVERY family tested, **including
the 71 sawtooth counterexamples** (verified: B6 [0,3,1,5,2,4], B5 [0,2,4,3,1], B6 [0,5,4,3,1,2]
all won for k₀∈{1..15}). So the answer is correct; the strategy is just genuinely adaptive.

**On the inductive `Winnable` predicate.** A finite-depth inductive predicate cannot prove the
initial (infinite) belief winnable: infinitely many `k₀` need infinitely many distinct leaves ⇒
infinite depth. The correct statement is per-`k₀`: `∀k₀ ∃T (depending on k₀)`, with `T`
unbounded across `k₀`. `depth(univ,0,0)=∞`, so finite-depth-minimax does not apply to the
initial belief — the proof must bound `k₀` first, then win the finite residual, while proving the
residual state is non-stranding. That last invariant is the genuine open piece.

---

## Q-ANSWER (decisive): a c-TAILORED signal-independent trajectory EXISTS — answer YES

**The question.** For non-EI `c`, does there exist a *c-tailored* signal-independent trajectory
`D : ℕ → ℕ` (`D₀=0`, `|D_{t+1}−D_t|=1`, `D_t≥0`) such that for every start `k₀` there is a finite
`T(k₀)` with: for every `k≠k₀` some `s≤T(k₀)` has `[c(k+D_s)<s] ≠ [c(k₀+D_s)<s]`?  (I.e. the
signal histories `h_{k₀}(t)=[c(k₀+D_t)<t]` are pairwise distinct with per-`k₀` finite separation.)

**ANSWER: YES** for every non-EI `c`. This is *not* a contradiction of negative result #1 above:
that result killed a **single trajectory universal over all `c`**. Here the trajectory **depends
on `c`** (Bob knows `c`). The two questions are different; the c-tailored one is YES.

### The one structural fact that drives everything: lag is monotone

For ANY trajectory, the **lag** `L_t := t − D_t` satisfies `dL = 1 − dD ∈ {0, +2}` (since
`dD ∈ {±1}`). So **`L_t` is monotone nondecreasing**, growing by 0 or 2 each tick; it can never
return to a smaller value. (This is the constraint earlier notes implicitly fought against. It
makes "navigate back to a low-slack discriminator" impossible — but it does NOT block (Q), see
below.) Equivalently, slack `t−D` only grows.

### Why monotone lag is NOT an obstruction: catchable-ahead

Each pair `(a,b)` has **infinitely many** separators `(D,t)` (verified: separator count grows
without bound for every family incl. the sparse-gap ones — `/tmp/p4q_final.py`, part A). A pair's
separators recur at higher and higher lag. So no pair is ever "use-it-or-lose-it": for any current
lag, a fresh separator for any still-unsplit pair exists at a higher lag, *reachable later* exactly
because lag is allowed to keep growing. This is precisely the proven `catchable-ahead` /
`not_eventually_identity_implies_distinguishable` (LemmaA, axiom-clean) read in the lag coordinate.

### The c-tailored construction: the MONOTONE-LAG STAIRCASE

Trajectory `D(t) = t − L(t)`, `L` monotone nondecreasing, parity-correct, tuned to `c`'s
**alarm structure** (the times at which novel separators for fresh pairs first appear). Operationally:
ride RIGHT (lag held) to sweep displacements at the current lag, periodically take one LEFT move to
bump lag by 2; dwell at each lag long enough to sweep the displacement range where pairs needing
that lag separate. Two regimes verified by exact-history simulation:

- **Periodic / bounded-structure `c`** (block cycles, the sawtooth colliders, reverse-dyadic
  blocks, growing-distance swaps, dense period-3 swaps): a **linear** dwell-staircase — lag bumps
  every `~B` ticks — separates all cells. `T(k₀)` grows *linearly/polynomially* in `k₀`.
  Verified: **53/53 sawtooth colliders, 60/60 random period-B non-EI, all structured families**
  separate cells `[1..80]` with one fixed staircase (`/tmp/p4q_staircase.py`, `/tmp/p4q_stress.py`,
  `/tmp/p4q_unified.py`).

- **Sparse-gap `c`** (the genuinely hard case): `c =` identity except swap `(2^j, 2^j+1)` for each
  `j` (non-EI; the canonical sparse-gap family). Here the identity-tail pair `(2i,2i+1)` is
  separable **only** at times `t = 2^j+1` (powers of two plus one) and **only** when the lag is
  exactly `∈ {2i, 2i+2}` (verified exactly, `/tmp/p4q_powers_sep_exact.py`). The matching
  trajectory is the **log-lag staircase**: bump lag by 2 at each `t = 2^j` (one LEFT per power of
  two), i.e. `L(t) ≈ 2⌊log₂ t⌋`, riding near the diagonal otherwise. This puts lag `= 2i` at the
  alarm `t = 2^i+1`, separating pair `i` there. **Verified ALL SEPARATED**: `M=20` (depth `2^14`,
  `maxT(k₀)=1024`), `M=33` (depth `2^18`, `maxT(k₀)=65537`) — `/tmp/p4q_unified.py`,
  `/tmp/p4q_powers_nearD.py`. `T(k₀)` is finite but **exponential** in the cell index
  (`T ≈ 2^{k₀/2}`), because lag must monotonically reach `~k₀` and lag rises only logarithmically
  in time (alarms are exponentially sparse). Finite-per-`k₀` is all (Q) requires.

**General rule (statement to formalize):** choose `L(t)` monotone nondecreasing so that for every
pair `(a,b)`, the trajectory's lag equals one of `(a,b)`'s separator-lags at a time inside that
separator's open window. Existence of such `L` follows from (i) lag may grow arbitrarily slowly,
and (ii) catchable-ahead (infinitely many separators per pair, at unboundedly large lag). The
schedule's *rate* is `c`-tailored: window `~B` for `B`-periodic, `~log` for sparse-at-powers.

### Sub-question (ii): finite `T(k₀)` and the finite-belief reduction

Every trajectory starts at `D=0`; oscillating `D∈{0,1}` over the prefix gives, at even `t`, the
signal `[c(k₀)<t]`. First Yes at `t=τ` (`τ≈c(k₀)`) pins `c(k₀)∈{τ−2,τ−1}`, so the belief collapses
to **≤ 2 candidate cells** `{c⁻¹(τ−2), c⁻¹(τ−1)}` — cofinitely many `k` are killed at once.
Verified (`/tmp/p4q_final.py`, part B): belief `≤2` by `t≈c(k₀)` on block5 and swap_powers (e.g.
swap_powers `k₀=20` → `{20,21}` by `t=22`). The remaining 2 consecutive cells are then separated by
the c-tailored tail at the pair's separator time. So `T(k₀) = τ + T_pair(k₀) < ∞` for every `k₀`.
(The infinitely-many-`k` worry is automatic — the belief is finite after the first Yes.)

### Verification ledger (all by exact-dynamics history simulation; parity lock respected)

- `/tmp/p4q_find_colliders.py` — reconstructs the sawtooth `a=2,b=1` colliders (53 over B∈{5,6,7}).
- `/tmp/p4q_lagslack.py`, `/tmp/p4q_uncovered.py` — per-pair separator (D, slack) structure.
- `/tmp/p4q_exact.py`, `/tmp/p4q_powers_dfs2.py` — exact DFS over fixed trajectories (small M).
- `/tmp/p4q_staircase.py`, `/tmp/p4q_stress.py` — linear staircase: 53/53 colliders + 60/60 random.
- `/tmp/p4q_powers_sep_exact.py` — proves swap_at_powers id-tail pairs separate only at `t=2^j+1`,
  lag `∈{2i,2i+2}`.
- `/tmp/p4q_unified.py`, `/tmp/p4q_powers_nearD.py` — log-lag staircase wins swap_at_powers
  (M=33, `T(k₀)=65537`).
- `/tmp/p4q_final.py` — catchable-ahead (∞ separators/pair), sub-(ii) belief-≤2, adversarial
  dense-swap c (all separated).

### Honest caveats / what this does and does not give

- The answer to (Q) is **YES**, decisively, with a constructive c-tailored schedule.
- The **rate** of the lag schedule is c-dependent (linear vs logarithmic vs general). A *single
  closed-form* `L(t)` independent of `c`'s fine structure does NOT work (that would be a universal
  trajectory = negative result #1). The construction is "fixed trajectory **per c**", as (Q) asks.
- For **Lean**: this discharges the winning direction *as a signal-independent strategy* — much
  easier than an adaptive belief-state machine. The formalizable lemma = "monotone-lag staircase
  matched to c's alarm structure separates every pair", whose mathematical core is the already
  axiom-clean catchable-ahead (LemmaA). The remaining engineering is defining the c-tailored lag
  schedule and proving per-`k₀` termination (the dwell/log-rate must be derived from `c`); the
  hard combinatorial heart (distinguishability) is done. This supersedes the "irreducibly adaptive"
  framing for the *fixed-per-c* question — adaptivity was only needed for a *universal* strategy.

---

## UNIFORM GREEDY CONSTRUCTION (2026-05) — the band-top staircase

This section gives the **single uniform algorithm** `c ↦ m` (the *same* algorithm for every
non-EI `c`; only its output `m` depends on `c`) that produces a fixed signal-independent
trajectory satisfying the three obligations of `separating_trajectory_exists` (the lone `sorry`
in `WinningAdaptive.lean`): (i) safety `D_t ≥ 0`, (ii) Yes-emitting, (iii) separating. It
supersedes the "the rate is c-dependent so no uniform schedule exists" caveat above: the rate
*is* c-dependent, but the **algorithm that derives the rate from c is uniform** — it reads off
the dwell lengths from `c`'s separator structure as it goes (a greedy/dovetail), so one
algorithm covers all non-EI `c`.

### The decisive structural facts (all verified empirically, parity lock respected)

Work in the signal identity `Yes at (D,t) ⟺ c(k₀+D) < t`. Write the **lag** `L_t = t − D_t`.
The parity lock forces `D_t ≡ t (mod 2)`, so `L_t` is even; and `dL = 1 − dD ∈ {0,+2}`, so
**lag is monotone nondecreasing** (the central constraint). A *separator* for a pair `(a,b)` is
a triple `(D, slack)` (slack = `t − D` even `≥ 0`) with `[c(a+D)<D+slack] ≠ [c(b+D)<D+slack]`.
At such a moment the trajectory must have lag exactly `slack` (to be at displacement `D` at time
`D+slack`). So **separators must be visited in nondecreasing slack order**, and a pair's
separator at slack `s` is *use-it-or-lose-it* once lag passes `s`.

Empirically (`/tmp/p4u_*.py`, families: block-`B` cycles, reverse blocks, adjacent-transposition
involution `c(2i−1)=2i`, sparse `swap_at_powers` `=` id except swap `(2ʲ,2ʲ+1)`, and 40 random
period-`B` "sawtooth-collider" perms):

1. **Slack-band is bounded per pair.** Each pair `(a,b)` has separators only in a small band of
   slack values `band(a,b) ⊆ {0,2,4,…}`. Slack does NOT go unbounded per pair — this is why a
   monotone-lag walk cannot "come back later" to a missed pair, and why the construction is
   subtle.
2. **`bandTop(a,b) ∈ {max(a,b), max(a,b)+1}`**, i.e. `bandTop(a,b) = 2·⌈max(a,b)/2⌉` (the least
   even number `≥ max(a,b)`) — exact on every family tested (distribution of `bandTop − max` is
   `{0,1}` only; `+1` exactly when `max(a,b)` is odd, forced by slack being even). In
   `g`-coordinates `g(m)=c(m)−m`, separation at slack `s` reads `[g(a+D)<s−a] ≠ [g(b+D)<s−b]`; the
   larger cell governs the largest slack at which the bit can still flip. The clean consequence is
   `max(a,b) ≤ bandTop(a,b) ≤ max(a,b)+1`, which is all that fact 4 needs.
   **(Earlier draft wrongly claimed `bandTop = max` exactly; the `+1` parity correction was found
   by a wider scan — `/tmp` violation count 42–91 for the strict-equality claim.)**
3. **Band-top recurrence at unbounded D.** For each pair, separators at slack `= bandTop(a,b)`
   occur at *infinitely many displacements `D`* (recur-counts in the hundreds; even sparse
   `swap_at_powers` id-tail pairs recur at `D` up to ≥ 500, at powers of two). This is the exact
   termination guarantee for the per-pair ride.
4. **Band-top finiteness.** Since `bandTop(a,b) ≥ max(a,b)` (fact 2), `{(a,b) : bandTop ≤ S} ⊆
   {(a,b) : max(a,b) ≤ S}`, which has `≤ C(S,2)` pairs — **finite**. So ordering pairs by
   `bandTop` has order type `ω`.
5. **Yes engine.** `{p : c(p) ≤ p}` is infinite for every permutation (standard; verified, counts
   grow linearly). Combined with lag `→ ∞`, this gives Yes for every `k₀`.

### The algorithm (precise move rule, a function of `c`)

Enumerate all unordered pairs of distinct start cells, ordered by the key
`key(a,b) = (bandTop(a,b), max(a,b), min(a,b))` ascending (a well-order of type `ω` by fact 4;
`bandTop` is computable from `c` by fact 3 since the band is bounded). Maintain trajectory state
`(D, L)` with `t = D + L`, starting `(0,0)`; the move list `m` is appended to. The two
primitives keep `D ≥ 0`:

- **R** (right): append `.right`; `D += 1`. Lag unchanged.
- **L** (left): *requires `D ≥ 1`*; append `.left`; `D −= 1`, `L += 2`.

Process pairs `P₀, P₁, …` in `key` order. For pair `P = (a,b)` with `τ = bandTop(P)`:

> **Skip** if some already-emitted step separated `(a,b)` (replay the partial trajectory; cheap).
> Otherwise:
> 1. **Bounded descend:** while `D > 0` and `L < τ`: do **L**.  (Walk toward `D = 0`, capped so
>    lag never exceeds `τ`.)
> 2. **Raise lag:** while `L < τ`: if `D = 0` do **R** (lift so an L-move is legal), then do **L**.
>    (Bumps lag by 2 each pass, oscillating `D ∈ {0,1}`; ends with `L = τ`.)
> 3. **Ride to separator:** do **R** repeatedly until `[c(a+D)<D+τ] ≠ [c(b+D)<D+τ]` holds at the
>    current `D` (with lag `= τ`). Terminates by fact 3.

`m` is the concatenation of all phases. (For `t` beyond the construction one may append `.right`;
the per-`k₀` stop time only ever uses a finite prefix.)

### Why this is well-defined and the ordering invariant (no overshoot)

When we begin pair `P`, **`L ≤ τ(P)`**. Proof: after finishing any earlier pair `P'` we had
`L = τ(P')` (step 2 ends at `L=τ`, step 3 rides keep `L` fixed); and `τ(P') ≤ τ(P)` since pairs
are processed in `bandTop` order. The bounded descend (step 1) only *raises* `L` and is explicitly
capped at `τ`. So `L ≤ τ` throughout, step 2 is a genuine raise (never a lower), and step 3 reads
the band-top slack — the pair's separators there exist at unbounded `D ≥` current `D` (fact 3),
so step 3 terminates. **The descend-to-`D=0`-first variant (no cap) was tried and FAILS** — it
overshoots `τ` of the next pair and strands it (witness: `block5` pair `(1,6)`, lag became `8 > 6`).
The cap is essential.

### Proof of (iii) SEPARATING

Every pair `(a,b)` with `a≠b` appears at a finite position `n` in the `key` enumeration (fact 4:
finitely many pairs precede it). When processed it is either already separated by the trajectory
so far, or step 3 drives the trajectory onto one of its band-top separators, where the signals at
displacement `D` from `a` and `b` differ. Either way the histories of `a` and `b` differ at some
finite time. So `hsep` holds. **Crux lemma needed:** band-top recurrence (fact 3) for the
ride to terminate, plus band-top finiteness (fact 4) for the enumeration to reach every pair.

### Proof of (i) SAFETY

`D_t ≥ 0` for all `t`: R increments `D`; L is only ever emitted when `D ≥ 1` (guarded in both
descend and raise), decrementing `D` to `≥ 0`. Hence from any start `k₀ ≥ 1`, position
`= k₀ + D_t ≥ 1`. Trivial and airtight, exactly as the task anticipated.

### Proof of (ii) YES-EMITTING

`Yes at (D,t) ⟺ c(k₀+D) < t = D+L ⟺ g(k₀+D) < L − k₀`. The construction raises lag to every
band-top, and band-tops `= max(a,b) → ∞`, so **`L → ∞`** along the trajectory. Two regimes,
both observed, together covering all `k₀`:

- *Low cells / dense `c`:* steps 1–2 oscillate `D ∈ {0,1}`, revisiting `D = 0` at times
  `t = L = 2,4,6,…`. At a `D=0` visit, `Yes ⟺ c(k₀) < L`, which holds once `L > c(k₀)`.
- *High cells / sparse `c`:* when the trajectory rides far right at lag `L`, it visits cells
  `k₀+D` for a long run of `D`. Since `{p : c(p) ≤ p}` is infinite (fact 5) and the ride reaches
  arbitrarily large `D`, it visits some `p = k₀+D` with `c(p) ≤ p`; once `L > k₀` this gives
  `c(p) ≤ p < p + (L−k₀) = t`, a Yes.

**Crux lemma needed:** `L → ∞` (from band-tops unbounded, fact 4) together with fact 5
(`{p:c(p)≤p}` infinite) — or, on the dense regime alone, the `D=0`-revisit-at-`L→∞` observation.
The bounded-descend variant exhibits the `D=0` revisits explicitly (6–13 of them on dense
families), making the dense-regime argument the clean Lean target; the sparse regime needs fact 5.

### EXACT separator-existence statements required

The bare `separators_exist` (one separator per pair, axiom-clean, already in `WinningAdaptive`)
is **NOT enough**. The construction needs two strictly stronger statements:

- **(S1) Band-top recurrence.** For every pair `(a,b)` with `a≠b` and non-EI `c`: separators at
  slack `bandTop(a,b)` occur at infinitely many displacements `D` (`∀ D₀ ∃ D ≥ D₀` a separator at
  that slack). This is *more* than "separators at unbounded displacement" — it pins the slack to
  the band-top. (`separators_unbounded`, which the task said may be assumed, gives unbounded `D`
  but not at a *fixed* slack; (S1) additionally needs that the band-top slack itself recurs.)
- **(S2) Band-top finiteness.** For each `S`, `{(a,b) : bandTop(a,b) ≤ S}` is finite. Reduces to
  the *lower* bound `bandTop(a,b) ≥ max(a,b)` (fact 2: `max ≤ bandTop ≤ max+1`; verified, 0
  violations). NB the band is *not* contained in `[max,∞)` — small-slack separators exist too
  (e.g. `band(1,2)={0,2}`); the relevant fact is only that the band's *top* reaches `≥ max(a,b)`,
  so `bandTop → ∞` with `max(a,b)`, giving `{(a,b):bandTop ≤ S} ⊆ {(a,b):max ≤ S}` finite. The
  precise mechanism for `bandTop ≥ max` (which displacement realizes the high-slack separator) is
  not needed for the algorithm — only the bound — but should be pinned down for the Lean proof.

Both verified empirically on every family (structured + 15 random colliders). **Honest status:**
(S2)'s needed lower bound `bandTop ≥ max(a,b)` is elementary from the `g`-coordinate signal
identity. (S1) is the genuinely stronger fact; it should follow from LemmaA's machinery
(`not_eventually_identity_…` gives separators; the band-top recurrence needs the bijectivity
bookkeeping that the band-top slack is achieved at infinitely many displacements) but is **not yet
formalized** — flagged as the new lemma to prove.

### Empirical validation (uniform greedy, identical algorithm for every family)

All by exact-dynamics history simulation with the parity lock (`D_t ≡ t mod 2`) enforced:

- **Separation + safety + Yes:** 6/6 structured families (block-3/5/7 cycles, reverse-block-5,
  adjacent-transposition involution, sparse `swap_at_powers`) fully separate cells `[1..N]`
  (`N` up to 30), `D_t ≥ 0` throughout, Yes for every interior cell. (`/tmp/p4u_*.py`.)
- **Sawtooth-colliders (the universal-trajectory killers):** 40/40 random period-`B`
  (`B∈{5,6,7}`) non-EI perms fully separated and safe — the *same* greedy that no fixed
  c-independent schedule could beat.
- **Sanity (EI loses):** the c-INDEPENDENT epoch staircase leaves identity with 14 unseparable
  pairs `(2j,2j+1)` (correct — EI ⇒ Bob loses), and leaves `swap_at_powers` with 7 collisions
  (correct — a *universal* trajectory cannot do sparse gaps); only the **c-tailored greedy**
  (dwell extended via (S1)) clears `swap_at_powers`. This is exactly why the algorithm must read
  the dwell length from `c`.
- **Belief → singleton:** by `ofMoves_localizes` (already proven in Lean), (i)+(ii)+(iii) ⇒
  `Localizes` for every `k₀` (first-Yes finiteness `yesSet_finite` collapses the belief to ≤2,
  then separation finishes). No separate check needed — the Lean reduction is airtight.

### Lean-feasibility assessment (honest)

The construction slots **directly** into `separating_trajectory_exists (c) (h : ¬EI c)` in
`WinningAdaptive.lean` as an explicit `m : ℕ → Dir` (then `ofMoves m`); everything downstream
(`ofMoves_localizes`, `localizes_BobWins`) is already proven and axiom-clean. To formalize:

- **Routine / tractable:**
  - The two move primitives and the `D_t ≥ 0` invariant (safety) — pure arithmetic on `cumDelta`.
  - `bandTop(a,b) = max(a,b)` and (S2) band-top finiteness — elementary in the `g`-coordinate.
  - The well-founded `ω`-enumeration of pairs by `(bandTop, max, min)` and the no-overshoot
    invariant (`L ≤ τ` at each pair) — structural induction over the greedy.
  - The recursive definition of `m` as a concatenation of phases (define the state machine, prove
    each phase appends finitely many moves).
- **The new lemma to prove (research-shaped but plausibly tractable):** **(S1) band-top
  recurrence.** This is the one piece beyond what is currently axiom-clean. It is stronger than
  `separators_exist`/`separators_unbounded`; it should reduce to LemmaA's value-hogging/bijectivity
  bookkeeping but is not yet written. Until (S1) is formalized, `separating_trajectory_exists`
  cannot be fully discharged — though the *reduction* and all of (i),(ii)-dense,(iii)-modulo-(S1)
  are clean.
- **(ii) Yes-emitting, sparse regime** additionally needs fact 5 (`{p:c(p)≤p}` infinite) plus
  "the ride reaches arbitrarily large `D`"; the dense regime needs only the `D=0`-revisit
  observation. Both are elementary given `L→∞`.

**Bottom line.** A genuinely *uniform* construction exists, is fully specified, and is validated;
its correctness rests on two named separator-existence facts, of which (S2) is elementary and
(S1) — *band-top recurrence at unbounded displacement* — is the single remaining nontrivial lemma
(strictly between `separators_exist` and a full structure theorem). This replaces the previous
"irreducibly adaptive belief-state" framing for the formalization target: the winning strategy
can be a fixed signal-independent trajectory, and the remaining gap is one combinatorial lemma,
not an adaptive-foresight machine.

---

## AUDIT + FRESH ATTACK (2026-05) — architecture re-confirmed; new reformulation; wall re-pinned

A dedicated birds-eye audit + fresh attack on the lone `sorry`
(`noSeparator_allSlack_imp_eventuallyIdentity` in `WinningAdaptive.lean`). Verdict and findings:

### JOB 1 — architecture verdict: KEEP (no simpler route found)
The lag-monotone constraint `L_{t+1} ∈ {L_t, L_t+2}` is *forced* by `D_t ≡ t (mod 2)` + `|ΔD|=1`,
so the slack/lag-coordination crux is INTRINSIC to every strategy, not an artifact of the
fixed-trajectory choice. Every documented alternative is already killed: universal trajectory
(sawtooth colliders), monotone-right (block-3), K-decoder (block-5), adaptive belief-state (same
low-slack/large-D tension; strands on the involution at lag>max). Determinacy/compactness gives
non-constructive existence but no Lean-checkable strategy. The band-top staircase + belief
reduction (already proven, axiom-clean, modulo this one lemma) is the cleanest formalizable target.

### JOB 2 — the two-slack angle (NEW) and why it does NOT close the proof
*New idea (advisor):* `hno` quantifies over ALL even `s ≥ max`, so use TWO consecutive even slacks
`s₀ = leastEvenGe(max)` and `s₀+2` at once. Agreement at both bins the pair `(c(a+D),c(b+D))`:
(A) both `< D+s₀`; (B) both in `{D+s₀, D+s₀+1}` ⟹ consecutive (engine-feeding); (C) both `> D+s₀+2`.

**Empirically validated (all GENUINE bijections, /tmp/p4_*.py):**
- Two-slack window `{s₀, s₀+2}` always contains a recurring (unbounded-`D`) separator: **0/495+
  failures** across involution, block3/5, rev-blocks, growing-block (unbounded `g`), swap_at_powers
  (log-sparse), parity-shift, random period-`B`. So `hno` is contradicted by just `s₀` and `s₀+2`.
- Recurring-slack EXCESS `s − s₀` is uniformly `≤ 2` (parity-shift `c(2k)=2k+2,c(2k+1)=2k−1` for
  `k≥1`, `c(1)=2` — a verified genuine bijection of ℕ⁺ with 0 fixed points (one bi-infinite chain
  `…→7→5→3→1→2→4→6→…`) — realizes excess exactly 2; pair `(4,6)`: slack 6 empty, slack 8 recurs).

**Why it still does NOT close (HONEST — confirmed empirically, the advisor retracted closure):**
At a *weak descent* of the lower cell `a` (`weak_descents_infinite`, axiom-clean), `c(a+D) ≤ a+D <
D+s₀`, so those D's land in **bin A only** — bin B (the consec conclusion) is excluded exactly where
we have a free supply of D's. Measured bin densities under two-slack agreement: **bin B is empty at
~all D** for every family (`/tmp/p4_bins.py`), so the consec/`chain_bound` route never fires from
two-slack agreement. The fallback "bin A cofinite ⟹ pigeonhole" gives only a ONE-SIDED upper bound
`g(a+D) ≤ s₀−a−1`; the involution (`g ∈ {±1}`, non-EI, genuine bijection) shows one-sided-`g` +
bijection ≠ EI. This is precisely the documented "upper-bound + bijection ≠ EI" residue.

### NEW durable artifact — clean interval reformulation of `hno` (0 mismatches, verified)
`hno` ⟺ *for cofinite `D`, the half-open interval `(min(c(a+D),c(b+D)), max(c(a+D),c(b+D))]`
contains NO even integer `≥ b`.* (Verified exact on involution + parity-shift, all pairs.) This is
the cleanest Lean-statable form of the hypothesis and the recommended phrasing if the lemma is
re-attacked: it turns the slack quantifier into a single "no even point in an interval" condition.

### Engine-side confirmation the wall is irreducible (NEW probe)
The proven `IndistFrom` engine (`indist_consec_from` etc.) reads the signal at times of slack
`min(c(a+D),c(b+D)) − D + {0,1,2}`. At good-but-low-min displacements (e.g. involution `(2,4)`,
`min−D=1`, critical slack `2 < b=4`) the engine's critical time has slack `< b`, OUTSIDE `hno`'s
range `s ≥ b`. So `hno` controls ONLY one even-slack bit per `D` and provably cannot uniformly feed
the three-times-per-`D` engine. (`/tmp/p4_engine_probe.py`.) This is the same residue from the
engine side: the coordination of `separators_unbounded` (axiom-clean, floors displacement) with
`weak_descents_infinite` (axiom-clean, floors the lower cell) on a COMMON displacement is the open
combinatorics — and no generic "two positive-density sets intersect" lemma applies (two
positive-density sets need not intersect: evens vs odds), so Mathlib offers no shortcut.

**Status unchanged: the lone `sorry` is TRUE (decisively, genuine bijections incl. unbounded-`g` and
no-identity-tail), well-isolated, and the wall is genuine — not closed this session. Build GREEN;
no Lean edits made (no real proof found, per the no-false-lemmas rule).**

## CURRENT STATUS (2026-05-23) — staircase FORMALIZED; winning direction reduced to ONE lemma

The band-top staircase of the previous section is now **formalized in Lean** (`WinningAdaptive.lean`),
not merely specified. `lake build` is GREEN (3334 jobs). `main : BobWins c ↔ ¬ EventuallyIdentity c`
(`Answer.lean`) is proven in BOTH directions, with the winning direction complete **modulo exactly
one isolated, computationally-verified combinatorial lemma**. We do NOT claim `main` is fully proven
or axiom-clean.

### Axiom audit (from `#print axioms`, the ground truth — supersedes any prose in source comments)

AXIOM-CLEAN (no `sorryAx`; only `[propext, Classical.choice, Quot.sound]`):
- Losing direction: `EventuallyIdentity_loses` (`Losing.lean`).
- Distinguishability / Lemma A: `Indistinguishable_implies_eventually_identity`,
  `not_eventually_identity_implies_distinguishable` (`LemmaA.lean`).
- Separator inputs: `separators_unbounded`, `weak_descents_infinite` (`WinningAdaptive.lean`).
- The REDUCTION: `localizes_BobWins`, `ofMoves_localizes`, `yesSet_finite` (first-Yes finiteness
  that collapses the infinite candidate set to a finite one).
- The K-decodable winning family for arbitrary K : ℕ+: `LocallyDecodable_BobWins` (K=2),
  `LocallyK3Decodable_BobWins` (K=3), `LocallyKDecodable_BobWins` (any K); capstone
  `locallyDecodable_main`.
- Pigeonhole bridge `fixedSlack_of_boundedSlack_recurrence`, conversion
  `separatorAtSlack_imp_separatedAtDisp`.

CARRIES `sorryAx` (solely through the ONE lemma below):
- `noSeparator_allSlack_imp_eventuallyIdentity` (line ~590) — **THE single `sorry` on `main`'s
  path**. Contrapositive of `band_recurrence_ge_max`.
- `band_recurrence_ge_max` → `separating_trajectory_exists` (= staircase safety+separation+Yes:
  `stair_safe`/`stair_separates`/`stair_yes`, all otherwise fully proven) → `notEI_BobWins` →
  `main`.

ORPHAN `sorry` (NOT on `main`'s path, irrelevant to the main audit):
- `boundedSlack_recurrence` (line ~431) feeds `band_recurrence`, which `main` does NOT use. The
  source comments in `Answer.lean`/`WinningAdaptive.lean` that say "modulo TWO lemmas" overstate;
  the `#print axioms` audit shows `main`'s `sorryAx` flows through `band_recurrence_ge_max` only,
  i.e. the one lemma `noSeparator_allSlack_imp_eventuallyIdentity`.

### The one residual lemma (precise)

`band_recurrence_ge_max`: for non-EI c and any a ≠ b, there is an EVEN slack s ≥ max(a,b) whose
slack-s separators recur at unbounded displacement (∀ D₀ ∃ D ≥ D₀ : [c(a+D)<D+s] ≠ [c(b+D)<D+s]).
- STRONGER than `separators_unbounded` (which gives unbounded D but at possibly unbounded slack);
  this pins the slack to the finite window [max, max+O(1)], needed because the staircase rides at
  one fixed lag. The `≥ max` lower bound is load-bearing: it makes the pair enumeration order-type
  ω (finitely many pairs per slack level), so every pair is processed at a finite phase.
- WHY TRUE: `weak_descents_infinite` (axiom-clean) pins the lower cell into the slack window;
  `separators_unbounded` (axiom-clean) gives the displacements; the lemma asserts these two
  infinite sets coordinate. DECISIVELY VERIFIED: 2300+ (family, pair) cases, 0 counterexamples,
  recurring-slack excess s − max ≤ 2 across ALL families (canonical witness `leastEvenGe(max)`;
  only the parity-shift c(2k)=2k+2, c(2k+1)=2k−1 needs max+2).
- WHY HARD: `hno` gives signal agreement at ONE time t=D+s per displacement (one bit per D); the
  Lemma-A engine (`indist_consec`, pinning |c(a+D)−c(b+D)|=1) reads THREE times per D, so single-
  slack agreement does not fire it. The universal quantifier over s is load-bearing (the parity-
  shift counterexample agrees at a single fixed slack forever yet is non-EI). It is a slack-
  localized strengthening of Lemma A that the displacement-flooring `IndistFrom` machinery does
  not supply — the genuine combinatorial residue.

### Honest bottom line

The ANSWER is settled and confirmed; the ARCHITECTURE of both directions is fully formalized. The
losing direction and distinguishability theorem are machine-checked and axiom-clean; the winning
direction is reduced — through a fully machine-checked reduction (`localizes_BobWins`) and a fully
machine-checked staircase construction — to ONE explicit, precisely stated, computationally-verified
combinatorial recurrence lemma. The winning direction is therefore **proven modulo this one true
lemma**; it is NOT yet a complete, `sorry`-free proof. Writeup (`griddles-p4-writeup/writeup.tex`)
updated 2026-05-23 to reflect this exact state (12 pages, compiles clean with `lualatex`).

## ATTEMPT LOG — "POSITIVE-DENSITY of low-slack separators" angle (2026-05-23) — BROKEN

*New idea (advisor):* instead of seeking a single common point between two infinite sets
(`separators_unbounded` ∩ `weak_descents`, which the "evens-vs-odds need not intersect" wall blocks),
target a POSITIVE-DENSITY lower bound: show `S(N) := #{D < N : ∃ even s ∈ {leastEvenGe(M),
leastEvenGe(M)+2} with a slack-`s` separator at D}` satisfies `S(N) ≥ c·N − O(1)`, then pigeonhole
over the ≤2 slacks to get a single recurring slack. The premise (from "fresh data" at D ∈ [0,300]):
the recurring witness slack is ALWAYS in `{leastEvenGe(M), leastEvenGe(M)+2}` and fires at positive
density.

**VERIFIED EMPIRICALLY FIRST (`density_probe.py`, `density_decay.py` in `griddles-p4-verify/`) —
THE ANGLE BREAKS. Two independent, decisive witnesses:**

1. **`swap_at_powers` kills the density bound itself (even all-slack).** Separators occur ONLY at
   `D = 2ᵏ − b` (log-sparse): for pair (2,3) the separating displacements are exactly
   `1,5,13,29,61,125,253,…,262141` (= `2ᵏ−3`). Hence `S(N) ≈ log₂(N)`, so `S(N)/N → 0`:
   measured `dens = 0.0045 → 0.0014 → 0.00041 → 0.00012 → 0.000034` as `N = 2k → 500k`. This is
   NOT a window artifact — allowing EVERY even slack ≥ M (`allslack` column) gives the IDENTICAL
   log-count. No counting/averaging argument can lift `O(log N)` to `Ω(N)`. The target
   `S(N) ≥ c·N − O(1)` is simply FALSE for this (genuine, non-EI) bijection.

2. **`growing_blocks_rev` kills the `{leastEvenGe(M), leastEvenGe(M)+2}` restriction (premise false).**
   The 2-element-window density decays to 0 (`0.044 → 0.022 → 0.011 → 0.0056 → 0.0032` as `N` grows),
   WHILE the all-slack density stays a healthy constant (0.5 for pair (1,2); 0.39 for (3,4)). So
   separators ARE dense — but at slacks that DRIFT UPWARD with the block index, NOT confined to
   `{leastEvenGe(M), +2}`. The task's "fresh data" was anchored at small `D` where blocks are still
   small; it does not extrapolate. This re-confirms the prior log's line ~618 finding (recurring
   slack window drifts to ~776 on (2,4)); the recurring-slack excess `s − M` is **unbounded** for
   growing_blocks_rev, contradicting the "always ≤ 2" premise.

**Why no salvage:** even pigeonholing over ALL `O(N)` candidate slacks `≤ N+M` buys nothing on
`swap_at_powers` — the TOTAL separator count over all slacks is still `O(log N)`. The two
obstructions are independent: (1) defeats any density bound; (2) defeats any bounded-slack-window
restriction. The genuine residue is unchanged — it is the *coordination* of two infinite sets on a
common displacement, and that coordination is genuinely sparse (`O(log N)`) for `swap_at_powers`,
so "infinitely often" is the strongest true statement, NOT "positive density".

**Net:** angle refuted with concrete witnesses. NO Lean edits (no false lemma introduced, per the
no-false-lemmas rule). Build GREEN (3334 jobs, `#print axioms main` unchanged: `sorryAx` flows
solely through `noSeparator_allSlack_imp_eventuallyIdentity`, the lone `sorry` at line 692). Durable
artifacts: `density_probe.py`, `density_decay.py`.
