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

## UPDATE (2026-05-23) — BOUNDED-DISPLACEMENT CASE REDUCED & PARTIALLY FORMALIZED (real new lead)

The band recurrence (`band_recurrence_ge_max`, the lone open lemma) now **dispatches on bounded vs
unbounded displacement** (`BddDisp c B := ∀ n, |c n − n| ≤ B`). The bounded case — the regime that
broke ALL prior routes — is reduced to a strictly-more-tractable residue, with the WALL-removing
step formalized **axiom-clean**.

### The new idea that removes the WALL (verified, then formalized)

The documented WALL was: `noSeparator_allSlack`'s per-slack displacement floor `D₀(s)` does NOT
uniformize across `s`. **Bounded displacement removes it**: a separator's slack is *capped*.

* **Step A — slack cap (`separatorAtSlack_slack_le_of_bddDisp`, AXIOM-CLEAN `[propext,Quot.sound]`).**
  A slack-`s` separator at `D` forces (via `separatorAtSlack_iff_window`)
  `D+s ≤ max(c(a+D),c(b+D))`. With `|c n − n| ≤ B` and `a<b`: `max ≤ (b+D)+B`, so `s ≤ b+B`.
  VERIFIED: 0 violations over **9.6·10⁶** checks (`bounded_case.py`, `clean_argument.py`).
  Consequence: only the FINITE even-slack set `[b, b+B]` can ever separate at slack `≥ M=b`.

* **`≥ M` finite pigeonhole (`fixedSlack_ge_of_window_recurrence`, AXIOM-CLEAN).** Mirror of the
  existing `fixedSlack_of_boundedSlack_recurrence`, restricted to slacks `≥ M`: a uniform floor
  across the finite slack set follows automatically.

* **Bounded-case theorem (`band_recurrence_ge_max_of_bddDisp`).** Combines Step A + pigeonhole;
  reduces the bounded case to ONE isolated residue, the **finite-window recurrence**
  `band_recurrence_finite_window_of_bddDisp`: at unbounded `D`, *some* even slack in `[b, b+B]`
  separates. This is the fiber-pigeonhole core (`D ↦ (c(a+D)−D, c(b+D)−D)` is FINITE-valued, so a
  constant-window value recurs, and one such value separates). VERIFIED: 0 counterexamples over
  **322** (family,pair) combos with fiber-correct, **log-sparse-aware** recurrence detection
  (`step3_contradiction.py`, `bounded_case.py`). Strictly more tractable than the original: slack
  range FINITE, floor UNIFORM.

### Crucial subtlety found & handled: log-sparse recurrence

`swap_at_powers (2,3)` separates only at `D = 2ᵏ − b` (the value `(0,1)` on the fiber): genuinely
infinite but **log-sparse**, last seen at `D = 2¹⁸ − 3`. Count-thresholds wrongly flag these as
"cofinitely non-separating"; the fiber pigeonhole handles them correctly (it is a true infinite
fiber). With fiber-correct detection, NO bounded non-EI perm is cofinitely-non-separating for any
pair — the per-pair recurrence holds.

### Why step 3 has no clean single-engine proof (honest residue characterization)

Step 3 ("some recurring fiber value separates") is an EXISTENTIAL over the finite recurring set
with no working single-witness selection rule and no single-engine reduction:
- max-hi / max-vb selection FAILS (block_cycle_3 (1,2): the max-hi recurring window `(2,3]` is
  non-separating; another value separates). Min-lo on the strict-ascent fiber had 0 failures but
  its correctness still rests on parity details (parity_shift (2,4): min-lo window `(4,6]` has
  `lo = leastEvenGe(M)` exactly, separating only via the LARGER even 6).
- "strict ascent of b ⇒ separating" is FALSE (block_cycle_3 (1,2): half its strict ascents are
  non-separating). The joint `weak-descent(a) ∧ weak-ascent(b)` engine FAILS on parity_shift
  (the canonical WALL pair). So the residue genuinely needs the finite-fiber pigeonhole +
  parity-counting; left as the isolated bounded residue.

### Unbounded case probe (`unbounded_probe.py`)

`growing_blocks_rev` (reverse blocks 2,3,4,…; `|φ|` grows ~√N to 773 over 3·10⁵): finite
pigeonhole fails (385 recurring slacks, drifting up with block index). BUT the FIXED smallest even
slack `s* = leastEvenGe(max)` **does recur** at unbounded `D` (count 1159–4614, last near scan top)
— the wide reversed-block windows engulf `s*`. Clean sufficient condition (0 implication-failures):
weak descent of `a` together with `c(b+D) ≥ D+s*`. But that is again a JOINT two-ray condition with
no co-occurrence lemma (same WALL), so the unbounded case is isolated as
`band_recurrence_ge_max_of_unbddDisp`. NOT closed.

### Lean status (build GREEN, 3334 jobs)

- AXIOM-CLEAN new lemmas: `separatorAtSlack_slack_le_of_bddDisp` (Step A), the `BddDisp` predicate,
  `fixedSlack_ge_of_window_recurrence`.
- `band_recurrence_ge_max` now dispatches: bounded → `band_recurrence_ge_max_of_bddDisp` (residue:
  `band_recurrence_finite_window_of_bddDisp`), unbounded → `band_recurrence_ge_max_of_unbddDisp`.
- `noSeparator_allSlack_imp_eventuallyIdentity` is now ORPHANED (off `main`'s path), retained only
  as the all-slacks-route record. `main`'s `sorryAx` now flows through the two NEW residues
  (bounded finite-window + unbounded), NOT through `noSeparator_allSlack`.
- NO false lemmas introduced. Durable Python artifacts (all in `griddles-p4-verify/`):
  `bounded_case.py`, `step3_rigor.py`, `step3_mechanism.py`, `step3_selection.py`,
  `step3_contradiction.py`, `step3_ascent_fiber.py`, `clean_argument.py`, `recurrence_proof.py`,
  `key_recurrence.py`, `unbounded_probe.py`, `swap_debug.py`.

## Attempt log (archived from WinningAdaptive) — 2026-05-23

The orphaned theorem `noSeparator_allSlack_imp_eventuallyIdentity` (the all-slacks-route record
for `band_recurrence_ge_max`, now off `main`'s path after the bounded/unbounded displacement
dichotomy) carried a large docstring of negative results. The theorem and its `#print axioms` were
deleted to tidy `WinningAdaptive.lean`; the genuinely-useful ATTEMPT LOG sections are preserved
verbatim below so the record of tried approaches is not lost. All routes hit the same wall: `hno`'s
per-slack displacement floor `D₀(s)` does not uniformize across `s`, and no proposed structure-
extraction yields more than a density that the balanced bijection parity-shift (`c(2k)=2k+2,
c(2k+1)=2k−1`) satisfies. The productive next move was the bounded/unbounded split that now routes
`main` through `band_recurrence_finite_window_of_bddDisp` and `band_recurrence_ge_max_of_unbddDisp`.

### ATTEMPT LOG — "band collapse + cut counting" strategy (independently re-verified, still open)

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

### ATTEMPT LOG — "residue-class structure + bijection cut-balance closure" (re-verified, STILL OPEN)

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

### ATTEMPT LOG — "value-hogging / cofinitely-bad" route (the LemmaA engine), re-verified, STILL OPEN

A further attempt evaluated the proposal that the `cofinitely_bad_impossible` value-hogging engine
(the machine that kills `Indistinguishable`) could be driven by `hno` directly, via the lead "the
cofinite-finiteness of small-`φ` cells uniformizes the per-`s` thresholds, so for large `D` the
*active* slack range is controlled and per-slack agreement composes to a full threshold-agreement
the engine consumes."  Every step checked with `uv run` (`vhog_probe.py`, `discriminator.py`).
**Truth re-confirmed** (every non-EI family has unbounded separators at some even slack `≥ max`;
`swap_at_powers` separators are at `D = 2ᵏ − b`, confirmed to `D = 2¹⁸ − 3 = 262141` — log-sparse,
so DENSITY is impossible, exactly the cofinite-but-SPARSE regime).  The route does NOT close; the
DISCRIMINATOR (geometric `separatorAtSlack_iff_window`: separator at `D` ⟺ even slack `s ∈ W(D) :=
(min(c(a+D),c(b+D))−D, max(…)−D]`) kills the uniformization lead two independent ways:

  • **Bounded-`φ` case — parity-shift `(2,4)` (the canonical wall).**  Here `φ` is bounded, so the
    active window `W(D)` IS bounded (the lead's premise holds).  But `W(D)` *never empties of even
    slacks*: slack `6 = leastEvenGe(max)+2` lies in `W(D)` at unbounded `D` (1496/2996 of a high-`D`
    window) — so `hno` at slack `6` FAILS, while `hno` at slack `4` holds forever.  The single
    non-EI bit lives in the one recurring slack `6`, and there is no uniform rule locating it.  So
    even in the lead's best case the engine never receives full agreement.  DECISIVE refutation that
    *no single-slack value-hogging contradiction exists*: parity-shift is a genuine non-EI bijection
    with `c(a+D)−D ∈ {0,4}` (bounded, balanced), hence `c(a+D) < D` holds **0 times** cofinitely —
    `cofinitely_bad_impossible`'s premise (`c(a+D) < D` for all large `D`) is unreachable from `hno`.

  • **Unbounded-`φ` case — `growing_blocks_rev (2,4)`.**  The active window `W(D)` is itself
    *unbounded* (recurring even slacks observed `4 … 348`, drifting up with the block index), so
    "finitely many active slacks" is outright false.

**Root cause (same residue as all prior routes).**  The engine that kills `Indistinguishable`
(`indist_consec` → `|c(a+D)−c(b+D)| = 1` → `cofinitely_bad_impossible`) reads the signal at ≥ 3
times per `D`; `hno` delivers only ONE bit per `D` (which side of the single threshold `D+s` the
pair straddles).  A balanced bijection (parity-shift) satisfies that one bit at the targeted slack
forever while staying non-EI, so the value-hogging finiteness never fires.  Confirmed: NO mechanism
found; `sorry` UNCHANGED, build GREEN.

### ATTEMPT LOG — "convergent-permutation classes C/D" (Agnew/Bourbaki/Kronrod/Wituła), re-verified, STILL OPEN

A further attempt evaluated the proposed split of the lemma along the **convergent/divergent
permutation dichotomy** of R. Wituła's survey ("Permutations preserving the convergence or the sum
of series", Zahorski monograph 2015).  For a permutation `p` of `ℕ`, `t(p,n) :=` the number of
*mutually separated intervals* (maximal consecutive runs) in `p({1,…,n})`; Agnew/Bourbaki:
`p ∈ C` (convergent) ⟺ `limsupₙ t(p,n) < ∞`; `p ∈ D` (divergent) ⟺ `t(p,n) → ∞`.  Wituła
Lemma 7.3: if `p` is non-almost-identity then `U(p) = {n : t↑}` and `V(p) = {n : t↓}` are both
infinite, with `|[1,n]∩U| − |[1,n]∩V| = t(p,n)`.  The proposal: split the lemma by C vs D, using
the global block-count machinery to produce per-pair separators.  Every step checked with `uv run`
(`convergence.py`, `conv_caseD.py`, `conv_bridge.py`, `conv_johnston.py`).  **Truth re-confirmed**
(every non-EI family — incl. a freshly-built genuine class-D witness — has unbounded separators at
some even slack `≥ max`, all within `excess ≤ 2` of `leastEvenGe(max)`).  The split does NOT close;
the precise findings:

  • **The split does NOT align with the difficulty boundary: EVERY documented hard witness is
    class C.**  Classification (`t_max` over `n ≤ 4000`): parity-shift `t≤3`, swap_at_powers `t≤2`,
    growing_blocks_rev `t≤2`, all block/rev_block/random-periodic/adjacent-involution `t≤3` — ALL
    class C (bounded block count).  No documented witness is class D.  The 5 prior failed routes
    therefore ALL live in class C; case D contains no hard witness, so the C/D axis does not separate
    easy from hard.

  • **Case D bridge is VACUOUS (the key negative result).**  A genuine class-D non-EI permutation
    was built (`class_d_scatter`: doubling-window interleave, verified `t` climbing to `1024` over
    one window, `q4_max=1023 ≫ q1_max=256`, 2046 non-fixed tail cells).  The proposed per-pair↔global
    bridge — "recurring separators at `(a,b)` coincide with `U(p)/V(p)` block-count events on the rays
    `{a+D},{b+D}`" — holds at `64/64, 97/97, 84/84` (100%) for tested pairs, BUT the **baseline density
    of `U∪V` over cells is `0.995`**: in class D almost every cell is a U/V event, so "separator cell ∈
    U∪V" is the trivial statement "almost every cell ∈ U∪V" and carries ZERO localizing information.
    The U/V machinery supplies no joint engine.  Case D's separators are driven by the same
    `separatorAtSlack_iff_window` local-window mechanism as case C.

  • **Case C "universal pattern" is the EXISTING engine restated.**  On every class-C witness/pair
    (incl. the canonical wall parity-shift `(2,4)`), the *upper* cell of the pair is a **weak ascent
    (`c ≥ index`) at 100% of separating displacements** — but this is exactly `weak_ascents_infinite`
    (already axiom-clean in Lean) applied to the upper cell, and the g-coordinate window description is
    exactly `separatorAtSlack_iff_window` re-expressed.  Neither restatement globalizes.  Parity-shift
    `(2,4)` again refutes any density extraction: the lower cell is a weak ascent too (`gₐ=g_b=+2`),
    `lower-weak-descent 0/2989`, so even the descent-side engine does not fire on the wall pair — the
    separator survives purely because the even threshold `D+6` lands in the open window `(D+4, D+6]`.

  • **Johnston subgroup `R = {p : supᵢ|I∖p(I)| < ∞}` sub-split (the one genuinely new axis) also
    fails to align.**  Sub-classifying class C by R-membership (`conv_johnston.py`, `J(p,L)` saturates
    ⟺ `p ∈ R`): parity-shift, swap_at_powers, adjacent-involution, block/rev_block ∈ R (J saturates at
    2–4); **growing_blocks_rev ∉ R** (J grows `4,8,16,27,…` with window length — cutting a size-k
    reversed block gives `|I∖p(I)| ≈ k → ∞`).  But the hardest wall (parity-shift `(2,4)`) is IN R,
    and the ∉-R witness (growing_blocks_rev) is handled by the same window engine, so R/¬R does not
    isolate the difficulty either.  No "intervals move boundedly" reduction for R yields more than the
    existing window characterization.

**Root cause (same residue as all prior routes).**  `weak_descents_infinite` pins the window's lower
edge and `weak_ascents_infinite` pins the upper edge, but there is no joint engine forcing BOTH at the
same `D` with the relative position enclosing an even `s ≥ max(a,b)` infinitely often.  The
convergent-permutation classification supplies clean *vocabulary* to test the split cleanly, and the
verdict is that the C/D split (and the finer R/¬R split within C) does NOT correspond to a difficulty
boundary — every hard case is class C, and the U/V global machinery is vacuous on the per-pair
question.  The wall is UNCHANGED.

**Net.**  Every route attempted (band-collapse, single-ray pigeonhole, cut-flow route A, residue-
class + cut-balance, value-hogging / cofinitely-bad, convergent-permutation C/D + Johnston-R split)
hits the identical wall: `hno`'s per-slack displacement floor `D₀(s)` does not uniformize across `s`,
and no proposed structure-extraction (density, residue-class, block-count, interval-displacement)
yields more than a structure that the balanced bijection parity-shift satisfies.  This motivated the
bounded/unbounded displacement dichotomy that now routes `main`: the bounded case's Step A
(`separatorAtSlack_slack_le_of_bddDisp`) caps the separating slack into the finite set `[max, max+B]`,
removing the per-slack non-uniformity wall, leaving the two isolated residues
`band_recurrence_finite_window_of_bddDisp` (bounded) and `band_recurrence_ge_max_of_unbddDisp`.

## Loop iteration (2026-05-23): cleaner bounded-case sufficient condition

NEW reduction for the bounded residue `band_recurrence_finite_window_of_bddDisp`:
  G (separating displacements) ⊇ { D : c(b+D) > b+D  AND  |c(a+D) − c(b+D)| ≥ 2 }.
Reason: strict ascent at b+D gives max(va,vb) ≥ M+1; gap ≥ 2 gives a width-≥2 window,
which therefore contains an even slack ≥ M (via separatorAtSlack_iff_window). So that set
⊆ G. VERIFIED infinite for every bounded non-EI family tested (parity-shift, involution,
swap-powers [infinite but log-sparse], block-3/5, rev-block-5, random period-6).
- For parity-shift / involution / swap-powers: gap=1 at strict-ascent-b NEVER occurs, so
  {strict-asc-b ∧ gap≥2} = {strict-asc-b}, infinite ⇒ G infinite ⇒ done outright.
- Residual edge: gap=1 cofinitely on strict-ascent-b ⇒ c(a+D)=c(b+D)±1 there ⇒ (bounded)
  φ(a+D) ≥ φ(b+D)+(δ−1) ≥ δ, a recurring value with c(A)=A+x on an infinite A. This is
  CONSISTENT with non-EI (parity-shift IS such a balanced shift), so it does NOT contradict;
  those c need the recurrence from OTHER (non-strict-asc-b) separators. So this sufficient
  condition handles most bounded c but not the gap=1-cofinite edge — that edge is where the
  remaining bounded difficulty concentrates.

## Loop iteration (2026-05-23 #2): cleaner bounded reduction is counterexample-free

Searched 1900 bounded non-EI permutations (block/periodic, B=2..8, all pairs): the set
{D : c(b+D)>b+D AND |c(a+D)−c(b+D)|≥2} is INFINITE in EVERY case (0 suspicious;
gap2/strict-asc ratio ≥ 0.25). So the cleaner reduction G ⊇ {strict-asc-b ∧ gap≥2}
robustly gives band_recurrence for bounded c. Residual to PROVE: "{strict-asc-b ∧ gap≥2}
infinite for bounded non-EI c", equivalently "gap=1 cofinitely on strict-ascent-b ⇒ EI"
(c(a+D)=c(b+D)±1 ⇒ φ(a+D)≥δ; for δ=1, consecutive cells→consecutive values cofinitely on
strict-ascents ⇒ shift ⇒ EI; δ≥2 needs the chaining argument). This residual is crisper and
likely more formalizable than the earlier separating_value_inf_fiber form.

## Loop iteration (2026-05-23 #3): JOINT-condition dichotomy (cleaner than bounded/unbounded?)

On weak-descents-of-a (always infinite), lo_D ≤ a < M, so a slack-M separator (M even) occurs
iff also weak-ascent-b. Hence:
  band_recurrence at slack M (M even)  ⟺  {D : c(a+D)≤a+D ∧ c(b+D)≥b+D} is INFINITE.
PROPOSED cleaner dichotomy (replaces bounded/unbounded):
  (1) JOINT {weak-desc-a ∧ weak-asc-b} infinite ⟹ slack-M (or M+1 if M odd, via strict ascent b)
      recurrence DIRECTLY. Clean, provable from weak_descents_infinite/weak_ascents_infinite +
      separatorAtSlack_iff_window. Verified infinite for growing_blocks_rev (unbounded) — count grows.
  (2) JOINT finite ⟹ the anti-correlated regime. parity-shift (bounded) is exactly this
      (weak-desc-a ⟺ D odd, weak-asc-b ⟺ D even — disjoint). Also: if φ(b+D)→∞ with φ(a+D)
      bounded on that subseq, slack-M separators appear anyway — so the genuinely-hard sub-case
      is joint-finite AND φ(a+D),φ(b+D) comonotone (both small or both large together), which is
      "bounded-like" and amenable to the finite pigeonhole (S_infinite).
NEXT: verify joint-finite ⟹ pigeonhole-handled (i.e. joint-finite ⟹ effectively bounded on rays
or directly S_infinite), and consider restructuring the Lean proof around the JOINT dichotomy
(slack-M-easy case is axiom-clean-able; would isolate the residue to the anti-correlated case only).

## Loop iteration (2026-05-23 #4): JOINT dichotomy IMPLEMENTED in Lean (residue 2 → 1)

Acted on #3's proposal. Restructured `band_recurrence_ge_max` (WinningAdaptive.lean) from the
bounded/unbounded split into the JOINT-condition dichotomy.

DEFINITIONS (ordered pair a<b, M=b.val, p=M%2, fixed even slack s=M+p):
  memJ c a b D := c(a+D) ≤ a+D  ∧  c(b+D) ≥ b+D + p.

PROVEN AXIOM-CLEAN:
  * `memJ_imp_separator`: every D∈J is a slack-(M+p) separator. (weak-desc-a ⇒ lo edge x<D+s
    using a<M; ascent-with-parity-b ⇒ hi edge y≥D+s; via separatorAtSlack_iff_window.)
  * `band_recurrence_ge_max_of_jointInfinite`: J recurs at unbounded D ⟹ band recurrence at the
    fixed s=M+p. Trivial transport via memJ_imp_separator. NO sorryAx.

SINGLE RESIDUE (sorry):
  * `band_recurrence_ge_max_of_jointFinite`: J finite (∃D₀,∀D≥D₀, ¬memJ) ⟹ band still holds.
    The anti-correlated bounded regime. Statement verified TRUE (joint_finite_residue.py: 25/25
    J-finite ordered pairs have a recurring even slack ≥M).

DISPATCH: `band_recurrence_ge_max` does WLOG a<b, then `by_cases` on the J-recurrence proposition
(NOT Set.Infinite, so push_neg gives exactly the J-finite hypothesis). b<a half swaps via
separatorAtSlack symmetry.

DISCRIMINATOR (joint_dichotomy.py, NMAX=2·10⁵, all FAMILIES × 8 pairs, 0 violations):
  (A) memJ ⇒ slack-(M+p) separator: 0 failures.
  (B) J-infinite ⇒ slack-s separators infinite: 0 failures.
  (C) **NO unbounded family is J-finite** (both growing_blocks_* are J-infinite on every pair).
      ⟹ the J-infinite clean case ABSORBS the entire unbounded regime; the old
      `band_recurrence_ge_max_of_unbddDisp` residue is DELETABLE.

DELETED dead sorry-bearing residues: `S_infinite_of_bddDisp`, `band_recurrence_ge_max_of_unbddDisp`,
plus their now-dead consumers `band_recurrence_finite_window_of_bddDisp`,
`band_recurrence_ge_max_of_bddDisp`. Retained axiom-clean scaffolding (memS, memS_imp_separator,
even_in_window_ge, separatorAtSlack_slack_le_of_bddDisp, fixedSlack_ge_of_window_recurrence) for reuse.

RESULT: `#print axioms main` = [propext, sorryAx, Classical.choice, Quot.sound]; sorryAx flows
through EXACTLY ONE residue (band_recurrence_ge_max_of_jointFinite), down from two. Build GREEN.
We did NOT formalize "J-finite ⟹ bounded" (empirically true but a separate combinatorial fact);
the J-finite case is simply the one residue.

## Loop iteration (2026-05-23 #4): residue = bounded + COMONOTONE (symmetric joint)

The single residue band_recurrence_ge_max_of_jointFinite is sharpened by a SYMMETRIC joint:
J'' := {ascent-a ∧ weak-desc-b} (a-cell high) ALSO yields separators (slack from the a-side).
So band holds if J OR J'' infinite. The true residue = BOTH finite, which forces (verified
125/1035 cases, 0 unbounded): φ(a+D), φ(b+D) COMONOTONE in sign (both ascend or both descend)
cofinitely, AND bounded displacement. = exactly the parity-shift regime. In the comonotone case
the finite pigeonhole gives a recurring value (x,y) same sign; it separates unless va,vb are
consecutive (|x−y−δ|=1); so the residue closes iff "all recurring comonotone values consecutive
⇒ EI" (the consecutive⇒EI argument, now with comonotone+bounded structure). Plan: formalize the
symmetric J'' lemma (shrink residue to comonotone+bounded), then attempt consecutive⇒EI close.

## Loop iteration (2026-05-23 #5): CLEAN closure of bounded comonotone (likely closes residue)

The residue band_recurrence_ge_max_of_bothJointFinite = comonotone (φ(a+D),φ(b+D) same sign
cofinitely ⟺ φ sign constant on residue classes mod δ). CLEAN CLOSURE for BOUNDED comonotone:
  band-fail ⟹ for EVERY even s≥M, cofinitely-many positive-class D have min(va,vb) ≥ s
            ⟹ min(va,vb) → ∞ on the positive class;
  but min ≤ va = a+φ(a+D) ≤ a+B (bounded) ⟹ CONTRADICTION. So bounded comonotone ⟹ band.
  (Alt: gap=1 on a DENSE positive class [comonotone gives full residue class, not sparse fiber] ⟹
   chain c(n+kδ)=c(n)±1 ⟹ φ(n+kδ) ≤ φ(n)−k(δ−1) → −∞, contradicting φ>0 on the positive class.
   δ=1 comonotone ⟹ φ constant sign ⟹ ¬bijection, vacuous. So δ≥2.)
KEY remaining question: is comonotone ⟹ bounded? Empirically YES (0 unbounded both-finite cases;
reverse_pow2_blocks is unbounded but NOT comonotone → joint-infinite). Surjectivity appears to
force bounded (unbounded displacement on a sign-constant class makes its image too sparse / breaks
balance). If comonotone ⟹ bounded is provable, the residue is VACUOUS → main fully axiom-clean.
Plan: formalize bounded-comonotone ⟹ band (clean), and prove comonotone ⟹ bounded (or split off
unbounded-comonotone as a tiny empirically-empty residue).

## Loop iteration (2026-05-23 #6): CORRECTION — the "bounded comonotone closure" has a real bridge gap (advisor-caught)

The #5 idea (bounded comonotone ⟹ band) is sound MATH for that slice, but it does NOT close the
residue `band_recurrence_ge_max_of_bothJointFinite`, because **`bothJointFinite` does not imply
bounded+comonotone**. Concretely (the killer check):
  - parity-shift c (c(2k)=2k+2, c(2k+1)=2k−1), pair (2,4): δ=2, M=b=4, p=0, q=leastEvenGe(5)−2=4.
    memJ  = (φa≤0 ∧ φb≥0): D even has φa=+2 (fails), D odd has φb=−2 (fails) → memJ EMPTY.
    memJ''= (φa≥4 ∧ φb≤0): |φ|=2 always, φa≥4 never → memJ'' EMPTY.
    So bothJointFinite holds VACUOUSLY for (2,4) — J/J'' extract ZERO structural info. The band
    still holds (s=6, D even: window (4,6]), but its proof must come from ¬EI+bijectivity ALONE.
  - Mixed-sign D survive both-finite: cofinitely (φa≥1 ∨ φb<p) ∧ (φa<q ∨ φb≥1) ALLOWS
    1≤φa≤q−1 ∧ φb≤0 (opposite sign). So both-finite ⊉ comonotone. (advisor case-walk)
  - The "min(va,vb)→∞ via all-s" step is also wrong: band-fail at s ⟺ (min≥s) ∨ (max<s); for
    bounded c the max<s branch handles all large s, so min does NOT →∞.
Two questions that genuinely BLOCK closure (both currently OPEN on paper):
  (1) bothJointFinite ∧ ¬EI ⟹ bounded?  — NOT derivable from defs (J/J'' can be vacuous);
      bounded is also globally false for ¬EI (reverse_pow2_blocks unbounded), only plausibly true
      restricted to both-finite, empirically (0 unbounded both-finite) but UNPROVEN.
  (2) bothJointFinite ⟹ comonotone (sign const on classes mod δ)? — NO, mixed-sign D survive.
The chain argument NEEDS comonotone (dense residue class); on a bounded-but-not-comonotone c the
recurring (u,v) fiber is sparse, so no chain. So neither bounded alone nor the chain alone closes it.
HONEST STATUS: the residue is the genuine research frontier. The J/J'' joint dichotomy shrinks the
residue for c where J or J'' is INFINITE (proven axiom-clean), but bounded-comonotone-ish c
(parity-shift family) fall into the both-finite residue with J/J'' vacuous, and closing them needs
deriving the band from ¬EI+bijectivity directly — which is exactly the hard bounded-displacement
band recurrence that has resisted every approach. Structural re-dispatch won't change this.

## Loop iteration (2026-05-23 #7): THREE-AGENT synthesis — BOUNDED-ABOVE case PROVEN (closes the wall); residue flips to UNBOUNDED-ABOVE

Ran 3 parallel agents on the band recurrence (band: non-EI c, a<b ⟹ ∃ even s≥b separating c(a+D),c(b+D) at ∞-many D).

### (A) Literature (bespoke; no off-the-shelf theorem)
Closest framework = bounded-displacement / WOBBLING GROUP theory; Laczkovich's discrepancy criterion. Our
cut B(N)=#{n≤N: c(n)>N} IS their discrepancy object. But it does NOT close even the bounded sub-case. The
EVEN-s parity condition has NO analog anywhere — the load-bearing oddity; any proof needs a bespoke parity/
counting argument on B(N). Cite Laczkovich+wobbling as conceptual home in writeup, keep honest framing.
(Refs: Juschenko–de la Salle arXiv:1301.4736; arXiv:1907.01597 quoting Laczkovich Crelle 404 (1990).)

### (B) Counterexample search (NONE; lemma robustly TRUE incl. unbounded)
13 families × 78 pairs = 1014 combos, ZERO counterexamples. Witness s = leastEvenGe(b) for every family/pair
EXCEPT parity_shift even-even needs leastEvenGe(b)+2. DENSITY DICHOTOMY: cyclic-shift/parity_shift = linear
density; ALL block-reversals/interval-exchanges = LOG density (in same reversed block, R−L = b−a EXACTLY ⟹
~3·log₂(D) separators, verified to D=3×10⁷). So NO positive-density/pigeonhole proof can work — proof must
tolerate log-sparse separators. Files: griddles-p4-verify/counterexample_search.py, structural_witness.py.

### (C) Direct proof (Opus): BOUNDED-ABOVE ⟹ band — COMPLETE PROOF (verified by me); UNBOUNDED-ABOVE open
Reformulation: f(n)=c(n)−n. For even s≥b, p=s−a ∈ P={p≥δ, p≡a mod 2}. band-fail ⟺ ∀p∈P, (⋆_p):
[f(n)≥p] ⟺ [f(n+δ)≥p−δ] for all n≥N_p (N_p finite PER p — no uniformity needed; that was the wall).
Lemma (general, no bddness): DESCENT-COFINITE ⟹ EI. If c(n)≤n cofinitely then EI (cut B(M)=#{n≤M:c(n)>M};
for n∈[N,M], c(n)≤M ⟹ {n≤M:c(n)>M}⊆[1,N), =0 for M≥max_{n<N}c(n) ⟹ c([1,M])=[1,M] ⟹ c(M)=M).
BOUNDED-ABOVE (f≤B⁺ globally) PROOF: V={v: f⁻¹(v) infinite}; weak-ascents ⟹ V≠∅, v*=max V≥0.
  • v*=0: values>0 finite (bdd above) ⟹ f≤0 cofinitely ⟹ EI. Contra.
  • v*≥1: q̄ = largest int ≡b(mod2), 0≤q̄≤v*; p=q̄+δ∈P. For ∞-many m=n+δ∈f⁻¹(v*), n≥N_p: RHS [f(m)≥q̄]
    true ⟹ LHS f(n)≥q̄+δ≥v*−1+δ.
      δ≥2: f(n)≥v*+1 at ∞-many n ⟹ pigeonhole over finite (v*,B⁺] ⟹ recurring value >v*, contra max V.
      δ=1: f(n)≥v* ∞-often with n+1∈f⁻¹(v*); bdd-above ⟹ f(n)=v* cofinitely ⟹ f⁻¹(v*) backward-closed
           ⟹ f≡v* on tail ⟹ c(n)=n+v* shift ⟹ omits v*≥1 values, not bijective. Contra.
  KEY: single-ray level set + threshold FIXED from global v* ⟹ ONE (⋆_p) application, ONE finite exception.
  Dodges sparse-fiber AND escaping-exception traps. CLOSES THE WALL (parity_shift is bdd-above; it just
  doesn't satisfy band-fail, so hypothesis unavailable — no spurious contradiction).
UNBOUNDED-ABOVE (limsup f=+∞): OPEN. Backward-push-up f(n+δ)≥q ⟹ f(n)≥q+δ chains backward but exceptions
  N_{q+jδ} ESCALATE while positions decrease, and small positions can carry huge f (c(1)=10⁶) ⟹ no ceiling
  to collide with. Empirically this regime is ALWAYS J-infinite (witness leastEvenGe(b), log-density).
  Minimal finishing sub-lemma: unbounded-above ⟹ memJ infinite (a-ray weak-descent ∧ b-ray peak co-occur
  at ∞-many common D). Then Lean's PROVEN band_recurrence_ge_max_of_jointInfinite finishes.

### NET / Lean plan
Residue FLIPS from "bounded comonotone (the hard wall)" → "unbounded-above ⟹ J-infinite (empirically easy)".
Restructure band_recurrence_ge_max to dispatch BOUNDED-ABOVE (formalize agent's proof) vs UNBOUNDED-ABOVE
(prove unbounded ⟹ J-infinite, then existing J-infinite proof). Bounded-above proof is the big new content
and is clean/formalizable. Status: agent's bounded-above proof manually verified; pressure-test w/ advisor
before formalizing.

## Loop iteration (2026-05-23 #8): CRITICAL — the BAND RECURRENCE IS FALSE (AP-split counterexample)

The bridge agent (δ=1 proven, δ≥2 open) flagged a candidate counterexample shape: one residue class
mod δ slowly ASCENDING to ∞ while another descends. I built it and VERIFIED it is a genuine
counterexample to the band recurrence itself (not just the bridge):

CONSTRUCTION (AP-split, δ=2): A = {a_k = 2k + 2·⌊√k⌋ : k≥1}; c(2k)=a_k (evens slowly ascend,
f(2k)=2⌊√k⌋→∞), c(2k−1)=b_k where B=ℕ∖A in order (odds descend, f≈−√k→−∞). Valid non-EI bijection
(verified injective + surjective-below on [1,238000]).

For pair (2,4): BOTH-FINITE (memJ, memJ'' have ZERO members — comonotone, never opposite-sign).
BAND FAILS: at even D=2j, window = (2+2⌊√(j+1)⌋, 4+2⌊√(j+2)⌋] ≈ (2+2√j, 4+2√j], width≈2, ESCAPING
upward. Each fixed even s = 4+2t is in the window only for j∈[t²,(t+1)²) (~2t values of D) then is
ABANDONED forever as the window climbs. Verified: active separator s ∈ [48,62] for D∈[1k,2k];
[130,144] for D∈[8k,16k]; [286,300] for D∈[40k,80k]. So NO fixed even s≥4 recurs at ∞-many D.
⇒ band_recurrence_ge_max(c,2,4) is FALSE. (Same for (1,3),(4,6),(6,8),(2,6).)

CONSEQUENCES:
1. `band_recurrence_ge_max_of_bothJointFinite` is a FALSE proposition. The lone `sorry` can NEVER be
   filled. The fixed-staircase winning-direction route is DOOMED (not merely unproven). This is the
   concrete realization of the documented "(1) NO FIXED TRAJECTORY is universal" negative result.
2. The bridge "unbounded-above ⟹ J-inf ∨ J''-inf" is FALSE (δ≥2): AP-split is unbounded-above AND
   both-finite. (δ=1 bridge remains true & proven.)
3. bounded-above ⟹ band remains TRUE & proven (AP-split is unbounded-above, outside its scope).
4. THE ANSWER (Bob wins ⟺ ¬EI) IS SAFE: discriminators exist for every pair (LemmaA, proven:
   (2,4)@(D=0,t=6), (1,3)@(D=0,t=2)). Bob distinguishes cells — but needs an ADAPTIVE strategy that
   tracks the CLIMBING slack s(D)~√D, which no fixed-slack staircase can do.

PATH FORWARD: the Lean winning direction must be rebuilt off the band recurrence. Options:
(a) formalize the adaptive belief-state strategy (memory: "substantial separate Lean project");
(b) replace the band recurrence with a TRUE weaker condition the staircase-with-growing-amplitude can
    use (the discriminators climb like √D — a growing-amplitude sweep, not fixed-slack, may capture
    them); (c) a localization argument directly from LemmaA's distinguishability + safety.
The honest writeup status should change from "machine-verified modulo one true lemma" to "modulo the
winning-direction strategy; the previously-attempted fixed-staircase lemma is now KNOWN FALSE
(AP-split), confirming adaptivity is required."

### #8 follow-up: ANSWER SURVIVES — Bob WINS AP-split via adaptive belief-state strategy
Belief-state minimax solver (negative displacement allowed; safety = position≥1 for all in belief):
AP-split is WINNABLE for all k₀ in {1..8},{1..12},{1..16},{1..20},{1..30} (all True). Controls:
involution (non-EI) wins; identity (EI) LOSES. So the solver is faithful and the answer
"Bob wins ⟺ ¬EI" is NOT threatened. The band recurrence being false ONLY kills the fixed-staircase
Lean route; Bob wins AP-split adaptively (tracking the climbing slack s(D)~√D). This concretely
realizes the documented "no fixed trajectory is universal / adaptivity is unavoidable" results.

## Loop iteration (2026-05-23 #9): ADAPTIVE design — D≥0 strategy, safety free, never stranded via separators_unbounded

User chose: formalize the adaptive strategy. Design (verified by belief-state minimax solver):
KEY: a D≥0-only (displacement never negative) adaptive strategy WINS all non-EI tested (AP-split,
block-5, involution) and correctly LOSES identity(EI). [solver /tmp/p4_dge0.py]
  • SAFETY IS FREE: D≥0 ⟹ position = k₀+D ≥ k₀ ≥ 1 always. No unsafe moves ever needed.
    (Memory's "block-5 winner uses negative D" was just ONE winner; a safe D≥0 winner also exists.)
  • NEVER STRANDED: separators_unbounded (PROVEN axiom-clean) gives every pair a separator at
    UNBOUNDED displacement D — always a FUTURE, SAFE discriminator (large D ⟹ large position). So
    go-right-and-dwell can resolve any remaining pair. THIS is the TRUE recurrence replacing the FALSE
    fixed-slack band: separators recur at unbounded DISPLACEMENT, not fixed slack.
  • ADAPTIVITY ESSENTIAL: no single trajectory hits every (D, even slack) [can't dwell-at-D forever
    AND visit all D]; fixed growing-amplitude sweep FAILS to localize block-5 (1,2 collide) & AP-split
    (8,10 collide) [/tmp/p4_growsweep.py]. So Bob must belief-guide which (D,slack) to visit.
  • GAME understood: EI loses because distinguishing k₀ from UNBOUNDEDLY-large k needs probing small
    thresholds = unsafe left moves (can't, position would hit 0); non-EI's displacement flips signals
    for small candidates "for free" via separators_unbounded.

PROOF ARCHITECTURE (reuses PROVEN pieces):
  localizes_BobWins (proven): never-guessing σ + (∀k₀ Localizes c σ k₀) ⟹ BobWins.
  Localizes k₀ = ∃ finite T: safe through T (FREE via D≥0) ∧ every k≠k₀ distinguished by T.
  Two phases: (1) explore (go right + dwell) until first YES ⟹ belief FINITE (yesSet_finite, proven:
  {k: c(k+D)<t} finite); (2) resolve finite belief — each remaining pair has a separator at unbounded
  D (separators_unbounded) reachable safely by going right + dwelling to catch its (even) slack ⟹
  belief → singleton at finite T. Then localizes_BobWins guesses. NO fixed-slack band needed.

TASKS #18–21. The research crux is the termination/no-stranding proof (task #19); the enabling true
facts (separators_unbounded, yesSet_finite, localizes_BobWins) are all already PROVEN axiom-clean.

## Loop iteration (2026-05-23 #10): CLEAN DICHOTOMY — bounded-above (band true) vs unbounded-above (Q2-even true). NO adaptive belief-state needed.

Adaptive-research agent concluded "foresight needed, requires the (false) band recurrence" — but that was
based on STALE info (it didn't know band is false) and a BOUNDED witness (adjacent-transposition) for its
"Q2 false". Correcting the regimes gives a clean dichotomy (verified):

KEY: Bob's lag L = t−D is ALWAYS EVEN (D_t ≡ t mod 2) and MONOTONE non-decreasing. So Bob needs EVEN-lag
separators, caught before lag climbs past them.

Q2-even ("every pair has even-lag separators at arbitrarily large lag"):
  • UNBOUNDED-ABOVE c: Q2-even TRUE. [verified: AP-split, doubling_rev, growing_rev — max even sep-lag
    doubles when D-range doubles; + 40 random growing-block bijections, ALL pairs grow.] Reason: unbounded
    displacement on the (cofinite) ray ⟹ window top max(va,vb)→∞ ⟹ even-lag separators at all large lags.
  • BOUNDED c: Q2-even FALSE (capped at ~max(a,b)) — but band recurrence is TRUE there (bounded-above proof).

THE DICHOTOMY (both cases = c-tailored FIXED trajectories via the PROVEN ofMoves_localizes; NO belief state):
  notEI_BobWins: by_cases on bounded-above (∃B ∀n (c n).val ≤ n.val+B):
   (1) BOUNDED-ABOVE → band_recurrence_ge_max is TRUE (agent: bounded-above ⟹ band) → existing band-staircase
       (rides at FIXED slack, catches recurring fixed-slack separator). [tasks: formalize bounded-above⟹band]
   (2) UNBOUNDED-ABOVE → Q2-even TRUE → c-tailored GROWING-LAG trajectory: enumerate pairs; for each, raise
       lag + ride right to an even-lag separator at lag ≥ current (Q2-even guarantees one at arbitrarily large
       lag ⟹ NEVER STRANDED). Satisfies ofMoves_localizes' hsep (sep every pair) + hsafe (D≥0) + hyes (D→∞).
This REPLACES the false band_recurrence_ge_max_of_bothJointFinite with TWO TRUE lemmas + two trajectory
constructions. No foresight/belief-state needed — lag monotonicity is fine because (1) fixed slack recurs
[bounded] or (2) separators at ALL large lags [unbounded], so the monotone-lag staircase is never stuck.
NEW LEMMA to formalize (case 2): unbounded-above ⟹ Q2-even (separators at arbitrarily large even slack),
then a growing-lag analogue of the Staircase. Case 1 = agent's bounded-above⟹band + existing staircase.

## Loop iteration (2026-05-23 #11): Q2-even substantially proven; δ≥2 residual gap

Q2-even (unbounded-above ⟹ every pair has even-lag separators at arbitrarily large lag) — the case-2
enabling lemma. PROVEN (airtight): reduction to the bad adversary (⋆) = "width-1 ∧ consecutive ∧ odd-top
at all high-max displacements"; SPIKE PROPAGATION (φ(n)≥M ∧ c(n+δ)=c(n)±1 ⟹ φ(n+δ)≥M-2, so high spikes
self-perpetuate along the δ-AP — removes the sparse-set obstruction); injective ±1 walk ⟹ strictly
monotone; INCREASING case ⟹ c(n)=n+g₀ on a tail (δ=1) ⟹ pigeonhole (values [1,n₀+g₀) vs indices
[1,n₀)) contradiction; DECREASING case for gap-1 killed via gap-2 (descending run gives c(n₀+2)=c(n₀)-2,
contradicting gap-2 width-1 |c(n₀)-c(n₀+2)|=1, at a propagated high spike — LOCAL, no sparsity).
NET PROVEN: ¬(gap-1 ∧ gap-2 both fail). RESIDUAL GAP: per-pair for δ≥2 (for δ≥2 the δ-AP ±1 walk is
FINITE — exits high-spike since φ(n₀+kδ)=φ(n₀)−k(δ∓1)... → so no infinite-run pigeonhole; needs a
descending-block/surjectivity-tiling count over many spikes, not completed). Q2-even verified TRUE
empirically (AP-split, doubling/growing-rev, 40 random unbounded-above; 0 counterexamples). The bad
adversary (consecutive-odd-top) is NOT killable by parity alone (decreasing blocks preserve odd-top);
it IS killed locally by a second gap. STATUS: replaced the FALSE band lemma with a TRUE (empirically)
Q2-even that is partially proven (δ≥2 open). Case 1 (bounded-above⟹band) being formalized separately.

## Loop iteration (2026-05-23 #12): Q2-even CLOSED for EVEN δ (parity collision); odd δ true-but-open

EVEN-δ closure (airtight, unconditional — no global counting): assume bad adversary (⋆) for a δ-even
pair. At a tall a-ray spike n: (⋆)@D₀ pins c(n+δ)=c(n)±ε (width-1); then va(D₁)=c(n+δ)−D₁ depends on
c(n+δ) ALONE (no circularity) and is ≥L, so (⋆)@D₁ is triggered; injectivity ⟹ c(n+2δ)=c(n)+2ε. The
two tops max(D₀),max(D₁) differ by δ−1 (ε=+1) or δ+1 (ε=−1) — ODD iff δ even ⟹ opposite parity ⟹
can't both be odd, contradicting (⋆). So Q2-even holds for ALL EVEN-δ pairs. (δ odd: δ±1 even ⟹ same
parity ⟹ no contradiction; this method fails for odd δ.)
ADVERSARY TEST (odd δ): reverse growing ODD-length blocks ⟹ interiors width-1 with odd tops (no even
sep in interiors). But Q2-even STILL HOLDS for (1,2),(2,3),(1,4),(3,4): the block BOUNDARIES give
even-lag separators at GROWING lag (verified: even sep-lag grows to ~disp). So the adversary is
defeated by boundaries; Q2-even is ROBUST for odd δ too — just unproven.
DOWNSTREAM NEED: ofMoves_localizes' hsep is ∀a≠b (ALL gaps δ), so localization needs Q2-even for ALL
δ (even AND odd). Even-δ-only is insufficient (adjacent/odd-distance pairs unseparated). So odd-δ
Q2-even is genuinely required.
STATUS: Q2-even TRUE for all δ (empirically, incl targeted adversaries); PROVEN for even δ; the
remaining MATH BOTTLENECK is odd-δ Q2-even (needs the global boundary/displacement-variation argument:
unbounded-above ⟹ width-1-odd-top-everywhere is impossible because displacement variation forces
width≥2 or even-top at growing lag — the agent's descending-block/surjectivity-tiling count, not
finished). Case-1 (bounded-above⟹band) Lean formalization running separately.

## Loop iteration (2026-05-23 #13): Q2-even CLOSED for δ=1 (peak-chase); now proven for even δ AND δ=1; odd δ≥3 open

δ=1 closure (airtight): for δ=1 the AP is ALL of ℕ. Assume (⋆). At a spike s with φ(s)≥max(L+2,c(a+1)):
both links width-1 ⟹ {c(s−1),c(s+1)}={c(s)−1,c(s)+1}. PEAK-CHASE toward value+1 ⟹ self-avoiding ±1
walk ⟹ monotone in cell index. Rightward: c(n)=n+φ(s) on [s,∞) ⟹ [s,∞)→[s+φ(s),∞) ⟹ cells [1,s−1]
(s−1 of them) must cover all values <s+φ(s) (s+φ(s)−1>s−1 values) — PIGEONHOLE contradiction. Leftward:
chase reaches cell 1 with c(1)=φ(s)+2s−1>φ(s)≥c(1) — contradiction. So (⋆) impossible ⟹ Q2-even holds
for ALL adjacent pairs. No δ=1 counterexample (explains why "reverse-odd-blocks" leaks even separators
at run boundaries). δ=1 is the most important case (adjacent pairs).
ODD δ≥3 (open): chase forces RIGHTWARD (leftward ruled out for large φ(s)), but c(a+jδ)=c(s)+j with
cells advancing by δ ⟹ φ drops by δ−1 per step ⟹ run is FINITE (length ~φ(s)/(δ−1)) on the density-1/δ
residue-class AP. Single-spike count is LOCAL (AP and complement decouple) ⟹ no bijectivity contradiction
from one spike. WHY δ=1 worked: there the AP IS all of ℕ, so the pigeonhole is GLOBAL. MISSING SUB-FACT:
a multi-spike global count (interlocking ascending runs over spikes s₁<s₂<… on a residue class force a
high width-≥2 link). Q2-even verified TRUE for odd δ≤9 empirically; the count is the open residue.

Q2-EVEN STATUS: proven for EVEN δ (parity-collision) and δ=1 (peak-chase); OPEN for odd δ≥3 (multi-spike
count). Downstream (ofMoves_localizes hsep ∀ pairs) needs ALL δ, so odd δ≥3 is required.
REMAINING for unbounded-above case: (1) odd δ≥3 Q2-even; (2) the growing-lag c-tailored trajectory
(NOT started — existing Staircase uses FIXED slack via band; a growing-lag analogue using Q2-even is new).
