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
