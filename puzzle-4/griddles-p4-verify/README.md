# Verification scripts for `noSeparator_allSlack_imp_eventuallyIdentity`

These back the empirical claims in the doc-comment of the lone remaining `sorry` in
`griddles-p4-lean/GriddlesP4Lean/WinningAdaptive.lean`
(`noSeparator_allSlack_imp_eventuallyIdentity`, a.k.a. `band_recurrence_ge_max`).

Run any script with `uv run --no-project <script>.py` from this directory.

## The lemma (slack form)

Fix a bijection `c` of ℕ⁺ and `a < b` (so `max(a,b)=b`). A **slack-`s` separator at displacement
`D`** holds iff `[c(a+D) < D+s] ≠ [c(b+D) < D+s]`. The lemma:

> If for **every even `s ≥ b`** the slack-`s` separators are eventually absent
> (`∃D₀ ∀D≥D₀ ¬sep`), then `c` is eventually identity.

Equivalent **contrapositive (band recurrence)**: non-EI `c` ⇒ some even `s ≥ b` has separators at
unboundedly many `D`.

## Scripts

- `families.py` — the test bijections (block/reverse-block cycles, adjacent-transposition
  involution, parity-shift `c(2k)=2k+2,c(2k+1)=2k−1`, `swap_at_powers`, growing-block families
  with unbounded `g`, random periodic). Imported by the others.
- `verify.py` — lemma truth: every non-EI family/pair has a recurring even slack ≥ max (0 failures);
  identity has none for opposite-parity pairs (Bob can't distinguish — correct).
- `wd_probe.py` / `wa_probe.py` — windows at weak descents of `a` / weak ascents of `b`. Shows the
  single-ray pigeonhole fails on `growing_blocks_rev` (window unbounded along any one ray).
- `endpoint_probe.py` — per-even-slack recurrence; canonical witness `leastEvenGe(b)` recurs for
  most perms, but `parity_shift (2,4)` needs `leastEvenGe(b)+2 = 6` (`4` recurs 0 times).
- `cut_probe.py` — cut identity `ψ(N)=|{n≤N:c(n)>N}|=|{n>N:c(n)≤N}|` holds, BUT `ψ(N)→∞` for
  `growing_blocks_rev` (non-EI). So the "ψ bounded ⇒ EI" route-A finish is false.
- `final_probe.py` — recurring-slack excess over `leastEvenGe(b)` across 400 random block-bijections:
  uniformly 0 (so the +2 case is special to structured perms like parity-shift). No single formula
  for the witness ⇒ the `∃ s` is unavoidable.

## Headline result

Lemma is **TRUE** (0 counterexamples over 600+ family/pair combos incl. 400 random bijections).
All three proposed proof routes (band-collapse STEP 1; single-ray pigeonhole; cut/flow route A) are
each **empirically broken** on a concrete tested family — see the ATTEMPT LOG in the Lean
doc-comment. The combinatorial residue is genuine and remains open.
