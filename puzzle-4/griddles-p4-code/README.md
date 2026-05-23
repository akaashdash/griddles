# Trolley Retrieval (Puzzle 4) — code

Empirical verification of the solution to Puzzle 4.

**Answer.** Bob has a winning strategy **iff** the labelling permutation `c` is *not*
eventually the identity (i.e. `c(n) ≠ n` for infinitely many `n`).

The **authoritative** proof is the machine-checked Lean 4 development in
[`../griddles-p4-lean`](../griddles-p4-lean): `theorem main : BobWins c ↔ ¬ EventuallyIdentity c`
is fully `sorry`-free and axiom-clean (`#print axioms main = [propext, Classical.choice, Quot.sound]`).

This folder holds a single self-verifying script that reproduces the **empirical** facts behind
that proof.

## Run

```bash
uv run main.py
```

It runs three checks and prints `ALL CHECKS PASSED`:

1. **Answer.** A belief-state (minimax) solver wins from every start cell for a battery of
   non-eventually-identity permutations, and provably cannot for the identity (eventually
   identity ⇒ Bob loses). The winner uses only displacement `D ≥ 0`, so safety (never falling
   to position `≤ 0`) is automatic — matching the Lean construction.
2. **The band recurrence is false.** A single fixed "lag" does *not* suffice: for the
   `ap_split` permutation the separating lag climbs (~`√D`), so no fixed even lag recurs. This
   is exactly why the proof splits into a bounded-above / unbounded-above dichotomy rather than
   using one band lemma.
3. **Q2-even.** For unbounded-above permutations every pair nonetheless has separators at
   *arbitrarily large even lag* (the enabling fact `q2even` for the unbounded-above case); for
   bounded-above permutations the lag is capped.

## The game

An invisible trolley starts at an unknown cell `k₀ ≥ 1`. At each time `t = 1, 2, …` Bob pushes
the trolley one cell left/right to position `k_t = k₀ + D_t` (`D_t` = net displacement); if
`k_t ≤ 0` Bob loses; otherwise the trolley emits the bit `[c(k_t) < t]`. Bob may instead guess
the trolley's current cell; a correct guess wins. Bob sees only the signal history, not `k₀`.

## Note

The historical development of the proof (including an attempted "band recurrence" lemma that
turned out **false**, and the bounded/unbounded-above dichotomy that replaced it) is documented
in [`../notes.md`](../notes.md). The earlier exploratory verification scripts have been
consolidated into `main.py`.
