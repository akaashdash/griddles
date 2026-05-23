-- Root of the GriddlesP4Lean library.
-- Submodules (in dependency order):
--   Defs              — permutations, strategies, game semantics, win condition
--   Parity            — parity invariant D_t ≡ t (mod 2)
--   Losing            — eventually-identity permutations: Bob has no winning strategy  (PROVEN)
--   LemmaA            — characterization of indistinguishable pairs (the CORRECT winning-direction
--                       lemma; captures all reachable discriminators incl. early wakes). Its
--                       Δ≥2 case `odd_good_pair_gap` is the open research-level crux.
--   WinningRestricted — complete BobWins for the locally-2-decodable class (axiom-clean)
--   WinningKProbe     — complete BobWins for the locally-3-decodable class (axiom-clean)
--   WinningKProbeGen  — complete BobWins for the locally-K-decodable class, arbitrary K (axiom-clean)
--   Answer            — main theorem: Bob wins ↔ c not eventually identity (winning dir OPEN; the
--                       precise obstacle — no fixed-K sweep covers all non-EI c, block-5 witness —
--                       is documented at the `sorry`)
--
-- NOTE: RestrictedSeparation.lean / WinningGeneral.lean (the "monotone-right" route) were
-- DELETED — `restricted_separation` was FALSE (blkPerm counterexample: rightward probes miss
-- early-wake discriminators). The winning direction is back to the abstract-LemmaA route.
import GriddlesP4Lean.Defs
import GriddlesP4Lean.Parity
import GriddlesP4Lean.BoundedAbove
import GriddlesP4Lean.Losing
import GriddlesP4Lean.LemmaA
import GriddlesP4Lean.WinningRestricted
import GriddlesP4Lean.WinningKProbe
import GriddlesP4Lean.WinningKProbeGen
import GriddlesP4Lean.Answer
import GriddlesP4Lean.WinningAdaptive
import GriddlesP4Lean.BandBoundedAbove
import GriddlesP4Lean.Q2Even
import GriddlesP4Lean.GrowStair
