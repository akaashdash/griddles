-- Root of the GriddlesP4Lean library.
-- Submodules (in dependency order):
--   Defs                — permutations, strategies, game semantics, win condition
--   Parity              — parity invariant D_t ≡ t (mod 2)
--   Losing              — eventually-identity permutations: Bob has no winning strategy
--   RestrictedSeparation — the single remaining lemma (winning-direction crux), as a `sorry`
--   WinningRestricted   — complete BobWins for the locally-decodable class (axiom-clean)
--   WinningGeneral      — general winning direction (monotone-right strategy), rests on
--                         RestrictedSeparation only
--   Answer              — main theorem: Bob wins ↔ c is not eventually identity
--   WinningKProbe       — K=3 probe winning theorem for locally 3-decodable permutations
--   LemmaA              — (superseded exploration) abstract characterization of the
--                         `Indistinguishable` relation; its `odd_good_pair_gap` is the same
--                         research-level content as RestrictedSeparation. Off the main path.
import GriddlesP4Lean.Defs
import GriddlesP4Lean.Parity
import GriddlesP4Lean.Losing
import GriddlesP4Lean.RestrictedSeparation
import GriddlesP4Lean.WinningRestricted
import GriddlesP4Lean.WinningGeneral
import GriddlesP4Lean.Answer
import GriddlesP4Lean.WinningKProbe
import GriddlesP4Lean.LemmaA
