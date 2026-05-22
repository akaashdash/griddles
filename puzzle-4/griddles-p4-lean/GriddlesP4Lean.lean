-- Root of the GriddlesP4Lean library.
-- Submodules (in dependency order):
--   Defs     — permutations, strategies, game semantics, win condition
--   Parity   — parity invariant D_t ≡ t (mod 2)
--   Losing   — eventually-identity permutations: Bob has no winning strategy
--   LemmaA   — characterization of indistinguishable pairs
--   Winning  — non-eventually-identity: Phase 1 + Phase 2 construction
--   Answer   — main theorem: Bob wins ↔ c is not eventually identity
--   WinningKProbe — K=3 probe winning theorem for locally 3-decodable permutations
import GriddlesP4Lean.Defs
import GriddlesP4Lean.Parity
import GriddlesP4Lean.Losing
import GriddlesP4Lean.LemmaA
import GriddlesP4Lean.Winning
import GriddlesP4Lean.Answer
import GriddlesP4Lean.WinningKProbe
