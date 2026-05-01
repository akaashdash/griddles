# Proof Plan: equiv_fixed180 and equiv_fixed90

## Math recap

For n = 2m+1 (odd), m = (n-1)/2:

### 180°-fixed proper colorings
- f(r,c) = base + R(c) + D(r), with R(0)=D(0)=0
- FixedBy180: f(r,c) = f(n-1-r, n-1-c)  ⟹  h_j = -h_{n-2-j}  and  v_k = -v_{n-2-k}
- Free parameters: base (3 choices), h_0,...,h_{m-1} (each ∈ NZMod3), v_0,...,v_{m-1}
- Count: 3 × 2^m × 2^m = 3 × 2^(n-1)

### 90°-fixed proper colorings
- f(r,c) = f(n-1-c, r)  ⟹  D(r)=R(r) (i.e. v_k=h_k) AND h_j = -h_{n-2-j}
- Free parameters: base, h_0,...,h_{m-1}
- Count: 3 × 2^m = 3 × 2^((n-1)/2)

## Extended slope construction (for 180°)

Given hs : Fin m → NZMod3, define the full n-1 slopes:
  ext_h hs j = hs(j)         if j < m
  ext_h hs j = -(hs(n-2-j))  if j ≥ m  (note: n-2-j = 2m-1-j < m when j ≥ m)

Key property: ext_h hs j + ext_h hs (n-2-j) = 0  for all j  [anti-palindrome]
Key property: ext_h hs j ≠ 0  for all j  [from NZMod3 and neg_ne_zero]

R hs c = Σ_{j < c.val} ext_h hs j  (accumulation)
Palindrome: R hs c = R hs (n-1-c)  [proved below]

Proof of palindrome (c ≤ m):
  R(n-1-c) = Σ_{j<m} hs(j) + Σ_{j=m}^{n-2-c} (-hs(n-2-j))
  sub k = n-2-j: = Σ_{j<m} hs(j) - Σ_{k=c}^{m-1} hs(k)
                = Σ_{k<c} hs(k) = R(c)  ✓

## Forward map (toFun)
Given ⟨f, hAdj, hRich, hFixed⟩:
  base = f(0,0)
  hs(j) = ⟨f(0, j+1) - f(0, j), proof_ne_zero⟩   for j : Fin m
  vs(k) = ⟨f(k+1, 0) - f(k, 0), proof_ne_zero⟩   for k : Fin m
proof_ne_zero: from hAdj.1 (or .2), since f(0,j) ≠ f(0,j+1) ↔ diff ≠ 0

## Backward map (invFun)
Given (base, hs, vs):
  f(r,c) = base + R hs c + D vs r
  AdjOk:    f(r,c+1) - f(r,c) = ext_h hs c ≠ 0  [ext_h nonzero]
            f(r+1,c) - f(r,c) = ext_v vs r ≠ 0
  RichOk:   decide-provable given h≠0, v≠0 (richness_from_slopes)
  FixedBy180: f(r,c) = base + R(c) + D(r) = base + R(n-1-c) + D(n-1-r) = f(n-1-r, n-1-c)
              [uses palindrome of R and D]

## left_inv (invFun ∘ toFun = id)
Given ⟨f, ...⟩, invFun(toFun ⟨f,...⟩) should equal f.
  invFun gives g(r,c) = f(0,0) + R'(c) + D'(r)
  where R'(c) = Σ_{j<c} ext_h (slopes of f) j
  Need: R'(c) = f(0,c) - f(0,0)  and  D'(r) = f(r,0) - f(0,0)
  
  R'(c) = Σ_{j<c} (f(0,j+1) - f(0,j))  [telescoping = f(0,c) - f(0,0)]
  This is Finset.sum_range_sub (or just induction).

## right_inv (toFun ∘ invFun = id)
Given (base, hs, vs), toFun(invFun(base, hs, vs)) should equal (base, hs, vs).
  g(r,c) = base + R hs c + D vs r
  base' = g(0,0) = base + R hs 0 + D vs 0 = base + 0 + 0 = base  ✓
  hs'(j) = g(0,j+1) - g(0,j) = R hs (j+1) - R hs j = ext_h hs j = hs(j)  ✓
  [need: R(j+1) - R(j) = ext_h hs j, which is Finset.sum_range_succ]

## equiv_fixed90 structure
Same as 180° but invFun takes (base, hs) and uses ext_v = ext_h (same slopes).
FixedBy90 condition: f(r,c) = f(n-1-c, r)
  base + R(c) + D(r) = base + R(r) + D(n-1-c)
  Need: R = D  and  R palindromic (same as 180°)
  Since D = R, both follow from the 90° construction.

## Key Mathlib lemmas needed
- Finset.sum_range_succ: Σ_{j<k+1} f(j) = Σ_{j<k} f(j) + f(k)
- Finset.sum_range_zero: Σ_{j<0} f(j) = 0
- sub_ne_zero: a - b ≠ 0 ↔ a ≠ b
- neg_ne_zero: -a ≠ 0 ↔ a ≠ 0

## Implementation order
1. [DONE] Lemma: richness_from_slopes (by decide)
2. ext_h nonzero: ext_h hs j ≠ 0 for all j
3. Palindrome: R hs c = R hs (n-1-c) (split at m, telescope)
4. invFun constructs proper coloring (AdjOk + RichOk)
5. invFun gives FixedBy180
6. left_inv: telescoping sum
7. right_inv: Finset.sum_range_succ
8. Assemble equiv_fixed180
9. equiv_fixed90 (similar but simpler)

## Current errors (to fix)
1. Lines 323,327: omega can't prove `j.val + 1 < n` — hm not visible in by block.
   Fix: use `by have := j.isLt; have := hm; omega`
2. Lines 361,368: right_inv ring goals — after `simp [ext_slope, dif_pos, Fin.eta]`, ring
   doesn't close because `hs ⟨j.val, j.isLt⟩ ≠ hs j` to ring. Need `simp [Fin.eta]` BEFORE ring.
3. Line 389: card_fixed180_odd fails because equiv_fixed180 fails (cascading).
4. mkCumSum_succ: Fin.sum_univ_castSucc may leave proof-term mismatch goals.

## Current status
- equiv_fixed180: structure in place, many sorrys (RichOk, left_inv, palindrome)
- equiv_fixed90: sorry
- card_fixed180_odd: depends on equiv_fixed180
- card_fixed90_odd: depends on equiv_fixed90
