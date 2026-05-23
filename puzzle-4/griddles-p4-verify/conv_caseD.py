"""Build a genuine class-D (t -> infinity) non-EI permutation and test whether
separators at a FIXED even slack >= max(a,b) recur at unbounded displacement,
and whether they connect to U/V (block-count-change) events.

A standard class-D construction (Witula 7.1(v)): pick an increasing sequence x_n
with bounded gaps but p(x_{n+1})-p(x_n) -> infinity.  Concretely we use the
"interleave growing forward/backward runs" idea but realise it as a genuine
permutation of a prefix via blocks whose IMAGES are spread far apart.

Cleanest genuine class-D bijection: the "sqrt-block scatter".  Tile N+ into blocks
B_0,B_1,... of growing size; map block B_k to a target window placed so that the
images of successive blocks are far apart, forcing the running image to have
~k separated intervals.  We instead use a simpler, provably class-D, EASILY
bijective construction: the "triangular transpose" / pairing that opens a new
interval every few steps.

We use: c swaps the two halves of each block of size 2m with a gap pattern... too fiddly.
Instead use the cleanest: c(n) defined by writing n in the "block" tiling of sizes
1,2,3,... and mapping position to a strided layout. We build it concretely on a prefix
and CHECK it is a permutation, CHECK t->inf, CHECK non-EI.
"""

from convergence import UV_sets, t_sequence
from families import make_perm_from_list


def class_d_scatter(NMAX):
    """Genuine class-D permutation on a prefix.

    Construction: process blocks of growing size s=1,2,3,...; the k-th block occupies
    input positions; we assign its outputs by INTERLEAVING into already-placed gaps so
    that the image p([1,n]) keeps splitting into more intervals.

    Concrete realisation that is easy to verify: the "odd-then-even within doubling
    windows" reversal at growing scale. We just take a permutation whose image of
    [1,n] provably has many msi: map n -> position under bit-reversal-like scatter.

    Simplest robust class-D: c = "stride permutation" of each doubling window
    [2^k, 2^{k+1}) reading it in a 2-interleaved order. Within window W_k of size
    L=2^k, send the first half and second half alternately -> image of a prefix that
    cuts W_k into ~L/2 singletons => t grows like 2^{k-1}. That's strongly class D.
    """
    vals = [0] * NMAX
    # window [start, start+L-1], L = current size (powers of two), interleave
    start = 1
    L = 1
    while start <= NMAX:
        end = min(start + L - 1, NMAX)
        idxs = list(range(start, end + 1))
        sz = len(idxs)
        # interleave: outputs go to positions start, start+2, start+4, ... then start+1, start+3,...
        # i.e. c maps idxs[j] to the j-th element of the interleaved order of the SAME window range.
        targets = list(range(start, end + 1))
        inter = targets[0::2] + targets[1::2]  # even offsets then odd offsets
        for j, src in enumerate(idxs):
            vals[src - 1] = inter[j]
        start = end + 1
        L *= 2
    # vals is a permutation of 1..NMAX (each window permuted within itself)
    return make_perm_from_list(vals)


def disp(c, n):
    return c(n) - n


def separator_at_slack(c, a, b, s, D):
    """[c(a+D) < D+s] != [c(b+D) < D+s]."""
    return (c(a + D) < D + s) != (c(b + D) < D + s)


def least_even_ge(m):
    return m if m % 2 == 0 else m + 1


def main():
    NMAX = 4096
    c, cinv, nmax = class_d_scatter(NMAX)
    eff = nmax - 1
    tseq = t_sequence(c, eff)
    U, Vs = UV_sets(tseq)
    print("=== class_d_scatter classification ===")
    print(f"  N={eff}  t_min={min(tseq)}  t_max={max(tseq)}  t_at_end={tseq[-1]}")
    q1 = max(tseq[: eff // 4])
    q4 = max(tseq[3 * eff // 4 :])
    print(f"  q1_max={q1}  q4_max={q4}  -> class {'D' if q4 > q1 + 1 else 'C'}")
    print(f"  |U|={len(U)}  |V|={len(Vs)}")
    # non-EI check: are there infinitely many (lots of) non-fixed points in the tail?
    nf_tail = [n for n in range(eff // 2, eff) if c(n) != n]
    print(
        f"  non-fixed points in tail [{eff // 2},{eff}): {len(nf_tail)}  (non-EI if >0)"
    )

    print("\n=== Case D: fixed-slack separator recurrence for several pairs ===")
    pairs = [(1, 2), (2, 4), (3, 7), (1, 4), (5, 8)]
    Dmax = eff - 20
    for a, b in pairs:
        mx = max(a, b)
        # for each even slack s in [leastEvenGe(mx), leastEvenGe(mx)+ window], count separating D
        found = None
        for s in range(least_even_ge(mx), least_even_ge(mx) + 12, 2):
            Ds = [
                D
                for D in range(1, Dmax)
                if a + D <= eff and b + D <= eff and separator_at_slack(c, a, b, s, D)
            ]
            # "recurs at unbounded D": separators appear in the last quarter too
            late = [D for D in Ds if D > 3 * Dmax // 4]
            if late:
                found = (s, len(Ds), len(late), late[:5])
                break
        if found:
            s, tot, nlate, sample = found
            print(
                f"  pair ({a},{b}): recurring even slack s={s} (excess {s - mx}); "
                f"#sep={tot}, #late={nlate}, sampleD={sample}"
            )
        else:
            print(
                f"  pair ({a},{b}): NO recurring even slack found in window  *** OBSTRUCTION ***"
            )


if __name__ == "__main__":
    main()
