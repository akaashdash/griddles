"""Two targeted probes:

(B) Case D: do the recurring separators coincide with U(p)/V(p) (block-count-change)
    events on the rays {a+D},{b+D}?  If yes => per-pair<->global bridge for case D.
    If no => U/V framework adds no leverage; case D is same mechanism as case C.

(A) Case C: displacement profiles on the rays for the canonical wall parity_shift (2,4)
    and the other class-C witnesses; test the WINDOW-EDGE discriminator:
      separator at slack s* at D  <=>  min(c(a+D),c(b+D)) < D+s* <= max(c(a+D),c(b+D))
    and specifically whether the recurring D's are exactly the D where the LOWER cell is a
    weak descent (c <= index) AND the UPPER cell sits >= D+s*  (i.e. a weak ascent reaching
    the threshold).  The open question: are these two events simultaneous infinitely often?
"""

from conv_caseD import class_d_scatter, least_even_ge, separator_at_slack
from convergence import UV_sets, t_sequence
from families import growing_blocks, parity_shift, swap_at_powers


def probe_caseD_bridge():
    print("=== (B) Case-D per-pair <-> global U/V bridge ===")
    NMAX = 4096
    c, cinv, nmax = class_d_scatter(NMAX)
    eff = nmax - 1
    tseq = t_sequence(c, eff)
    U, Vs = UV_sets(tseq)
    Uset, Vset = set(U), set(Vs)
    pairs = [(2, 4), (3, 7), (5, 8)]
    Dmax = eff - 20
    for a, b in pairs:
        mx = max(a, b)
        s = least_even_ge(mx)
        # try slacks until we find recurring
        for s in range(least_even_ge(mx), least_even_ge(mx) + 12, 2):
            Ds = [
                D
                for D in range(1, Dmax)
                if a + D <= eff and b + D <= eff and separator_at_slack(c, a, b, s, D)
            ]
            if Ds and Ds[-1] > 3 * Dmax // 4:
                break
        # For these separating D, is a+D or b+D in U or V?  Or is c(a+D) / c(b+D) in U/V (value side)?
        in_uv_cell = 0
        in_uv_val = 0
        for D in Ds:
            if a + D in Uset or a + D in Vset or b + D in Uset or b + D in Vset:
                in_uv_cell += 1
            if (
                c(a + D) in Uset
                or c(a + D) in Vset
                or c(b + D) in Uset
                or c(b + D) in Vset
            ):
                in_uv_val += 1
        n = len(Ds)
        print(
            f"  pair ({a},{b}) s={s}: #sep={n}; "
            f"cell a+D/b+D in U/V: {in_uv_cell}/{n}; value c(.) in U/V: {in_uv_val}/{n}"
        )
        # baseline: how often is a RANDOM cell in U union V?
    base = (len(U) + len(Vs)) / eff
    print(f"  (baseline density of U∪V over cells: {base:.3f})")


def probe_caseC_window(name, c, eff, pairs):
    print(f"\n--- class C witness: {name} (eff={eff}) ---")
    for a, b in pairs:
        mx = max(a, b)
        # find recurring even slack >= mx
        chosen = None
        Dmax = eff - 20
        for s in range(least_even_ge(mx), least_even_ge(mx) + 16, 2):
            Ds = [
                D
                for D in range(1, Dmax)
                if a + D <= eff and b + D <= eff and separator_at_slack(c, a, b, s, D)
            ]
            if Ds and Ds[-1] > 3 * Dmax // 4:
                chosen = (s, Ds)
                break
        if not chosen:
            print(f"  pair ({a},{b}): NO recurring slack found (window) *** check ***")
            continue
        s, Ds = chosen
        # On the separating D's: examine the lower/upper cells.
        # lower cell = the one with smaller c-value; check if it's a weak descent (c<=idx)
        lower_wd = 0  # lower cell is weak descent
        upper_wa = 0  # upper cell is weak ascent (c>=idx)
        both = 0
        sampleD = Ds[-3:]
        for D in Ds:
            ca, cb = c(a + D), c(b + D)
            ia, ib = a + D, b + D
            if ca <= cb:
                lo_idx, lo_val, hi_idx, hi_val = ia, ca, ib, cb
            else:
                lo_idx, lo_val, hi_idx, hi_val = ib, cb, ia, ca
            wd = lo_val <= lo_idx
            wa = hi_val >= hi_idx
            lower_wd += wd
            upper_wa += wa
            both += wd and wa
        n = len(Ds)
        print(f"  pair ({a},{b}): recurring s={s} (excess {s - mx}), #sep={n}")
        print(
            f"     lower-cell weak-descent: {lower_wd}/{n}; upper-cell weak-ascent: {upper_wa}/{n}; BOTH: {both}/{n}"
        )
        # show g-profiles at the tail separating D
        for D in sampleD:
            ga, gb = c(a + D) - (a + D), c(b + D) - (b + D)
            print(
                f"       D={D}: g_a={ga} g_b={gb}  c(a+D)={c(a + D)} c(b+D)={c(b + D)}  thr=D+s={D + s}"
            )


def main():
    probe_caseD_bridge()
    print("\n=== (A) Case-C window/weak-descent-ascent discriminator ===")
    N = 6000
    # parity_shift (canonical wall), swap_at_powers, growing_blocks_rev
    c, _, _ = parity_shift(N + 10)
    probe_caseC_window("parity_shift", c, N, [(2, 4), (1, 3), (2, 5)])
    c, _, nmax = swap_at_powers(N + 10)
    probe_caseC_window("swap_at_powers", c, nmax - 1, [(2, 3), (1, 4), (2, 4)])
    c, _, nmax = growing_blocks(N + 10, True)
    probe_caseC_window("growing_blocks_rev", c, nmax - 1, [(2, 4), (1, 5), (3, 7)])


if __name__ == "__main__":
    main()
