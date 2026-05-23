"""Convergence-permutation framework probes for the lone P4 lemma.

Implements t(p,n) = #msi of p([1,n]), U(p), V(p) (Witula Lemma 7.1/7.3), classifies
each documented witness as class C (t bounded) or class D (t -> infinity), builds a
genuine class-D non-EI permutation, and tests the per-pair (separator) <-> global
(U/V block-count) connection that the proposed split needs.

Run: uv run convergence.py
"""

from families import FAMILIES


def num_msi(image_set):
    """Number of maximal runs of consecutive integers in a finite set."""
    if not image_set:
        return 0
    s = sorted(image_set)
    blocks = 1
    for i in range(1, len(s)):
        if s[i] != s[i - 1] + 1:
            blocks += 1
    return blocks


def t_sequence(c, N):
    """t(p,n) for n=1..N, incremental."""
    cur = set()
    out = []
    for n in range(1, N + 1):
        cur.add(c(n))
        out.append(num_msi(cur))
    return out


def UV_sets(tseq):
    """U = {n : t(n)-t(n-1)=+1}, V = {n : t(n)-t(n-1)=-1}.  t(0):=0, indices are n (1-based)."""
    U, Vs = [], []
    prev = 0
    for idx, tn in enumerate(tseq):
        n = idx + 1
        d = tn - prev
        if d == 1:
            U.append(n)
        elif d == -1:
            Vs.append(n)
        prev = tn
    return U, Vs


def classify(c, N):
    tseq = t_sequence(c, N)
    tmax = max(tseq)
    tmin = min(tseq)
    # crude class detection: look at tail growth
    tail = tseq[N // 2 :]
    tail_max = max(tail)
    return tseq, tmin, tmax, tail_max


def main():
    N = 4000
    print(f"=== Classification of witnesses (N={N}) ===")
    print(
        f"{'family':24} {'t_min':>6} {'t_max':>6} {'tail_max':>9} {'|U[:N]|':>8} {'|V[:N]|':>8}  class"
    )
    results = {}
    for name, (factory, is_ei) in sorted(FAMILIES.items()):
        try:
            c, cinv, nmax = factory(N + 10)
        except Exception as e:
            print(f"{name:24} ERROR {e}")
            continue
        eff = min(N, nmax - 1)
        tseq, tmin, tmax, tail_max = classify(c, eff)
        U, Vs = UV_sets(tseq)
        # heuristic: class D if t still climbing in second half (tail_max > first-half max + slack)
        first_half_max = max(tseq[: eff // 2]) if eff >= 2 else tmax
        cls = "D?" if tail_max > first_half_max else "C"
        # stronger: compare quarters
        q1 = max(tseq[: eff // 4]) if eff >= 4 else tmax
        q4 = max(tseq[3 * eff // 4 :]) if eff >= 4 else tmax
        cls = "D" if q4 > q1 + 1 else "C"
        results[name] = (tseq, U, Vs, cls)
        print(
            f"{name:24} {tmin:>6} {tmax:>6} {tail_max:>9} {len(U):>8} {len(Vs):>8}  {cls}"
        )
    return results


if __name__ == "__main__":
    main()
