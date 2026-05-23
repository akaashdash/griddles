"""Verify the EXACT bounds the Lean scaffolding needs, honestly.

For D in S = {c(b+D)>b+D AND |c(a+D)-c(b+D)|>=2}, M=b (a<b), bounded disp B:
  window (lo, hi] with lo=min(ca,cb)-D, hi=max(ca,cb)-D.
  Claim A: hi >= M+1.   (because cb-D > b => if cb>=ca then hi=cb-D>=b+1=M+1;
                          if ca>cb then hi=ca-D, and ca>=cb+2>b+D+2 so hi>=b+3>=M+1.)
  Claim B: hi - lo >= 2  (gap>=2 means |ca-cb|>=2, hi-lo=|ca-cb|).
  => exists even s in (lo,hi] with s>=M  (the arith lemma), AND we need s <= M+B
     for the finite pigeonhole range [M, M+B].
  Claim C: the chosen even s satisfies s <= M+B = b+B.
     s <= hi = max(ca,cb)-D <= (b+D+B)-D = b+B   [bounded disp: ca<=a+D+B<=b+D+B, cb<=b+D+B].
     So s <= b+B. GOOD.

Also: must the chosen s be the SAME parity-consistent one, and is M <= s? yes s>=M by arith.

So the containment lemma:  D in S  =>  exists even s, M <= s <= M+B, separatorAtSlack c a b s D.
Verify ALL three claims with 0 violations, and that s in [M, M+B] always.
"""

from families import FAMILIES


def make_c(fn, NMAX):
    return fn(NMAX)


def bdd_disp_bound(c, n):
    B = 0
    for x in range(1, n + 1):
        B = max(B, abs(c(x) - x))
    return B


def even_in_window_ge_M(lo, hi, M):
    for s in (hi, hi - 1):
        if s % 2 == 0 and s > lo and s >= M:
            return s
    return None


def main():
    NMAX = 20000
    pairs = [(1, 2), (2, 3), (1, 3), (1, 4), (3, 5), (2, 7)]
    fails_A = fails_B = fails_C = fails_arith = fails_range = 0
    fails_sep = 0
    total = 0
    for name, (fn, is_ei) in FAMILIES.items():
        if is_ei or name.startswith("growing"):
            continue
        for a, b in pairs:
            c, cinv, n = make_c(fn, NMAX)
            B = bdd_disp_bound(c, n)
            M = b
            Dmax = n - b - 1
            for D in range(Dmax):
                ca = c(a + D)
                cb = c(b + D)
                if not (cb > b + D and abs(ca - cb) >= 2):
                    continue  # not in S
                total += 1
                lo = min(ca, cb) - D
                hi = max(ca, cb) - D
                if not (hi >= M + 1):
                    fails_A += 1
                if not (hi - lo >= 2):
                    fails_B += 1
                if not (hi <= M + B):
                    fails_C += 1
                s = even_in_window_ge_M(lo, hi, M)
                if s is None:
                    fails_arith += 1
                    continue
                if not (M <= s <= M + B):
                    fails_range += 1
                # actual separator check: [ca < D+s] != [cb < D+s]
                sep = (ca < D + s) != (cb < D + s)
                if not sep:
                    fails_sep += 1
    print(f"total D in S checked: {total}")
    print(f"  fails hi>=M+1      : {fails_A}")
    print(f"  fails hi-lo>=2     : {fails_B}")
    print(f"  fails hi<=M+B      : {fails_C}")
    print(f"  fails arith(s exists): {fails_arith}")
    print(f"  fails M<=s<=M+B    : {fails_range}")
    print(f"  fails separator    : {fails_sep}")


if __name__ == "__main__":
    main()
