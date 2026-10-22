#!/usr/bin/env python3
"""Rokicki-type constants of the sums of two squares and of the squarefree numbers.

Companion to research/two-squares-squarefree.md and RokickiConstant/General/TwoSquares.lean.

Let s_0 = 1 < s_1 = 2 < 4 < 5 < ... be the positive sums of two squares and u_0 = 1 < u_1 = 2 <
3 < 5 < ... the squarefree numbers.  For each digit rule d_k below, the script prints

* the dense constant x = sum_k d_k / 2^(k+1) to 60 decimals, certified by an exact enclosure
  A / 2^N <= x <= (A + 1) / 2^N from N = 3400 exact binary digits;
* the smallest eventual period <= 1000 of the first 2 * 10^5 digits (none expected except for
  the identically zero digit [s_k = 3 mod 4]);
* the first integer relation among 1, x, ..., x^d, d <= 6, found by PSLQ at 300 digits with
  coefficients up to 10^25 (none expected except x = 0).

It then prints the numerics behind the proofs:

* sums of two squares: Landau's B(x) ~ K x / sqrt(log x); the quantities that eventual
  periodicity of the residue digits would force to be O(1); the longest runs of 0s of the square
  and prime digits;
* squarefree numbers: subword complexity of u_k mod 4 for words of length <= 5, and the first
  index of a run of each residue of each length (the runs used in the Lean proof).

Exactness: membership in both sequences is decided by exact integer sieves; every digit is
exact.  Run statistics and complexities are over finite prefixes (evidence, not proof).

Usage:  python3 scripts/two_squares.py
Dependencies: numpy, mpmath.  Runtime: about 20 seconds.
"""

import io
import math
import sys

import mpmath
import numpy as np
from mpmath import mp, mpf

sys.set_int_max_str_digits(0)

X = 10 ** 7             # sieve bound
NBITS = 3400            # binary digits per constant: 3400 log10(2) = 1023 decimals
N_DEC = 60
PERIOD_DIGITS = 2 * 10 ** 5
MAX_PERIOD = 1000
PSLQ_DPS = 300
PSLQ_DEG = 6
PSLQ_C = 25
LANDAU_K = mpf("0.76422365358922066299069873125009232811679054139340951472168667374961464165873")


# ---------------------------------------------------------------------------------------------
# Sieves
# ---------------------------------------------------------------------------------------------

def primes_below(n):
    s = np.ones(n, dtype=bool)
    s[:2] = False
    s[4::2] = False
    for p in range(3, math.isqrt(n) + 1, 2):
        if s[p]:
            s[p * p::2 * p] = False
    return s


def squarefree_mask(n):
    s = np.ones(n, dtype=bool)
    s[0] = False
    for p in np.nonzero(primes_below(math.isqrt(n) + 1))[0]:
        s[p * p::p * p] = False
    return s


def sum_two_squares_mask(n):
    s = np.zeros(n, dtype=bool)
    for a in range(math.isqrt(n) + 1):
        b = np.arange(a, math.isqrt(max(n - 1 - a * a, 0)) + 1)
        s[a * a + b * b] = True
    s[0] = False
    return s


def is_square_vec(m):
    r = np.floor(np.sqrt(m.astype(np.float64))).astype(np.int64)
    r -= (r * r > m)
    r += ((r + 1) * (r + 1) <= m)
    return r * r == m


# ---------------------------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------------------------

def enclosure(digits):
    bits = "".join("1" if d else "0" for d in digits[:NBITS])
    assert len(bits) == NBITS
    return int(bits, 2), NBITS


def decimals(enc, n):
    """n decimals of x, checked against both ends of the enclosure."""
    A, N = enc
    lo = (A * 10 ** n) >> N
    hi = ((A + 1) * 10 ** n) >> N
    ok = lo == hi or (hi - lo == 1 and (A + 1) * 10 ** n == hi << N)
    return "0." + str(lo).rjust(n, "0"), ok


def value(enc, dps):
    A, N = enc
    with mp.workdps(dps + 10):
        return mpf(A) / mpf(2) ** N


def eventual_period(d):
    d = np.asarray(d, dtype=np.int8)
    n = len(d)
    for P in range(1, MAX_PERIOD + 1):
        diff = np.nonzero(d[P:] != d[:-P])[0]
        pre = 0 if len(diff) == 0 else diff[-1] + 1
        if pre <= n // 4:
            return P, int(pre)
    return None


def run_pslq(x):
    if x == 0:
        return [1]
    with mp.workdps(PSLQ_DPS):
        for deg in range(1, PSLQ_DEG + 1):
            vec = [x ** i for i in range(deg + 1)]
            old, sys.stdout = sys.stdout, io.StringIO()
            try:
                rel = mpmath.pslq(vec, maxcoeff=10 ** PSLQ_C, maxsteps=10 ** 5)
            finally:
                sys.stdout = old
            if rel is not None:
                return rel
    return None


def report(name, d):
    enc = enclosure(d)
    dec, ok = decimals(enc, N_DEC)
    per = eventual_period(d[:PERIOD_DIGITS])
    rel = run_pslq(value(enc, PSLQ_DPS))
    freq = float(np.mean(d[:PERIOD_DIGITS]))
    print(f"{name}")
    print(f"    x = {dec}  (enclosure {'ok' if ok else 'FAILED'})")
    print(f"    density of 1s (first {PERIOD_DIGITS}) = {freq:.4f};  eventual period <= "
          f"{MAX_PERIOD}: {per};  PSLQ (deg <= {PSLQ_DEG}): {rel}")


# ---------------------------------------------------------------------------------------------
# Statistics
# ---------------------------------------------------------------------------------------------

def longest_run(d, v):
    best, run, start = 0, 0, None
    for k, x in enumerate(d):
        run = run + 1 if x == v else 0
        if run > best:
            best, start = run, k - run + 1
    return best, start


def first_runs(d, v):
    """First index at which a run of value v of length L starts, for each L that occurs."""
    first, run = {}, 0
    for k, x in enumerate(d):
        run = run + 1 if x == v else 0
        if run and run not in first:
            first[run] = k - run + 1
    return first


def complexity(d, L, base):
    d = np.asarray(d, dtype=np.int64)
    n = len(d) - L + 1
    code = np.zeros(n, dtype=np.int64)
    for j in range(L):
        code = code * base + d[j:j + n]
    return np.unique(code)


def main():
    S_mask = sum_two_squares_mask(X)
    S = np.nonzero(S_mask)[0]
    P_mask = primes_below(X)
    Q_mask = squarefree_mask(X)
    U = np.nonzero(Q_mask)[0]
    print(f"sums of two squares below 10^7: {len(S)};  squarefree numbers below 10^7: {len(U)}")
    print()

    print("=" * 96)
    print("Sums of two squares s_k: constants")
    print("=" * 96)
    report("[s_k = 3 mod 4]  (identically 0)", (S % 4 == 3).astype(np.int8))
    report("[s_k odd] = [s_k = 1 mod 4]  (irrational under Landau; Lean, conditional)",
           (S % 2).astype(np.int8))
    report("[s_k = 0 mod 4]  (irrational under Landau; note)", (S % 4 == 0).astype(np.int8))
    report("[s_k = 2 mod 4]  (irrational under Landau; note)", (S % 4 == 2).astype(np.int8))
    report("[s_k = 1 mod 8]  (open)", (S % 8 == 1).astype(np.int8))
    report("[s_k is a square]  (irrational; Lean)", is_square_vec(S).astype(np.int8))
    report("[s_k is prime]  (irrational; Lean)", P_mask[S].astype(np.int8))
    print()

    print("=" * 96)
    print("Sums of two squares: Landau and the quantities periodicity would bound")
    print("=" * 96)
    B = np.cumsum(S_mask)                        # B[x] = #{s <= x}
    odd = np.cumsum(S_mask & (np.arange(X) % 2 == 1))
    c81 = np.cumsum(S_mask & (np.arange(X) % 8 == 1))
    c85 = np.cumsum(S_mask & (np.arange(X) % 8 == 5))
    print("       x |        B(x) | B sqrt(log x)/x | odd/B  | B(x)-2B(x/2) | Landau pred. |"
          " B(x)-4B(x/4) | B(x/2)-B(x/4)-B(x)/4 | B(x;8,1)-B(x;8,5)")
    for e in range(3, 8):
        x = 10 ** e - 1
        b = int(B[x])
        lan = float(b * mpmath.sqrt(mpmath.log(x)) / x)
        pred = float(-LANDAU_K * x * mpmath.log(2) / (2 * mpmath.log(x) ** 1.5))
        d2 = b - 2 * int(B[x // 2])
        d4 = b - 4 * int(B[x // 4])
        d24 = int(B[x // 2]) - int(B[x // 4]) - b / 4
        print(f"{x + 1:8.0e} | {b:11d} | {lan:15.6f} | {odd[x] / b:.4f} | {d2:12d} |"
              f" {pred:12.0f} | {d4:12d} | {d24:20.1f} | {int(c81[x]) - int(c85[x]):10d}")
    print(f"Landau-Ramanujan constant K = {float(LANDAU_K):.10f}; the column B sqrt(log x)/x"
          " converges to K slowly, from above (secondary term ~ K c / log x).")
    print("Eventual periodicity of [s_k odd] would force B(x) - 2B(x/2) = O(1); of [s_k = 0 mod 4],"
          " B(x) - 4B(x/4) = O(1); of [s_k = 2 mod 4], B(x/2) - B(x/4) - B(x)/4 = O(1).")
    print()
    sq = is_square_vec(S).astype(np.int8)
    pr = P_mask[S].astype(np.int8)
    for name, d in (("square digit", sq), ("prime digit", pr)):
        L, k = longest_run(d, 0)
        print(f"{name}: longest run of 0s among s_k < 10^7 has length {L}, at k = {k}"
              f" (s_k = {S[k]}..{S[k + L - 1]})")
    print("(the Lean windows: between t^2 and (t+1)^2 there are ~ 2t K/sqrt(log t^2) sums of two"
          " squares and no square; the prime windows sit at t = R! (L + 2)^2 and are far beyond"
          " 10^7.)")
    print()

    print("=" * 96)
    print("Squarefree numbers u_k: constants")
    print("=" * 96)
    r = (U % 4).astype(np.int64)
    report("[u_k = 3 mod 4]  (irrational; Lean)", (r == 3).astype(np.int8))
    report("[u_k = 1 mod 4]  (irrational; Lean)", (r == 1).astype(np.int8))
    report("[u_k even] = [u_k = 2 mod 4]  (irrational; Lean)", (r == 2).astype(np.int8))
    enc4 = 0
    for k in range(1700):
        enc4 = 4 * enc4 + int(r[k])
    lo = (enc4 * 10 ** N_DEC) >> (2 * 1700)
    hi = ((enc4 + 1) * 10 ** N_DEC) >> (2 * 1700)
    print("sum_k (u_k mod 4) / 4^(k+1)  (irrational; Lean)")
    print(f"    x = 0.{str(lo).rjust(N_DEC, '0')}  (enclosure {'ok' if lo == hi else 'FAILED'})")
    print()

    print("=" * 96)
    print("Squarefree numbers: words and runs of residues mod 4")
    print("=" * 96)
    r3 = r - 1                                   # residues 1, 2, 3 -> 0, 1, 2
    for L in range(1, 6):
        words = complexity(r3, L, 3)
        missing = 3 ** L - len(words)
        line = f"L = {L}: {len(words):3d} of {3 ** L:3d} words occur"
        if 0 < missing <= 30:
            allw = set(range(3 ** L))
            miss = sorted(allw - set(words.tolist()))
            dig = ["".join(str((w // 3 ** (L - 1 - j)) % 3 + 1) for j in range(L)) for w in miss]
            line += f"; missing: {' '.join(dig)}"
        print(line)
    for v in (1, 2, 3):
        fr = first_runs(r, v)
        Lmax = max(fr)
        shown = ", ".join(f"{L}: {fr[L]}" for L in sorted(fr))
        print(f"residue {v}: longest run {Lmax}; first index of a run of length L -> {shown}")


if __name__ == "__main__":
    main()
