#!/usr/bin/env python3
"""Rokicki-type constants for other sequences and other digit placements.

For a sequence a_0, a_1, ... and a 0/1 digit rule d_k = D(a_k), the constant is

    x = sum_{k>=0} d_k / 2^(e_k),    e_k = k + 1 (dense placement) or e.g. (k+1)!, 2^k, (k+1)^2.

This script computes each constant of the table in research/sequences.md from N = 3400 binary
digits (>= 1000 certified decimals), prints 60 decimals and the first 64 binary digits, detects
eventual periodicity of the digit sequence, runs PSLQ (degree <= 6, 300 digits) on the
non-periodic ones, and prints the supporting statistics quoted in the note (subword
complexity, Chebyshev-type biases, the sums-of-two-squares scaling defect, Gauss's quartic
criterion, Liouville exponents of the lacunary placements).

Rigor model.  With A = sum_{k: e_k <= N} d_k 2^(N - e_k), exactly A/2^N <= x <= (A+1)/2^N
(the tail is at most sum_{j > N} 2^-j).  The 60 printed decimals are checked to agree for both
ends of the enclosure.  PSLQ, periodicity detection and the statistics are evidence, not proof.

Usage:  python3 scripts/sequences.py [--full]      (--full prints 1000 decimals of each)
Dependencies: numpy, sympy (only for a cross-check), mpmath.  Runtime: about 15 seconds.
"""

import argparse
import io
import math
import sys
import time

import numpy as np
import mpmath
from fractions import Fraction

from mpmath import mp, mpf
from sympy import isprime

sys.set_int_max_str_digits(0)

NBITS = 3400            # binary digits per constant: 3400 log10(2) = 1023 decimals
SIEVE = 10 ** 7         # primes below this bound, for the digit sequences and the statistics
PSLQ_DPS = 300
PSLQ_DEG = 6
PSLQ_C = 25             # maxcoeff = 10^25: (0.75 * 300 - 50) / 6 ~ 29, rounded down
MAX_PERIOD = 1000


# ---------------------------------------------------------------------------------------------
# Sequences
# ---------------------------------------------------------------------------------------------

def primes_below(n):
    s = np.ones(n, dtype=bool)
    s[:2] = False
    s[4::2] = False
    for p in range(3, math.isqrt(n) + 1, 2):
        if s[p]:
            s[p * p::2 * p] = False
    return np.nonzero(s)[0]


def squarefree_below(n):
    s = np.ones(n, dtype=bool)
    s[0] = False
    for p in primes_below(math.isqrt(n) + 1):
        s[p * p::p * p] = False
    return np.nonzero(s)[0]


def sums_of_two_squares_below(n):
    s = np.zeros(n, dtype=bool)
    for a in range(math.isqrt(n) + 1):
        b = np.arange(a, math.isqrt(max(n - 1 - a * a, 0)) + 1)
        s[a * a + b * b] = True
    s[0] = False
    return np.nonzero(s)[0]


def two_squares(p):
    """p = a^2 + b^2 with a odd > 0, b even > 0, for a prime p = 1 (mod 4) (Hermite-Serret)."""
    c = 2
    while pow(c, (p - 1) // 2, p) != p - 1:
        c += 1
    r = pow(c, (p - 1) // 4, p)          # r^2 = -1 (mod p)
    a, b = p, r
    while b * b > p:
        a, b = b, a % b
    x, y = b, math.isqrt(p - b * b)
    assert x * x + y * y == p
    return (x, y) if x % 2 else (y, x)


def isqrt_vec(m):
    """Exact floor(sqrt(m)) for an int64 numpy array."""
    r = np.floor(np.sqrt(m.astype(np.float64))).astype(np.int64)
    r -= (r * r > m)
    r += ((r + 1) * (r + 1) <= m)
    return r


def thue_morse(n):
    t = np.zeros(n, dtype=np.int64)
    for k in range(1, n):
        t[k] = t[k >> 1] ^ (k & 1)
    return t


# ---------------------------------------------------------------------------------------------
# Constants: digits, enclosures, values
# ---------------------------------------------------------------------------------------------

def dense(digits):
    """Digits placed at positions 1, 2, 3, ...: returns (A, N) with A/2^N <= x <= (A+1)/2^N."""
    bits = "".join("1" if d else "0" for d in digits[:NBITS])
    assert len(bits) == NBITS, "not enough terms"
    return int(bits, 2), NBITS


def placed(digits, pos):
    """Digit k at binary position pos(k) (strictly increasing): enclosure from positions <= N."""
    A, k = 0, 0
    while pos(k) <= NBITS:
        if digits[k]:
            A += 1 << (NBITS - pos(k))
        k += 1
    return A, NBITS


def value(enc, dps):
    A, N = enc
    with mp.workdps(dps + 10):
        return mpf(A) / mpf(2) ** N


def decimals(enc, n):
    """n decimals of x, checked against both ends of the enclosure."""
    A, N = enc
    lo = (A * 10 ** n) >> N
    hi = ((A + 1) * 10 ** n) >> N
    s = str(lo).rjust(n, "0")
    ok = lo == hi or (hi - lo == 1 and (A + 1) * 10 ** n == hi << N)
    return "0." + s, ok


def first_bits(enc, n=64):
    A, N = enc
    return bin(A)[2:].rjust(N, "0")[:n]


def eventual_period(d, max_period=MAX_PERIOD):
    """Smallest (period, preperiod) consistent with the whole finite sequence, with the period
    <= max_period and the periodic part covering at least the last 3/4 of the data."""
    d = np.asarray(d, dtype=np.int8)
    n = len(d)
    for P in range(1, max_period + 1):
        diff = np.nonzero(d[P:] != d[:-P])[0]
        pre = 0 if len(diff) == 0 else diff[-1] + 1
        if pre <= n // 4:
            return P, int(pre)
    return None


def run_pslq(x):
    """First integer relation among 1, x, ..., x^d for d = 1, ..., PSLQ_DEG (or None)."""
    with mp.workdps(PSLQ_DPS):
        for deg in range(1, PSLQ_DEG + 1):
            vec = [x ** i for i in range(deg + 1)]
            old = sys.stdout
            sys.stdout = io.StringIO()
            try:
                rel = mpmath.pslq(vec, maxcoeff=10 ** PSLQ_C, maxsteps=10 ** 5)
            finally:
                sys.stdout = old
            if rel is not None:
                return rel
    return None


# ---------------------------------------------------------------------------------------------
# Supporting statistics
# ---------------------------------------------------------------------------------------------

def complexity(d, L):
    """Number of distinct words of length L in the 0/1 (or small-alphabet) sequence d."""
    d = np.asarray(d, dtype=np.int64)
    base = int(d.max()) + 1
    n = len(d) - L + 1
    code = np.zeros(n, dtype=np.int64)
    for j in range(L):
        code = code * base + d[j:j + n]
    return len(np.unique(code)), base ** L


def bias(signs):
    """Fraction of n with S(n) < 0 and number of sign changes of S(n) = sum_{k<n} signs[k]."""
    S = np.cumsum(signs)
    neg = float(np.mean(S < 0))
    nz = np.sign(S[S != 0])
    changes = int(np.count_nonzero(nz[1:] != nz[:-1]))
    return neg, changes, int(S[-1])


def longest_runs(d, value_, upto):
    """First index at which a run of `value_` of length L starts, for L = 1, 2, ..."""
    first = {}
    run = 0
    for k, x in enumerate(d[:upto]):
        run = run + 1 if x == value_ else 0
        if run and run not in first:
            first[run] = k - run + 1
    return first


# ---------------------------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--full", action="store_true", help="print 1000 decimals of each constant")
    args = ap.parse_args()
    t0 = time.time()

    P = primes_below(SIEVE)
    odd = P[1:]
    p13 = P[P % 3 == 1]
    p23 = P[(P % 3 == 2) & (P > 2)]
    p18 = P[P % 8 == 1]
    p14 = P[P % 4 == 1]
    quartic = np.array([pow(2, (int(p) - 1) // 4, int(p)) == 1 for p in p18])
    sq = squarefree_below(SIEVE)
    s2 = sums_of_two_squares_below(SIEVE)
    k = np.arange(1, 400001, dtype=np.int64)
    beatty = isqrt_vec(2 * k * k)                       # floor(k sqrt 2), k >= 1
    beatty_diff = np.diff(np.concatenate(([0], beatty)))  # Sturmian: values 1, 2
    fib = [0, 1]
    while len(fib) < NBITS + 10:
        fib.append((fib[-1] + fib[-2]) % 4)
    tm = thue_morse(200000)
    rok = odd % 4 == 3                                  # Rokicki's digits b_k

    ab = np.array([two_squares(int(p)) for p in p14])  # p = a^2 + b^2, a odd > 0, b even > 0
    sector = ab[:, 0] % 4 == 3

    # name: (description, digit sequence (for periodicity), enclosure, kind)
    C = {}

    def add(name, desc, d, enc=None, kind="dense"):
        C[name] = (desc, np.asarray(d[:max(NBITS, 200000)], dtype=np.int8),
                   enc if enc is not None else dense(d), kind)

    add("rho", "[p == 3 mod 4], odd primes (Rokicki)", rok)
    add("ap_1mod3", "[p == 7 mod 12], primes p == 1 mod 3", p13 % 12 == 7)
    add("ap_2mod3", "[p == 11 mod 12], primes p == 2 mod 3", p23 % 12 == 11)
    add("hecke", "[2 not a 4th power mod p], primes p == 1 mod 8", ~quartic)
    add("sector", "[a == 3 mod 4], p = a^2+b^2 == 1 mod 4, a odd > 0", sector)
    add("sum2sq", "[n odd], n = sums of two squares", s2 % 2 == 1)
    add("squarefree", "[s == 3 mod 4], s squarefree", sq % 4 == 3)
    add("beatty", "[floor(k sqrt2) == 3 mod 4], k >= 1", beatty % 4 == 3)
    add("sturmian", "[floor((k+1)sqrt2) - floor(k sqrt2) = 2]", beatty_diff == 2)
    add("thue_morse", "[t_k = 1], Thue-Morse", tm == 1)
    add("fibonacci", "[F_k == 3 mod 4], k >= 0", np.array(fib) == 3, kind="periodic")
    add("squares", "[k^2 == 1 mod 4], k >= 0", np.arange(NBITS + 10) % 2 == 1, kind="periodic")
    add("powers3", "[3^k == 3 mod 4], k >= 0",
        np.array([pow(3, j, 4) == 3 for j in range(NBITS + 10)]), kind="periodic")
    add("lac_fact", "Rokicki digits at positions (k+1)!", rok,
        placed(rok, lambda j: math.factorial(j + 1)), kind="lacunary")
    add("lac_pow2", "Rokicki digits at positions 2^k", rok,
        placed(rok, lambda j: 2 ** j), kind="lacunary")
    add("lac_square", "Rokicki digits at positions (k+1)^2", rok,
        placed(rok, lambda j: (j + 1) ** 2), kind="lacunary")

    print("# Rokicki-type constants: values, periodicity, PSLQ\n")
    print(f"N = {NBITS} binary digits per constant; primes below {SIEVE:.0e}; "
          f"PSLQ on [1, x, ..., x^{PSLQ_DEG}] at {PSLQ_DPS} digits, maxcoeff 10^{PSLQ_C}.\n")
    for name, (desc, d, enc, kind) in C.items():
        dec, ok = decimals(enc, 60)
        print(f"## {name}: {desc}")
        print(f"   x      = {dec}{'' if ok else '  (enclosure ends differ!)'}")
        print(f"   binary = 0.{first_bits(enc)}")
        if kind == "lacunary":
            print("   digit sequence: Rokicki's (see rho); binary expansion is sparse")
            print("   PSLQ: skipped -- to 300 digits x is a dyadic rational of height "
                  "> 10^150 (see the Liouville exponents below)")
        else:
            per = eventual_period(d)
            if per is None:
                print(f"   period: none <= {MAX_PERIOD} in {len(d)} digits")
            else:
                Pd, pre = per
                print(f"   period: {Pd} (preperiod {pre}) over {len(d)} digits")
                if pre == 0:
                    num = int("".join(str(int(v)) for v in d[:Pd]), 2)
                    fr = Fraction(num, 2 ** Pd - 1)
                    A, N = enc
                    agree = A <= fr * 2 ** N <= A + 1
                    print(f"   exact value: {fr} (agrees with enclosure: {agree})")
            rel = run_pslq(value(enc, PSLQ_DPS))
            if rel is None:
                print(f"   PSLQ: no relation of degree <= {PSLQ_DEG} with |coeff| <= "
                      f"10^{PSLQ_C}")
            else:
                print(f"   PSLQ: relation {rel} (coefficients of 1, x, x^2, ...)")
        if args.full:
            print(f"   1000 decimals: {decimals(enc, 1000)[0]}")
        print()

    print("# Supporting statistics\n")

    print("## Gauss: for p == 1 mod 8, 2 is a 4th power mod p iff p = x^2 + 64 y^2 (8 | b)")
    bad = 0
    for p, q in zip(p18[:20000], quartic[:20000]):
        a, b = two_squares(int(p))
        bad += (b % 8 == 0) != bool(q)
    print(f"   checked for the first 20000 primes p == 1 mod 8 (p < {p18[19999]}): "
          f"{bad} exceptions; quartic residues: {quartic.mean():.4f} of {len(p18)}")
    same = bool(np.all((ab[:, 1] % 4 == 2) == (p14 % 8 == 5)))
    tab = {r: sorted(set((ab[p14 % 8 == r, 0] % 4).tolist())) for r in (1, 5)}
    print(f"   all {len(p14)} p == 1 mod 4 below 1e7: [b == 2 mod 4] == [p == 5 mod 8]: {same}; "
          f"a mod 4 by p mod 8: {tab}")
    chi_a = np.where(ab[:, 0] % 4 == 1, 1, -1)
    print(f"   sector digit sum_p chi_4(a_p) = {int(chi_a.sum())}, of which a = 1 (p = 1 + b^2): "
          f"{int(chi_a[ab[:, 0] == 1].sum())}, a <= 9: {int(chi_a[ab[:, 0] <= 9].sum())}; "
          f"sign of Re(primary pi): sum = "
          f"{int((chi_a * np.where(p14 % 8 == 1, 1, -1)).sum())}")
    print()

    print("## Chebyshev-type bias: fraction of n with S(n) < 0, S(n) = sum_{k<n} (1 - 2 d_k)")
    for name, d in [("rho (chi_4 over odd primes)", rok),
                    ("ap_1mod3 (1 vs 7 mod 12)", p13 % 12 == 7),
                    ("ap_2mod3 (5 vs 11 mod 12)", p23 % 12 == 11),
                    ("hecke (quartic vs not, p == 1 mod 8)", ~quartic),
                    ("sector (a == 1 vs 3 mod 4)", np.array(sector))]:
        signs = 1 - 2 * np.asarray(d, dtype=np.int64)
        neg, ch, last = bias(signs)
        print(f"   {name:40s} terms {len(signs):8d}  S<0: {neg:6.1%}  sign changes {ch:5d}  "
              f"S(end) = {last}")
    print()

    print("## Sums of two squares: B(x) - 2 B(x/2) (would be O(1) if the parity digits "
          "were eventually periodic)")
    s2_set = s2
    for x in [10 ** j for j in range(3, 8)]:
        Bx = int(np.searchsorted(s2_set, x, side="right"))
        Bh = int(np.searchsorted(s2_set, x // 2, side="right"))
        res = int(np.count_nonzero(s2_set[s2_set <= x] % 4 == 3))
        print(f"   x = 1e{int(math.log10(x))}: B(x) = {Bx:8d}, B(x) - 2B(x/2) = {Bx - 2 * Bh:7d}, "
              f"elements == 3 mod 4: {res}")
    print()

    print("## Subword complexity p(L) (distinct words of length L)")
    sq_res = (sq % 4)[:6000000]
    row = []
    for L in range(1, 13):
        c, full = complexity(sq_res, L)
        row.append(f"{L}:{c}/{full}")
    print(f"   squarefree residues mod 4 (alphabet 1,2,3; {len(sq_res)} terms): " + " ".join(row))
    # forced non-squarefree numbers (not divisible by 4) between consecutive residues r -> r'
    forced = {(r, t): sum(1 for j in range(1, (t - r - 1) % 4 + 1) if (r + j) % 4)
              for r in (1, 2, 3) for t in (1, 2, 3)}
    L = 5
    n = len(sq_res) - L + 1
    code = np.zeros(n, dtype=np.int64)
    for j in range(L):
        code = code * 4 + sq_res[j:j + n]
    seen = set(np.unique(code).tolist())
    missing = []
    for w in np.ndindex(*(3,) * L):
        word = [x + 1 for x in w]
        c = 0
        for x in word:
            c = c * 4 + x
        if c not in seen:
            missing.append(sum(forced[(word[i], word[i + 1])] for i in range(L - 1)))
    print(f"   words of length 5 missing: {len(missing)}; each forces at least {min(missing)} "
          f"numbers not divisible by 4 to be non-squarefree (max possible 8); "
          f"forced-count histogram of missing words: "
          f"{ {m: missing.count(m) for m in sorted(set(missing))} }")
    for name, d in [("beatty", beatty % 4 == 3), ("sturmian", beatty_diff == 2),
                    ("beatty residues mod 4", beatty % 4), ("thue_morse", tm == 1)]:
        vals = [complexity(d, L)[0] for L in range(1, 31)]
        print(f"   {name:22s} L=1..30: {vals}")
    print()

    print("## Liouville exponents of the lacunary placements")
    print("   mu_n = log(1/|x - p_n/q_n|) / log q_n for the truncation after digit n "
          "(q_n = 2^{e_n})")
    ones = np.nonzero(rok)[0]
    for name, pos in [("(k+1)!", lambda j: math.factorial(j + 1)), ("2^k", lambda j: 2 ** j),
                      ("(k+1)^2", lambda j: (j + 1) ** 2)]:
        out = []
        for n in range(0, 9):
            nxt = ones[ones > n][0]
            # tail = 2^{-pos(nxt)} (1 + theta), 0 <= theta < 1: mu = pos(nxt)/pos(n) - O(1/pos(n))
            out.append(f"{pos(int(nxt)) / pos(n):.3g}")
        print(f"   positions {name:8s}: mu_0..mu_8 ~ {', '.join(out)}")
    zr = longest_runs(rok, False, len(rok))
    print(f"   runs of Rokicki digit 0 (consecutive primes == 1 mod 4) below {SIEVE:.0e}: "
          f"first run of length L starts at index { {L: zr[L] for L in sorted(zr)} }")
    print("   (positions 2^k: a run of L zeros after digit n gives mu_n >= 2^(L+1); "
          "Shiu: L unbounded)")
    print()

    assert isprime(int(p18[-1]))
    print(f"[done in {time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
