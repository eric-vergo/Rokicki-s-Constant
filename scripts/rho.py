#!/usr/bin/env python3
"""Rokicki's constant rho.

A362583(n) = the integer whose binary digits are, for the odd primes
3 = p_2, p_3, ..., p_n in order, the bit [p_k == 3 (mod 4)].
Hence A362583(n) / 2^(n-1) is the binary fraction 0.b_2 b_3 ... b_n and

    rho := lim_{n->oo} A362583(n) / 2^(n-1)
         = sum_{k>=2} [p_k == 3 (mod 4)] * 2^(-(k-1)).

Usage:  python3 scripts/rho.py [number_of_primes] [decimal_digits]
"""
import sys
from fractions import Fraction
from sympy import prime, primerange
from mpmath import mp, mpf

N = int(sys.argv[1]) if len(sys.argv) > 1 else 400
DIGITS = int(sys.argv[2]) if len(sys.argv) > 2 else 60
mp.dps = DIGITS + 10


def a362583(n):
    c = 0
    for k in range(2, n + 1):
        c = (c << 1) + (prime(k) & 3 == 3)
    return c


def rho_partial(n):
    """Exact rational partial sum using the first n primes (p_2..p_n)."""
    return Fraction(a362583(n), 2 ** (n - 1))


if __name__ == "__main__":
    # check against OEIS data
    print("a(2..12) =", [a362583(n) for n in range(2, 13)])
    r = rho_partial(N)
    # the tail is < 2^-(N-1), so r <= rho < r + 2^-(N-1)
    lo = mpf(r.numerator) / mpf(r.denominator)
    hi = lo + mpf(2) ** (-(N - 1))
    print(f"using primes p_2..p_{N} (p_{N} = {prime(N)}):")
    print(f"  rho >= {mp.nstr(lo, DIGITS)}")
    print(f"  rho <  {mp.nstr(hi, DIGITS)}")
    bits = "".join("1" if p % 4 == 3 else "0" for p in primerange(3, prime(60) + 1))
    print("binary expansion: 0." + bits + "...")
    for n in (10, 20, 30, 40):
        print(f"  a({n})/2^{n-1} = {float(rho_partial(n)):.12f}")
