#!/usr/bin/env python3
"""Numerical values of the constants of the research fork.

* rho_b  = sum_{k>=0} [p_{k+2} == 3 (mod 4)] / b^(k+1)   (Rokicki's digits read in base b)
* lambda_{l,b} = sum_{k>=0} [p_k is a quadratic non-residue mod l] / b^(k+1)   (Legendre constants)

Usage: python3 scripts/constants.py [number_of_primes]
"""
import sys
from fractions import Fraction
from sympy import prime, legendre_symbol
from mpmath import mp, mpf

N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
mp.dps = 40


def show(name, frac, b):
    lo = mpf(frac.numerator) / mpf(frac.denominator)
    print(f"{name} = {mp.nstr(lo, 30)}  (error < {b}^-{N})")


def rho(b):
    return sum(Fraction(int(prime(k + 2) % 4 == 3), b ** (k + 1)) for k in range(N))


def legendre_constant(ell, b):
    return sum(Fraction(int(legendre_symbol(prime(k + 1), ell) == -1), b ** (k + 1))
               for k in range(N))


if __name__ == "__main__":
    for b in (2, 3, 10):
        show(f"rho_{b}", rho(b), b)
    for ell in (3, 5, 7, 11):
        show(f"lambda_({ell},2)", legendre_constant(ell, 2), 2)
    show("lambda_(3,3)", legendre_constant(3, 3), 3)
