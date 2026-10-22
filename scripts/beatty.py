#!/usr/bin/env python3
"""The Beatty-Rokicki constant x = sum_k [floor(k sqrt 2) = 3 mod 4] / 2^(k+1).

Prints x to 60 decimals (certified by an exact enclosure), the first 64 binary digits, the
subword complexity p(n) of the digit sequence for n <= 20, and, for comparison, the complexity
of the Sturmian difference sequence floor((k+1) sqrt 2) - floor(k sqrt 2) - 1 and of the full
residue sequence floor(k sqrt 2) mod 4.

Exactness.  floor(k sqrt 2) = isqrt(2 k^2) exactly (integer square root), so every digit is
exact.  With A = sum_{k < N} d_k 2^(N - 1 - k), A / 2^N <= x <= (A + 1) / 2^N; the 60 printed
decimals are checked to agree at both ends.  The complexity counts are over a finite prefix of
length L = 10^6 and are lower bounds for p(n); for n <= 20 every factor of a rotation coding
recurs with bounded gaps far below L, so they are the true values (evidence, not proof).

Usage:  python3 scripts/beatty.py
Dependencies: none (standard library).  Runtime: a few seconds.
"""

from math import isqrt

N_DIGITS = 400          # binary digits for the enclosure (2^-400 < 10^-120)
N_DEC = 60              # decimals printed
L = 10 ** 6             # prefix length for subword complexity
N_MAX = 20              # largest factor length


def floor_k_sqrt2(k: int) -> int:
    """floor(k * sqrt 2), exactly."""
    return isqrt(2 * k * k)


def beatty_digit(k: int, m: int = 4, a: int = 3) -> int:
    """[floor(k sqrt 2) = a mod m]."""
    return 1 if floor_k_sqrt2(k) % m == a % m else 0


def decimals(num: int, den: int, n: int) -> str:
    """The first n decimals of num / den in [0, 1), truncated."""
    return str(num * 10 ** n // den).zfill(n)


def complexity(seq, n_max: int) -> list[int]:
    """Number of distinct factors of each length 1..n_max of the sequence seq."""
    s = "".join(map(str, seq))
    return [len({s[i:i + n] for i in range(len(s) - n + 1)}) for n in range(1, n_max + 1)]


def main() -> None:
    digits = [beatty_digit(k) for k in range(N_DIGITS)]
    a = 0
    for d in digits:
        a = 2 * a + d
    den = 2 ** N_DIGITS
    lo, hi = decimals(a, den, N_DEC), decimals(a + 1, den, N_DEC)
    assert lo == hi, "enclosure too wide"
    print(f"x = 0.{lo}")
    print("first 64 binary digits d_0..d_63:")
    print("".join(map(str, digits[:64])))

    beatty = [beatty_digit(k) for k in range(L)]
    sturm = [floor_k_sqrt2(k + 1) - floor_k_sqrt2(k) - 1 for k in range(L)]
    resid = [floor_k_sqrt2(k) % 4 for k in range(L)]
    pb, ps, pr = complexity(beatty, N_MAX), complexity(sturm, N_MAX), complexity(resid, N_MAX)
    print(f"subword complexity over a prefix of length {L}:")
    print(" n | [=3 mod 4] |  2n | Sturmian | n+1 | residue mod 4 | 4n")
    for n in range(1, N_MAX + 1):
        print(f"{n:2d} | {pb[n - 1]:10d} | {2 * n:3d} | {ps[n - 1]:8d} | {n + 1:3d} |"
              f" {pr[n - 1]:13d} | {4 * n:2d}")


if __name__ == "__main__":
    main()
