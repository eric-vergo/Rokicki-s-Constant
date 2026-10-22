#!/usr/bin/env python3
"""Size of the partial sums S(n) = sum_{k < n} chi_4(p_k) against sqrt(n).

p_0 = 2 < p_1 = 3 < ... are the primes and chi_4 is the nonprincipal character mod 4, so
-S(n + 1) = #{k < n : d_k = 1} - #{k < n : d_k = 0} for the binary digits d_k of Rokicki's
constant. RokickiConstant/General/Oscillation.lean proves S(n) != O(n^(1/2 - eps)).

For each N in 10^4 ... 10^max_exp the script prints
  max_{n <= N} |S(n)| / sqrt(n)   (attained at n = 5, S(5) = -2, for every N >= 10, so also)
  max_{N/10 < n <= N} |S(n)| / sqrt(n)   (where it is attained, and S there),
  max_{x <= p_N} |sum_{p <= x} chi_4(p)| * log(x) / sqrt(x)   (Rubinstein-Sarnak scale),
  max_{x <= p_N} |sum_{p <= x} chi_4(p)| * log(x)^2 / sqrt(x)   (the log-power refinement
      proves that this is unbounded, as is the same with log(x)^A for every A > 1),
  the proportion of n <= N with S(n) < 0   (Chebyshev's bias).

A second table gives, for the same N, the location of the (log x)^2 maximum, the same maximum
with (log x)^1.5, and the index-scale maxima max_{n <= N} |S(n)| (log n)^A / sqrt(n) for
A = 1/2 and A = 1 (the index-scale threshold of the log-power refinement is A = 1/2).

A third table gives the signed extremes min_{x <= p_N} S*(x) (log x)^A / sqrt(x) and
max_{x <= p_N} S*(x) (log x)^A / sqrt(x) for A = 1.5 and A = 2, S*(x) = sum_{p <= x} chi_4(p).
RokickiConstant/General/Landau.lean proves that the running minimum tends to -infinity for every
A > 1 (the one-sided, Chebyshev-bias direction Omega_-); the running maximum is not covered by
that theorem (Omega_+ needs a nonreal zero of L(s, chi_4)), see research/landau.md.

Usage:  python3 scripts/oscillation.py [max_exp]      (default 7; needs ~200 MB for 7)
"""
import math
import sys

import numpy as np

MAX_EXP = int(sys.argv[1]) if len(sys.argv) > 1 else 7


def primes_upto(m):
    sieve = np.ones(m + 1, dtype=bool)
    sieve[:2] = False
    sieve[4::2] = False
    for p in range(3, math.isqrt(m) + 1, 2):
        if sieve[p]:
            sieve[p * p::2 * p] = False
    return np.flatnonzero(sieve)


def main():
    n_max = 10 ** MAX_EXP
    # p_n < n (log n + log log n) for n >= 6 (Rosser)
    bound = int(n_max * (math.log(n_max) + math.log(math.log(n_max)))) + 10
    p = primes_upto(bound)[:n_max]
    chi = np.where(p % 2 == 0, 0, np.where(p % 4 == 1, 1, -1)).astype(np.int64)
    # S[n] = sum_{k < n} chi(p_k), n = 0 .. n_max
    S = np.concatenate(([0], np.cumsum(chi)))
    n = np.arange(1, n_max + 1)
    ratio = np.abs(S[1:]) / np.sqrt(n)
    # sum_{p <= x} chi(p) = S(k + 1) on [p_k, p_{k+1}); |.| log x / sqrt x is largest near x = p_k
    # (for x >= e^2), so we evaluate at the primes
    x = p.astype(np.float64)
    rs = np.abs(S[1:]) * np.log(x) / np.sqrt(x)
    rs[x < math.e ** 2] = 0.0
    # log(x)^2 / sqrt(x) is decreasing for x >= e^4
    rs2 = np.abs(S[1:]) * np.log(x) ** 2 / np.sqrt(x)
    rs2[x < math.e ** 4] = 0.0
    assert p[-1] == {4: 104723, 5: 1299689, 6: 15485863, 7: 179424673}.get(MAX_EXP, p[-1])
    print(f"{'N':>10} {'max_(n<=N)':>10} {'max_(N/10<n<=N)':>15} {'at n':>10} {'S(n)':>7} "
          f"{'max |S| log x/sqrt x':>21} {'max |S| log^2 x/sqrt x':>23} {'P(S<0)':>8}")
    for e in range(4, MAX_EXP + 1):
        N = 10 ** e
        m = float(ratio[:N].max())
        i = N // 10 + int(np.argmax(ratio[N // 10:N]))
        j = int(np.argmax(rs[:N]))
        j2 = int(np.argmax(rs2[:N]))
        neg = float(np.mean(S[1:N + 1] < 0))
        print(f"{N:>10} {m:>10.4f} {ratio[i]:>15.4f} {i + 1:>10} {int(S[i + 1]):>7} "
              f"{rs[j]:>21.4f} {rs2[j2]:>23.4f} {neg:>8.4f}")

    rs15 = np.abs(S[1:]) * np.log(x) ** 1.5 / np.sqrt(x)
    rs15[x < math.e ** 3] = 0.0
    nn = n.astype(np.float64)
    ix = {A: np.abs(S[1:]) * np.log(nn) ** A / np.sqrt(nn) for A in (0.5, 1.0)}
    for A in ix:
        ix[A][nn < math.e ** (2 * A) + 1] = 0.0
    print()
    print(f"{'N':>10} {'argmax log^2: x':>16} {'S':>7} {'max |S| log^1.5 x/sqrt x':>25} "
          f"{'max |S(n)| log^0.5 n/sqrt n':>28} {'max |S(n)| log n/sqrt n':>24}")
    for e in range(4, MAX_EXP + 1):
        N = 10 ** e
        j2 = int(np.argmax(rs2[:N]))
        print(f"{N:>10} {int(p[j2]):>16} {int(S[j2 + 1]):>7} {rs15[:N].max():>25.4f} "
              f"{ix[0.5][:N].max():>28.4f} {ix[1.0][:N].max():>24.4f}")

    # signed extremes of S*(x) (log x)^A / sqrt(x); (log x)^A / sqrt(x) decreases for x >= e^(2A),
    # so on [p_k, p_{k+1}) the extreme of either sign is at x = p_k
    sg = {A: S[1:] * np.log(x) ** A / np.sqrt(x) for A in (1.5, 2.0)}
    for A in sg:
        sg[A][x < math.e ** (2 * A)] = 0.0
    print()
    print(f"{'N':>10} {'min S* log^1.5/sqrt':>20} {'min S* log^2/sqrt':>18} {'at x':>10} "
          f"{'max S* log^1.5/sqrt':>20} {'max S* log^2/sqrt':>18} {'at x':>10}")
    for e in range(4, MAX_EXP + 1):
        N = 10 ** e
        jm = int(np.argmin(sg[2.0][:N]))
        jM = int(np.argmax(sg[2.0][:N]))
        print(f"{N:>10} {sg[1.5][:N].min():>20.4f} {sg[2.0][:N].min():>18.4f} {int(p[jm]):>10} "
              f"{sg[1.5][:N].max():>20.4f} {sg[2.0][:N].max():>18.4f} {int(p[jM]):>10}")


if __name__ == "__main__":
    main()
