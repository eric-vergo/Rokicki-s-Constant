#!/usr/bin/env python3
"""The Rokicki constant of an elliptic curve: rho_E = sum_k [a_{p_k}(E) < 0] / 2^(k+1).

Numerics for research/elliptic.md (Round 4, item 4 of research/PROGRAM.md).  p_0 = 2 < p_1 = 3 < ...
are all the primes, and a_p = p + 1 - #E~(F_p) for the reduction E~ of the minimal model, counted
with its singular point if any (so a_p = 0, +1, -1 for additive, split, nonsplit reduction).  The
digit is 1 exactly when E~ has more than p + 1 points.

The script prints, for X = 10^6 (all 78498 primes below 10^6):

  1. a_p for the five non-CM curves 11a1, 14a1, 37a1, 389a1, 5077a1 by the Legendre sum
     a_p = -sum_x ((4x^3 + b2 x^2 + 2 b4 x + b6) / p) (numpy, multiprocessing), and for the CM
     curves y^2 = x^3 + x (64a), y^2 = x^3 - x (32a), y^2 = x^3 + 1 (36a), y^2 + y = x^3 (27a)
     by the classical formulas through p = a^2 + b^2, p = t^2 + 3 s^2, 4p = L^2 + 27 M^2, checked
     against the Legendre sum for p < 10^4.  Checks: Hasse bound, torsion congruences, and the
     Fricke involution of each weight-2 form (level N and root number W), L(1), L'(1).
  2. rho_E to 40 decimals from an exact enclosure A/2^200 <= rho_E <= (A+1)/2^200, and the first
     64 digits.
  3. the sign race S_E(x) = sum_{p<=x} sgn a_p at x = 10^4, 10^5, 10^6 with its normalizations,
     the time spent negative, sign changes, digit density; the log-mean of S_E/pi(sqrt x) over
     [10^4, 10^6].
  4. CM curves: the Bateman-Horn line model (exact lattice sums to 10^6, integrals to 10^12),
     whose leading terms are +sqrt(x)/(2 pi) (64a), +sqrt(x)/(6 pi) (36a), -sqrt(x)/(6 pi) (27a);
     root numbers of the Hecke characters psi^j (j odd <= 41) of 36a and 27a by the Fricke test,
     and the mode sums; then all four CM curves to XCM = 10^9 by lattice enumeration (the race,
     the line model P(x), the mode model Q(x), the mode biases).
  5. non-CM curves: the Chebyshev-U expansion sgn(cos t) = sum_{j odd} c_j U_j(cos t), the
     predicted bias B_E (prime squares + central zeros, root numbers W(Sym^j E) = (-2/j) W(E)),
     a numerical check of W(Sym^3 E) and of L(1/2, Sym^3 E), the mode sums, the "discreteness"
     term Delta_E coming from rational torsion, and the race sum a_p/sqrt p (Sarnak: 1/2 - r).
  6. the quadratic twist families of 11a1 and 37a1 (|d| <= 150): root numbers, analytic ranks
     (from L(1), L'(1)), observed sign-race bias against B.
  7. residue classes p mod N, subword complexity and block frequencies (L <= 10), consecutive
     repeats.
  8. congruence (Chebotarev) digits: densities, the defect |C| - nu(C) in GL_2(F_l) (l <= 7) that
     decides the project's parity method, and the observed biases.

Exactness: every a_p is an exact integer; the digits and the enclosures of rho_E are exact.  All
biases, means and fits are numerical evidence over x <= 10^6 (10^9 for the CM curves), nothing more.

Dependencies: numpy, mpmath.  Runtime: about 3 minutes with 24 processes (the Legendre sums take
about 85 s of it); peak resident memory about 9 GB, from the 10^9 sieve and lattice of section 4b
(--xcm 1e8 needs far less).
Usage: python3 scripts/elliptic.py [--xmax 1e6] [--workers 24] [--xcm 1e9]
"""

import argparse
import math
import sys
import time
from multiprocessing import Pool

import mpmath
import numpy as np
from mpmath import mp, mpf

sys.set_int_max_str_digits(0)
T0 = time.time()

NBITS = 200          # binary digits for the enclosure of rho_E
NDEC = 40            # certified decimals printed

# (a1, a2, a3, a4, a6), conductor, rank (Cremona's tables; checked below via W and L-values)
NONCM = {
    "11a1": ((0, -1, 1, -10, -20), 11, 0, 5),
    "14a1": ((1, 0, 1, 4, -6), 14, 0, 6),
    "37a1": ((0, 0, 1, -1, 0), 37, 1, 1),
    "389a1": ((0, 1, 1, -2, 0), 389, 2, 1),
    "5077a1": ((0, 0, 1, -7, 6), 5077, 3, 1),
}                    # last field: order of the rational torsion subgroup
CM = {
    "64a": ((0, 0, 0, 1, 0), 64, "y^2 = x^3 + x"),
    "32a": ((0, 0, 0, -1, 0), 32, "y^2 = x^3 - x"),
    "36a": ((0, 0, 0, 0, 1), 36, "y^2 = x^3 + 1"),
    "27a": ((0, 0, 1, 0, 0), 27, "y^2 + y = x^3  (= y^2 = x^3 + 16; isogenous to y^2 = x^3 - 432)"),
}


def log(msg=""):
    print(msg, flush=True)


# ---------------------------------------------------------------------------------------------
# Primes and a_p
# ---------------------------------------------------------------------------------------------

def primes_below(n):
    s = np.ones(n, dtype=bool)
    s[:2] = False
    s[4::2] = False
    for p in range(3, math.isqrt(n) + 1, 2):
        if s[p]:
            s[p * p::2 * p] = False
    return np.nonzero(s)[0].astype(np.int64)


def binv(a):
    a1, a2, a3, a4, a6 = a
    return a1 * a1 + 4 * a2, 2 * a4 + a1 * a3, a3 * a3 + 4 * a6


def ap_two(a):
    """a_2 = 3 - #E~(F_2) on the long Weierstrass model (singular point counted)."""
    a1, a2, a3, a4, a6 = a
    n = 1 + sum(1 for x in (0, 1) for y in (0, 1)
                if (y * y + a1 * x * y + a3 * y - x ** 3 - a2 * x * x - a4 * x - a6) % 2 == 0)
    return 3 - n


def _legendre_worker(args):
    """For each odd prime p and each cubic f = 4x^3 + b2 x^2 + 2 b4 x + b6: a_p = -sum_x (f(x)/p)
    and the number of roots of f mod p (the 2-torsion of E~(F_p))."""
    ps, bs = args
    ap = np.zeros((len(bs), len(ps)), dtype=np.int64)
    nr = np.zeros((len(bs), len(ps)), dtype=np.int64)
    P = int(ps.max()) + 1
    X = np.arange(P, dtype=np.int64)
    tb = np.empty(P, dtype=np.int64)
    x2b = np.empty(P, dtype=np.int64)
    x3b = np.empty(P, dtype=np.int64)
    fb = np.empty(P, dtype=np.int64)
    chib = np.empty(P, dtype=np.int8)
    gb = np.empty(P, dtype=np.int8)
    for i, p in enumerate(ps.tolist()):
        x, x2, x3, f, chi, t, g = X[:p], x2b[:p], x3b[:p], fb[:p], chib[:p], tb[:p], gb[:p]
        np.multiply(x, x, out=t)
        np.remainder(t, p, out=x2)
        np.multiply(x2, x, out=t)
        np.remainder(t, p, out=x3)
        chi.fill(-1)
        chi[x2] = 1
        chi[0] = 0
        for c, (b2, b4x2, b6) in enumerate(bs):
            np.multiply(x3, 4, out=f)
            if b2:
                np.multiply(x2, b2, out=t)
                np.add(f, t, out=f)
            if b4x2:
                np.multiply(x, b4x2, out=t)
                np.add(f, t, out=f)
            if b6:
                np.add(f, b6, out=f)
            np.remainder(f, p, out=f)
            np.take(chi, f, out=g)
            ap[c, i] = -int(g.sum(dtype=np.int64))
            nr[c, i] = int(np.count_nonzero(f == 0))
    return ap, nr


def legendre_ap(ps, curves, workers):
    """a_p and #roots for every prime in ps (p = 2 by direct count; nroots[2] = -1)."""
    bs = []
    for a in curves:
        b2, b4, b6 = binv(a)
        bs.append((b2, 2 * b4, b6))
    odd = ps[ps > 2]
    nch = max(1, workers * 8)
    chunks = [odd[i::nch] for i in range(nch) if len(odd[i::nch])]
    if workers > 1 and len(odd) > 2000:
        with Pool(workers) as pool:
            res = pool.map(_legendre_worker, [(c, bs) for c in chunks])
    else:
        res = [_legendre_worker((c, bs)) for c in chunks]
    ap = np.zeros((len(curves), len(ps)), dtype=np.int64)
    nr = np.full((len(curves), len(ps)), -1, dtype=np.int64)
    off = int(np.sum(ps == 2))
    for i, (r, n) in enumerate(res):
        ap[:, off + i::nch] = r
        nr[:, off + i::nch] = n
    if off:
        for c, a in enumerate(curves):
            ap[c, 0] = ap_two(a)
    return ap, nr


def two_square_tables(X):
    """p = a^2 + b^2 (a odd > 0, b even > 0); p = t^2 + 3 s^2 (t, s > 0); 4p = L^2 + 27 M^2 (L, M > 0)."""
    R = math.isqrt(X) + 2
    A = {}
    a = np.arange(1, R, 2)
    b = np.arange(2, R, 2)
    n = a[:, None] ** 2 + b[None, :] ** 2
    ii, jj = np.nonzero(n < X)
    for i, j in zip(ii.tolist(), jj.tolist()):
        A.setdefault(int(n[i, j]), (int(a[i]), int(b[j])))
    T = {}
    t = np.arange(1, R)
    s = np.arange(1, R)
    n = t[:, None] ** 2 + 3 * s[None, :] ** 2
    ii, jj = np.nonzero(n < X)
    for i, j in zip(ii.tolist(), jj.tolist()):
        T.setdefault(int(n[i, j]), (int(t[i]), int(s[j])))
    E = {}
    L = np.arange(1, 2 * R)
    M = np.arange(1, R)
    n = L[:, None] ** 2 + 27 * M[None, :] ** 2
    ii, jj = np.nonzero((n < 4 * X) & (n % 4 == 0))
    for i, j in zip(ii.tolist(), jj.tolist()):
        E.setdefault(int(n[i, j]) // 4, (int(L[i]), int(M[j])))
    return A, T, E


def cm_fast(ps):
    """Classical formulas (Gauss, Jacobi; Ireland-Rosen ch. 18), all primes p in ps:
       64a  y^2 = x^3 + x : p = a^2 + b^2, a odd > 0: a_p = 2 a chi_4(a);   a_p = 0 for p = 3 mod 4
       32a  y^2 = x^3 - x : a_p = 2 a chi_4(a) chi_8(p)  (= 2 Re pi_0, pi_0 = 1 mod 2+2i)
       36a  y^2 = x^3 + 1 : p = t^2 + 3 s^2, t = 1 mod 3: a_p = 2t;      a_p = 0 for p = 2 mod 3
       27a  y^2 + y = x^3 : 4p = L^2 + 27 M^2, L = 2 mod 3: a_p = L."""
    X = int(ps.max()) + 1
    A, T, E = two_square_tables(X)
    out = {k: np.zeros(len(ps), dtype=np.int64) for k in CM}
    for i, p in enumerate(ps.tolist()):
        if p % 4 == 1:
            a, b = A[p]
            c4 = 1 if a % 4 == 1 else -1
            c8 = 1 if p % 8 == 1 else -1
            out["64a"][i] = 2 * a * c4
            out["32a"][i] = 2 * a * c4 * c8
        if p % 3 == 1:
            t, s = T[p]
            out["36a"][i] = 2 * (t if t % 3 == 1 else -t)
            L, M = E[p]
            out["27a"][i] = L if L % 3 == 2 else -L
    return out


def cm_extended(X):
    """a_p for the four CM curves and every prime p < X (X up to ~10^8), by enumerating the lattice
    points of the quadratic forms row by row and testing primality in a sieve."""
    half = np.ones(X // 2, dtype=bool)           # half[k]: 2k+1 prime
    half[0] = False
    for k in range(1, (math.isqrt(X) - 1) // 2 + 1):
        if half[k]:
            p = 2 * k + 1
            half[p * p // 2::p] = False
    P = np.concatenate([[2], 2 * np.nonzero(half)[0] + 1]).astype(np.int64)
    val = np.zeros(X, dtype=np.int32)
    out = {}

    def isprime(n):
        return (n % 2 == 1) & half[np.minimum(n // 2, len(half) - 1)] & (n < X)

    # 64a and 32a: p = a^2 + b^2, a odd, b even
    for name in ("64a", "32a"):
        val.fill(0)
        for a in range(1, math.isqrt(X) + 1, 2):
            b = np.arange(2, math.isqrt(max(X - a * a, 0)) + 1, 2, dtype=np.int64)
            n = a * a + b * b
            n = n[isprime(n)]
            c4 = 1 if a % 4 == 1 else -1
            v = 2 * a * c4
            if name == "32a":
                val[n] = np.where(n % 8 == 1, v, -v)
            else:
                val[n] = v
        out[name] = val[P].copy()
    # 36a: p = t^2 + 3 s^2, a_p = 2t with t = 1 mod 3
    val.fill(0)
    for t in range(1, math.isqrt(X) + 1):
        if t % 3 == 0:
            continue
        sv = np.arange(1, math.isqrt(max(X - t * t, 0) // 3) + 1, dtype=np.int64)
        n = t * t + 3 * sv * sv
        n = n[isprime(n)]
        val[n] = 2 * t if t % 3 == 1 else -2 * t
    out["36a"] = val[P].copy()
    # 27a: 4p = L^2 + 27 M^2, a_p = L with L = 2 mod 3
    val.fill(0)
    for L in range(1, 2 * math.isqrt(X) + 2):
        if L % 3 == 0:
            continue
        Mv = np.arange(2 - L % 2, math.isqrt(max(4 * X - L * L, 0) // 27) + 1, 2, dtype=np.int64)
        n4 = L * L + 27 * Mv * Mv
        n = n4 // 4
        n = n[isprime(n)]
        val[n] = L if L % 3 == 2 else -L
    out["27a"] = val[P].copy()
    del val
    return P, out


# ---------------------------------------------------------------------------------------------
# Coefficients a_n, Fricke test, L-values
# ---------------------------------------------------------------------------------------------

def spf_table(n):
    spf = np.zeros(n + 1, dtype=np.int64)
    for p in range(2, n + 1):
        if spf[p] == 0:
            spf[p::p][spf[p::p] == 0] = p
    return spf


def an_from_ap(apmap, N, nmax, spf):
    """a_n, n <= nmax, from a_p (dict p -> a_p): Hecke recursion at good p, a_{p^k} = a_p^k at bad p."""
    an = np.zeros(nmax + 1)
    an[1] = 1.0
    ppow = {}
    for n in range(2, nmax + 1):
        p = int(spf[n])
        m, k = n, 0
        while m % p == 0:
            m //= p
            k += 1
        key = (p, k)
        if key not in ppow:
            a = apmap[p]
            vals = [1.0, float(a)]
            for kk in range(2, k + 1):
                vals.append(a * vals[-1] - (0 if N % p == 0 else p) * vals[-2])
            for kk in range(len(vals)):
                ppow[(p, kk)] = vals[kk]
        an[n] = ppow[key] * an[m]
    return an


def fricke_weight2(an, N):
    """phi(1/(N y)) / (N y^2 phi(y)) at two points; equals W for the right level N."""
    n = np.arange(1, len(an))
    a = an[1:]

    def phi(y):
        return np.sum(a * np.exp(-2 * np.pi * n * y))

    r = [phi(1 / (N * y)) / (N * y * y * phi(y)) for y in (1.1 / math.sqrt(N), 1.3 / math.sqrt(N))]
    return r


def e1_vec(z):
    """Exponential integral E_1(z), z > 0 (series for z < 1, continued fraction otherwise)."""
    z = np.asarray(z, dtype=float)
    out = np.empty_like(z)
    sm = z < 1
    zs = z[sm]
    s = np.zeros_like(zs)
    term = np.ones_like(zs)
    for k in range(1, 40):
        term = term * (-zs) / k
        s += -term / k
    out[sm] = -np.euler_gamma - np.log(zs) + s
    zl = z[~sm]
    f = np.zeros_like(zl)
    for k in range(80, 0, -1):
        f = k / (1 + k / (zl + f))
    out[~sm] = np.exp(-zl) / (zl + f)
    return out


def lvalues(an, N, W):
    """L(E,1) if W = +1, L'(E,1) if W = -1 (classical rapidly convergent series)."""
    n = np.arange(1, len(an))
    a = an[1:]
    z = 2 * np.pi * n / math.sqrt(N)
    keep = z < 700
    if W == 1:
        return 2 * np.sum(a[keep] / n[keep] * np.exp(-z[keep]))
    return 2 * np.sum(a[keep] / n[keep] * e1_vec(z[keep]))


def kron_primes(d, ps):
    """Kronecker symbol (d/p) for primes p (vectorized Euler criterion)."""
    out = np.zeros(len(ps), dtype=np.int64)
    odd = ps > 2
    p = ps[odd]
    base = d % p
    e = (p - 1) // 2
    r = np.ones_like(p)
    b = base.copy()
    while np.any(e > 0):
        m = (e & 1) == 1
        r[m] = r[m] * b[m] % p[m]
        b = b * b % p
        e >>= 1
    out[odd] = np.where(r == 1, 1, np.where(r == 0, 0, -1))
    if np.any(~odd):
        out[~odd] = 0 if d % 2 == 0 else (1 if d % 8 in (1, 7) else -1)
    return out


# ---------------------------------------------------------------------------------------------
# Symmetric cube
# ---------------------------------------------------------------------------------------------

def bessel_k(nu, z):
    """K_nu(z), z > 0, by the trapezoidal rule on int_0^inf exp(-z cosh t) cosh(nu t) dt."""
    z = np.atleast_1d(np.asarray(z, dtype=float))
    h = 0.05
    t = np.arange(0, 12, h)
    w = np.full(len(t), h)
    w[0] = h / 2
    ch = np.cosh(t)
    cw = np.cosh(nu * t) * w
    out = np.empty_like(z)
    for i in range(0, len(z), 20000):
        zz = z[i:i + 20000]
        out[i:i + 20000] = (np.exp(-np.outer(zz, ch)) * cw).sum(axis=1)
    return out


def sym3_coeffs(apmap, N, nmax, ps_small):
    """lambda(n) of L(s, Sym^3 E), unitary normalization; semistable E (bad p multiplicative)."""
    lam = np.zeros(nmax + 1)
    lam[1] = 1.0
    for p in ps_small.tolist():
        if p > nmax:
            break
        a = apmap[p]
        vals = [1.0]
        if N % p == 0:
            x = a * p ** -1.5
            while p ** len(vals) <= nmax:
                vals.append(vals[-1] * x)
        else:
            t = a / math.sqrt(p)
            e1 = t ** 3 - 2 * t
            e2 = t ** 4 - 3 * t * t + 2
            e = (e1, e2, e1, 1.0)
            while p ** len(vals) <= nmax:
                k = len(vals)
                vals.append(sum((-1) ** i * e[i] * vals[k - 1 - i] for i in range(4) if k - 1 - i >= 0))
        pk = p
        for k in range(1, len(vals)):
            idx = np.arange(pk, nmax + 1, pk)
            idx = idx[(idx // pk) % p != 0]
            lam[idx] = lam[idx // pk] * vals[k]
            pk *= p
    return lam


def sym3_test(lam, N):
    """Theta(y) = sum lambda(n) k(n y / sqrt N), k(t) = 8 pi^2 t K_1(4 pi sqrt t) (inverse Mellin of
    Gamma(s+1/2) Gamma(s+3/2) (2 pi)^(-2s)); Lambda(s) = W Lambda(1-s) <=> Theta(1/y) = W y Theta(y).
    Returns the two ratios and L(1/2, Sym^3) = 2 pi Lambda_G(1/2) / N^(1/4) computed as if W = +1,
    with Lambda_G(1/2) = 2 sum lambda(n) 4 pi sqrt(c) K_2(4 pi sqrt c), c = n / sqrt N."""
    n = np.arange(1, len(lam))
    l = lam[1:]

    def theta(y):
        t = n * y / math.sqrt(N)
        keep = 4 * np.pi * np.sqrt(t) < 700
        return np.sum(l[keep] * 8 * np.pi ** 2 * t[keep] * bessel_k(1, 4 * np.pi * np.sqrt(t[keep])))

    ratios = [theta(1 / y) / (y * theta(y)) for y in (1.1, 1.3)]
    c = n / math.sqrt(N)
    keep = 4 * np.pi * np.sqrt(c) < 700
    lam_half = 2 * np.sum(l[keep] * 4 * np.pi * np.sqrt(c[keep]) * bessel_k(2, 4 * np.pi * np.sqrt(c[keep])))
    return ratios, 2 * np.pi * lam_half / N ** 0.25


# ---------------------------------------------------------------------------------------------
# Hecke characters of 27a and 36a: theta series, Fricke test, central values
# ---------------------------------------------------------------------------------------------

def eisenstein_points(kind, M):
    """Generators x + y w (w = e^{2 pi i/3}) of norm <= M, one per ideal coprime to the conductor:
    '27a': alpha = 1 mod 3;  '36a': beta = 1 mod 2 sqrt(-3)."""
    R = 2 * math.isqrt(M) + 2
    pts = []
    for x in range(-R, R + 1):
        for y in range(-R, R + 1):
            n = x * x - x * y + y * y
            if n == 0 or n > M:
                continue
            if kind == "27a" and not (x % 3 == 1 and y % 3 == 0):
                continue
            if kind == "36a" and not (x % 2 == 1 and y % 2 == 0 and (x + y) % 3 == 1):
                continue
            pts.append((x, y, n))
    return pts


def hecke_root_numbers(kind, jmax=41, M=1500, levels=(9, 27, 36, 81, 108, 144, 243, 324)):
    mp.dps = 50
    pts = eisenstein_points(kind, M)
    w3 = mpmath.mpc(-0.5, mpmath.sqrt(3) / 2)
    out = {}
    for j in range(1, jmax + 1, 2):
        a = [mpf(0)] * (M + 1)
        for x, y, n in pts:
            a[n] += ((x + y * w3) ** j).real
        nz = [k for k in range(1, M + 1) if abs(a[k]) > 0.5]
        found = None
        wt = j + 1
        for N in levels:
            def phi(y):
                return mp.fsum(a[k] * mp.e ** (-2 * mp.pi * k * y) for k in nz)
            rs = [phi(1 / (N * y)) / (mpf(N) ** (mpf(wt) / 2) * y ** wt * phi(y))
                  for y in (mpf("0.8") / mp.sqrt(N), mpf("1.25") / mp.sqrt(N))]
            if abs(abs(rs[0]) - 1) < 1e-15 and abs(rs[0] - rs[1]) < 1e-15:
                found = (N, int(mp.nint(rs[0].real)))
                break
        if found is None:
            out[j] = (None, None, None)
            continue
        N, W = found
        cv = (1 + W) * mp.fsum(a[k] * (2 * mp.pi * k) ** (-mpf(wt) / 2) *
                               mp.gammainc(mpf(wt) / 2, 2 * mp.pi * k / mp.sqrt(N)) for k in nz)
        out[j] = (N, W, float(cv))
    return out


# ---------------------------------------------------------------------------------------------
# Bateman-Horn line model for the CM curves
# ---------------------------------------------------------------------------------------------

def chi_m3(n):
    n = np.asarray(n)
    r = n % 3
    return np.where(r == 0, 0, np.where(r == 1, 1, -1))


def chi_m4(n):
    n = np.asarray(n)
    return np.where(n % 2 == 0, 0, np.where(n % 4 == 1, 1, -1))


def logw_sieve(n, chi, qmin):
    """log w(m) = sum_{q | m, q >= qmin prime} log((q-1)/(q-1-chi(q)))."""
    lw = np.zeros(n + 1)
    for q in primes_below(n + 1).tolist():
        if q < qmin:
            continue
        c = int(chi(q))
        lw[q::q] += math.log((q - 1) / (q - 1 - c))
    return lw


def bh_constants(Q=10 ** 7):
    """H4 = 2 prod_{q odd} (1 - chi_4(q)/(q-1));  H3 = prod_{q >= 5} (1 - chi_-3(q)/(q-1)),
    via the absolutely convergent ratio to prod (1 - chi(q)/q) = known L-values."""
    qs = primes_below(Q)
    q4 = qs[qs > 2].astype(float)
    c4 = chi_m4(qs[qs > 2]).astype(float)
    r4 = np.prod((1 - c4 / (q4 - 1)) / (1 - c4 / q4))
    H4 = 2 * r4 * (4 / math.pi)                      # prod_{q odd}(1 - chi_4(q)/q) = 1/L(1,chi_4)
    q3 = qs[qs > 3].astype(float)
    c3 = chi_m3(qs[qs > 3]).astype(float)
    r3 = np.prod((1 - c3 / (q3 - 1)) / (1 - c3 / q3))
    H3 = r3 * (2 * math.sqrt(3) / math.pi)           # prod_{q>=5}(1 - chi(q)/q) = (2/3)/L(1,chi_-3)
    return H4, H3


def bh_lattice(kind, xs, H4, H3):
    """Exact lattice sum P(x) = sum over lattice points (line, k) with value v <= x of
    sign(line) * C(line) / log v, for x in xs (all <= 10^7)."""
    X = int(max(xs))
    if kind == "64a":                   # p = a^2 + 4 c^2, sign chi_4(a), C = H4 w(a)
        R = math.isqrt(X) + 1
        lw = logw_sieve(R, lambda q: 1 if q % 4 == 1 else -1, 3)
        a = np.arange(1, R, 2)
        sgn = chi_m4(a) * H4 * np.exp(lw[a])
        c = np.arange(1, R // 2 + 2)
        v = a[:, None] ** 2 + 4 * c[None, :] ** 2
        wgt = sgn[:, None] * np.ones_like(v, dtype=float)
    elif kind == "36a":                 # p = t^2 + 3 s^2, sign chi_-3(t), C = (3/2) H3 w(t)
        R = math.isqrt(X) + 1
        lw = logw_sieve(R, lambda q: 1 if q % 3 == 1 else -1, 5)
        t = np.arange(1, R)
        sgn = chi_m3(t) * 1.5 * H3 * np.exp(lw[t])
        s = np.arange(1, R)
        v = t[:, None] ** 2 + 3 * s[None, :] ** 2
        wgt = sgn[:, None] * np.ones_like(v, dtype=float)
    else:                               # 27a: 4p = L^2 + 27 M^2, M = L mod 2, sign -chi_-3(L),
        R = 2 * math.isqrt(X) + 2       # C = (3/2) H3 c_2(L) w(L), c_2 = 2 (L odd), 1 (L even)
        lw = logw_sieve(R, lambda q: 1 if q % 3 == 1 else -1, 5)
        L = np.arange(1, R)
        c2 = np.where(L % 2 == 1, 2.0, 1.0)
        sgn = -chi_m3(L) * 1.5 * H3 * c2 * np.exp(lw[L])
        M = np.arange(1, math.isqrt(4 * X // 27) + 2)
        v4 = L[:, None] ** 2 + 27 * M[None, :] ** 2
        ok = (L[:, None] % 2) == (M[None, :] % 2)
        v = np.where(ok, v4 // 4, 0)
        wgt = sgn[:, None] * ok
    out = []
    for x in xs:
        m = (v <= x) & (v > 1) & (wgt != 0)
        out.append(float(np.sum(wgt[m] / np.log(v[m]))))
    return out


def bh_integral(kind, x, H4, H3, lw_cache):
    """P(x) beyond the sieve range: each line's sum over the second coordinate replaced by the
    integral int du / log(value) (Gauss-Legendre, 24 nodes in log u)."""
    nodes, weights = np.polynomial.legendre.leggauss(24)
    if kind == "64a":
        R = math.isqrt(int(x))
        a = np.arange(1, R, 2).astype(float)
        sgn = chi_m4(a.astype(np.int64)) * H4 * np.exp(lw_cache["64a"][a.astype(np.int64)])
        lo = np.full_like(a, 0.5)
        hi = np.floor(np.sqrt(np.maximum(x - a * a, 0)) / 2) + 0.5
        f = lambda u: a[:, None] ** 2 + 4 * u * u
        scale = 1.0
    elif kind == "36a":
        R = math.isqrt(int(x))
        a = np.arange(1, R).astype(float)
        sgn = chi_m3(a.astype(np.int64)) * 1.5 * H3 * np.exp(lw_cache["3"][a.astype(np.int64)])
        lo = np.full_like(a, 0.5)
        hi = np.floor(np.sqrt(np.maximum(x - a * a, 0) / 3)) + 0.5
        f = lambda u: a[:, None] ** 2 + 3 * u * u
        scale = 1.0
    else:
        R = 2 * math.isqrt(int(x))
        a = np.arange(1, R).astype(float)
        ai = a.astype(np.int64)
        c2 = np.where(ai % 2 == 1, 2.0, 1.0)
        sgn = -chi_m3(ai) * 1.5 * H3 * c2 * np.exp(lw_cache["3"][ai])
        lo = np.full_like(a, 0.5)
        hi = np.sqrt(np.maximum(4 * x - a * a, 0) / 27) + 0.5
        f = lambda u: (a[:, None] ** 2 + 27 * u * u) / 4
        scale = 0.5                     # M runs over one parity class
    ok = hi > lo
    a, sgn, lo, hi = a[ok], sgn[ok], lo[ok], hi[ok]
    u0, u1 = np.log(lo), np.log(hi)
    u = (u1 - u0)[:, None] / 2 * nodes[None, :] + (u1 + u0)[:, None] / 2
    c = np.exp(u)
    vals = a[:, None] ** 2
    if kind == "64a":
        vals = vals + 4 * c * c
    elif kind == "36a":
        vals = vals + 3 * c * c
    else:
        vals = (vals + 27 * c * c) / 4
    I = ((u1 - u0) / 2) * np.sum(weights[None, :] * c / np.log(vals), axis=1)
    return float(scale * np.sum(sgn * I))


# ---------------------------------------------------------------------------------------------
# Statistics helpers
# ---------------------------------------------------------------------------------------------

def race_stats(ps, sg, xs):
    """S(x) = sum_{p <= x} sg_p at each x; fraction of prefixes (natural and logarithmic) with S < 0;
    number of strict sign changes; density of ones of [sg < 0]."""
    S = np.cumsum(sg)
    rows = []
    for x in xs:
        i = int(np.searchsorted(ps, x, side="right"))
        Si = S[:i]
        neg = Si < 0
        w = 1.0 / ps[:i]
        nz = Si[Si != 0]
        changes = int(np.count_nonzero(np.sign(nz[1:]) != np.sign(nz[:-1])))
        rows.append(dict(x=x, n=i, S=int(S[i - 1]), frac_neg=float(np.mean(neg)),
                         lfrac_neg=float(np.sum(w[neg]) / np.sum(w)), changes=changes,
                         ones=float(np.mean(sg[:i] < 0)), zeros=int(np.count_nonzero(sg[:i] == 0))))
    return S, rows


def pi_sqrt(ps, x):
    return int(np.searchsorted(ps, math.sqrt(x), side="right"))


_LM_CACHE = {}


def logmean_norm(ps, S, lo=1e4):
    """Logarithmic mean over x in [lo, X] of S(x)/pi(sqrt x) (S sampled at the primes, weight 1/p)."""
    key = (id(ps), len(ps), lo)
    if key not in _LM_CACHE:
        m = ps >= lo
        pis = np.searchsorted(ps, np.sqrt(ps[m]), side="right")
        w = 1.0 / ps[m]
        _LM_CACHE[key] = (m, w / pis, np.sum(w))
    m, wp, sw = _LM_CACHE[key]
    return float(np.sum(S[m] * wp) / sw)


def enclosure(digits, nbits=NBITS, ndec=NDEC):
    A = 0
    for d in digits[:nbits]:
        A = 2 * A + int(d)
    lo = A * 10 ** ndec // 2 ** nbits
    hi = (A + 1) * 10 ** ndec // 2 ** nbits
    s = str(lo).rjust(ndec, "0")
    return A, lo == hi, "0." + s


def block_chi2(d, L):
    """Non-overlapping blocks of length L against i.i.d. Bernoulli(q_hat): chi^2, d.o.f., z (Wilson-Hilferty)."""
    q = float(np.mean(d))
    nb = len(d) // L
    B = d[:nb * L].reshape(nb, L)
    code = B @ (1 << np.arange(L - 1, -1, -1))
    cnt = np.bincount(code, minlength=2 ** L).astype(float)
    ones = np.array([bin(c).count("1") for c in range(2 ** L)])
    exp_ = nb * q ** ones * (1 - q) ** (L - ones)
    chi2 = float(np.sum((cnt - exp_) ** 2 / exp_))
    dof = 2 ** L - 2
    z = ((chi2 / dof) ** (1 / 3) - (1 - 2 / (9 * dof))) / math.sqrt(2 / (9 * dof))
    return chi2, dof, z


def complexity(d, L):
    code = np.zeros(len(d) - L + 1, dtype=np.int64)
    for i in range(L):
        code = 2 * code + d[i:len(d) - L + 1 + i]
    return len(np.unique(code))


def repeat_stat(d):
    q = float(np.mean(d))
    same = float(np.mean(d[1:] == d[:-1]))
    e = q * q + (1 - q) * (1 - q)
    z = (same - e) / math.sqrt(e * (1 - e) / (len(d) - 1))
    return same, e, z


# ---------------------------------------------------------------------------------------------
# Chebyshev-U expansion of sgn(cos t) and the predicted bias
# ---------------------------------------------------------------------------------------------

def cj(j):
    """sgn(cos t) = sum_{j odd} c_j U_j(cos t) in L^2(Sato-Tate):
    c_j = (2/pi) (-1)^((j-1)/2) (1/j + 1/(j+2))."""
    return (2 / math.pi) * (-1) ** ((j - 1) // 2) * (1 / j + 1 / (j + 2))


def kron_m2(j):
    """(-2/j) for odd j."""
    return 1 if j % 8 in (1, 3) else -1


_TAILS = {}


def _tails(J=400001):
    if not _TAILS:
        _TAILS["pos"] = sum(cj(j) * kron_m2(j) for j in range(3, J, 2))
        _TAILS["neg"] = sum(cj(j) * kron_m2(j) * -((-1) ** ((j - 1) // 2)) for j in range(3, J, 2))
    return _TAILS


def predicted_B(r, W, twist_sign=1, chiN=1):
    """B = c_1 (1/2 - r) + (1/2) sum_{j >= 3 odd} c_j W_j, with W_j = W(Sym^j E_d) =
    (-2/j) W(E) chi_d(N) * (1 if d > 0 else -(-1)^((j-1)/2)) for a twist E_d of a semistable E
    (d = 1: W_j = (-2/j) W(E)); here W is W(E) of the untwisted curve and r the rank of E_d."""
    t = _tails()
    tail = W * chiN * (t["pos"] if twist_sign > 0 else t["neg"])
    return cj(1) * (0.5 - r) + 0.5 * tail


def torsion_mu(m):
    """Discreteness term: mean over units c mod m of mu(c+1 mod m), mu(r) = m - 2r (0 < r < m), mu(0) = 0;
    Delta_E = mu / pi in units of pi(sqrt x) (rational m-torsion forces a_p = p + 1 mod m)."""
    if m <= 2:
        return 0.0
    vals = []
    for c in range(1, m):
        if math.gcd(c, m) == 1:
            r = (c + 1) % m
            vals.append(0 if r == 0 else m - 2 * r)
    return sum(vals) / len(vals)


def discreteness_model(ps, a, Mod):
    """Lang-Trotter-type model: E[sgn a_p | p] with a_p ~ sqrt(4p - a^2) * q_c(a mod Mod), q_c the
    empirical distribution of a_p mod Mod in the class p = c mod Mod.  Returns cumulative sum."""
    E = np.zeros(len(ps))
    for c in range(Mod):
        if math.gcd(c, Mod) != 1:
            continue
        sel = np.nonzero((ps % Mod == c) & (ps > 3))[0]
        h = np.bincount(a[sel] % Mod, minlength=Mod).astype(float)
        h /= h.sum()
        for i in sel.tolist():
            p = int(ps[i])
            A = np.arange(-int(2 * math.sqrt(p)), int(2 * math.sqrt(p)) + 1)
            w = np.sqrt(np.maximum(4 * p - A * A, 0)) * h[A % Mod]
            E[i] = np.sum(np.sign(A) * w) / np.sum(w)
    return np.cumsum(E)


# ---------------------------------------------------------------------------------------------
# GL_2(F_l): Chebotarev digits and the defect |C| - nu(C)
# ---------------------------------------------------------------------------------------------

def gl2_defects(l):
    G = [(a, b, c, d) for a in range(l) for b in range(l) for c in range(l) for d in range(l)
         if (a * d - b * c) % l]
    sq = [((a * a + b * c) % l, (a * b + b * d) % l, (c * a + d * c) % l, (c * b + d * d) % l)
          for a, b, c, d in G]
    tr = lambda g: (g[0] + g[3]) % l
    dt = lambda g: (g[0] * g[3] - g[1] * g[2]) % l
    classes = {}
    for t in range(l):
        classes[f"tr = {t}"] = lambda g, t=t: tr(g) == t
    classes["det(1-g) = 0  (l | #E(F_p))"] = lambda g: (1 - tr(g) + dt(g)) % l == 0
    classes["g = 1  (p splits in Q(E[l]))"] = lambda g: g == (1, 0, 0, 1)
    out = []
    for name, f in classes.items():
        C = sum(1 for g in G if f(g))
        nu = sum(1 for h in sq if f(h))
        out.append((name, C, nu, len(G)))
    return out


# ---------------------------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------------------------

def fundamental_discriminants(D):
    out = []
    for d in range(-D, D + 1):
        if d in (0, 1):
            continue
        if d % 4 == 1:
            m = abs(d)
        elif d % 4 == 0 and (d // 4) % 4 in (2, 3):
            m = abs(d // 4)
        else:
            continue
        if any(m % (q * q) == 0 for q in range(2, math.isqrt(m) + 1)):
            continue
        out.append(d)
    return out


def main():
    ap_ = argparse.ArgumentParser()
    ap_.add_argument("--xmax", type=float, default=1e6)
    ap_.add_argument("--workers", type=int, default=24)
    ap_.add_argument("--xcm", type=float, default=1e9, help="range for the CM curves (lattice enumeration)")
    args = ap_.parse_args()
    X = int(args.xmax)
    ps = primes_below(X)
    xs = [x for x in (1e4, 1e5, 1e6) if x <= X]
    log(f"# Elliptic Rokicki constants: all {len(ps)} primes below {X:.0e}\n")

    # -----------------------------------------------------------------------------------------
    log("## 1. a_p\n")
    t = time.time()
    names = list(NONCM)
    apL, nrL = legendre_ap(ps, [NONCM[k][0] for k in names], args.workers)
    AP = {k: apL[i] for i, k in enumerate(names)}
    NR = {k: nrL[i] for i, k in enumerate(names)}
    log(f"Legendre sums for {len(names)} non-CM curves: {time.time() - t:.1f} s")
    t = time.time()
    cmf = cm_fast(ps)
    AP.update(cmf)
    log(f"CM formulas for {len(CM)} curves: {time.time() - t:.1f} s")
    small = ps[ps < 10 ** 4]
    apc, _ = legendre_ap(small, [CM[k][0] for k in CM], 1)
    for i, k in enumerate(CM):
        ok = np.array_equal(apc[i], AP[k][:len(small)])
        log(f"  {k}: classical formula == Legendre sum for all {len(small)} p < 10^4: {ok}")
        assert ok
    allnames = names + list(CM)
    conductor = {k: NONCM[k][1] for k in names}
    conductor.update({k: CM[k][1] for k in CM})
    for k in allnames:
        a = AP[k]
        assert np.all(a.astype(float) ** 2 < 4 * ps), k
    log("Hasse bound |a_p| < 2 sqrt p: holds for every curve and prime.")
    for k in names:
        m = NONCM[k][3]
        good = (conductor[k] % ps != 0) & (ps % m != 0) if m > 1 else None
        if m > 1:
            ok = np.all((AP[k][good] - ps[good] - 1) % m == 0)
            log(f"  {k}: a_p = p + 1 (mod {m}) at every good p not dividing {m} (rational {m}-torsion): {ok}")
    bad = {k: {int(p): int(AP[k][i]) for i, p in enumerate(ps) if conductor[k] % p == 0} for k in allnames}
    log("a_p at the bad primes: " + "; ".join(f"{k}: {bad[k]}" for k in allnames))
    log("first a_p (p = 2, 3, 5, ..., 29):")
    for k in allnames:
        log(f"  {k:7s} " + " ".join(f"{v:+d}" for v in AP[k][:10]))

    spf = spf_table(30000)
    apmap = {k: dict(zip(ps[:3300].tolist(), AP[k][:3300].tolist())) for k in allnames}
    log("\nFricke test phi(1/(N y)) = W N y^2 phi(y) at y = 1.1/sqrt N, 1.3/sqrt N; L-values:")
    log("| curve | N | ratios | W | L(1) or L'(1) |")
    log("|---|---|---|---|---|")
    WE = {}
    for k in allnames:
        N = conductor[k]
        an = an_from_ap(apmap[k], N, 3000, spf)
        r = fricke_weight2(an, N)
        W = int(round(r[0]))
        WE[k] = W
        lv = lvalues(an, N, W)
        log(f"| {k} | {N} | {r[0]:+.12f}, {r[1]:+.12f} | {W:+d} | {'L' if W == 1 else 'L1'}={lv:.10f} |")
    log("(analytic ranks: 11a1, 14a1: 0 (L(1) != 0); 37a1: 1 (W = -1, L'(1) != 0); 389a1: >= 2 "
        "(W = +1, L(1) = 0); 5077a1: >= 3 (W = -1, L'(1) = 0); Cremona: ranks 0, 0, 1, 2, 3)\n")

    # -----------------------------------------------------------------------------------------
    log("## 2. The constants rho_E = sum_k [a_{p_k} < 0] 2^-(k+1), p_0 = 2\n")
    log(f"| curve | rho_E (40 decimals, certified) | first 64 digits d_0 d_1 ... d_63 |")
    log("|---|---|---|")
    RHO = {}
    for k in allnames:
        d = (AP[k][:NBITS] < 0).astype(int)
        A, ok, s = enclosure(d)
        assert ok, k
        RHO[k] = (s, A)
        log(f"| {k} | {s} | {''.join(map(str, d[:64]))} |")
    log(f"(enclosure A/2^{NBITS} <= rho_E <= (A+1)/2^{NBITS} from {NBITS} exact digits; the 40-decimal "
        "truncations of both ends agree)")
    for k in allnames:
        log(f"  A({k}) = 0x{RHO[k][1]:050x}")
    log("")

    # -----------------------------------------------------------------------------------------
    log("## 3. The sign race S_E(x) = sum_{p<=x} sgn a_p = #{a_p > 0} - #{a_p < 0}\n")
    log("D_E(n) = #{k<n: a<0} - #{k<n: a>0} = -S_E(p_{n-1}) (index scale).\n")
    log("| curve | x | S | S/sqrt x | S log x/sqrt x | S/pi(sqrt x) | frac S<0 | log-frac S<0 | sign changes | "
        "density of 1s | #{a_p=0} |")
    log("|---|---|---|---|---|---|---|---|---|---|---|")
    SUM = {}
    LM = {}
    for k in allnames:
        sg = np.sign(AP[k])
        S, rows = race_stats(ps, sg, xs)
        SUM[k] = S
        LM[k] = logmean_norm(ps, S)
        for r in rows:
            x = r["x"]
            log(f"| {k} | {x:.0e} | {r['S']:+d} | {r['S'] / math.sqrt(x):+.4f} | "
                f"{r['S'] * math.log(x) / math.sqrt(x):+.3f} | {r['S'] / pi_sqrt(ps, x):+.3f} | "
                f"{r['frac_neg']:.3f} | {r['lfrac_neg']:.3f} | {r['changes']} | {r['ones']:.5f} | {r['zeros']} |")
    log("\nlog-mean of S_E(x)/pi(sqrt x) over x in [10^4, 10^6]: " +
        ", ".join(f"{k} {LM[k]:+.3f}" for k in allnames))
    log("D_E(n) at n = 10^3, 10^4, " + str(len(ps)) + ": " +
        "; ".join(f"{k}: {-SUM[k][999]:+d}, {-SUM[k][9999]:+d}, {-SUM[k][-1]:+d}" for k in allnames) + "\n")

    # -----------------------------------------------------------------------------------------
    log("## 4. CM curves\n")
    H4, H3 = bh_constants()
    log(f"Bateman-Horn constants: H4 = 2 prod_(q odd)(1 - chi_4(q)/(q-1)) = {H4:.6f};  "
        f"H3 = prod_(q>=5)(1 - chi_-3(q)/(q-1)) = {H3:.6f}")
    log("leading terms: 64a: +sqrt(x)/(2 pi) = +0.159155 sqrt x;  36a: +sqrt(x)/(6 pi) = +0.053052 sqrt x;  "
        "27a: -sqrt(x)/(6 pi);  32a: no sqrt(x) term")
    log("\n| curve | x | S(x) | P(x) (lattice) | S - P | S/sqrt x | P/sqrt x | leading const |")
    log("|---|---|---|---|---|---|---|---|")
    lead = {"64a": 1 / (2 * math.pi), "36a": 1 / (6 * math.pi), "27a": -1 / (6 * math.pi)}
    for k in ("64a", "36a", "27a"):
        P = bh_lattice(k, xs, H4, H3)
        for x, Px in zip(xs, P):
            Sx = int(SUM[k][np.searchsorted(ps, x, side="right") - 1])
            log(f"| {k} | {x:.0e} | {Sx:+d} | {Px:+.1f} | {Sx - Px:+.1f} | {Sx / math.sqrt(x):+.4f} | "
                f"{Px / math.sqrt(x):+.4f} | {lead[k]:+.4f} |")
    lwc = {"64a": logw_sieve(10 ** 6 + 2, lambda q: 1 if q % 4 == 1 else -1, 3),
           "3": logw_sieve(2 * 10 ** 6 + 4, lambda q: 1 if q % 3 == 1 else -1, 5)}
    log("\nP(x)/sqrt x beyond the sieve (line integrals), and (P/sqrt x - const) log x:")
    for k in ("64a", "36a", "27a"):
        row = []
        for x in (1e6, 1e8, 1e10, 1e12):
            Pv = bh_integral(k, x, H4, H3, lwc)
            row.append(f"x=1e{int(round(math.log10(x)))}: {Pv / math.sqrt(x):+.4f} "
                       f"[{(Pv / math.sqrt(x) - lead[k]) * math.log(x):+.2f}]")
        log(f"  {k}: " + "  ".join(row))

    log("\nHecke characters psi^j (j odd) of 27a (alpha = 1 mod 3) and 36a (beta = 1 mod 2 sqrt-3): "
        "level N and root number W by the Fricke test of the CM form sum psi(a)^j q^(N a) (weight j+1); "
        "Lambda(1/2) up to a positive factor.  (For 36a and j = 3 mod 6 the character is that of 27a.)")
    RN = {k: hecke_root_numbers(k) for k in ("27a", "36a")}
    for j in range(3, 42, 6):
        RN["36a"][j] = RN["27a"][j]
    log("| j | N(27a) | W(27a) | Lambda(1/2) | (-1)^((j-1)/2) W | N(36a) | W(36a) | Lambda(1/2) | (-1)^((j-1)/2) W |")
    log("|---|---|---|---|---|---|---|---|---|")
    for j in range(1, 42, 2):
        s = (-1) ** ((j - 1) // 2)
        r27, r36 = RN["27a"][j], RN["36a"][j]
        if r27[1] is None or r36[1] is None:
            log(f"| {j} | {r27} | {r36} | (Fricke test failed) |")
            continue
        log(f"| {j} | {r27[0]} | {r27[1]:+d} | {r27[2]:.4g} | {s * r27[1]:+d} | {r36[0]} | {r36[1]:+d} | "
            f"{r36[2]:.4g} | {s * r36[1]:+d} |")
    for k in ("27a", "36a"):
        al = [(-1) ** ((j - 1) // 2) * RN[k][j][1] for j in range(1, 42, 2)]
        log(f"  {k}: mean of (-1)^((j-1)/2) W(psi^j) over j odd <= 41: {np.mean(al):+.3f}  "
            f"(the lattice model needs {'-1/3' if k == '27a' else '+1/3'})")
    log("\nMode biases: sum_{p<=x} cos(j theta_p) / pi(sqrt x), log-mean over [10^4, 10^6], against W/4 "
        "(inert primes give +1/4, a simple central zero -1/2):")
    for k in ("27a", "36a", "32a", "64a"):
        a = AP[k]
        split = a != 0
        th = np.arccos(np.clip(a / (2 * np.sqrt(ps)), -1, 1))
        row = []
        for j in (1, 3, 5, 7, 9, 11, 13, 15):
            Mj = np.cumsum(np.where(split, np.cos(j * th), 0.0))
            pred = ""
            if k in RN:
                pred = f"({RN[k][j][1] / 4:+.2f})"
            row.append(f"j={j}: {logmean_norm(ps, Mj):+.2f}{pred}")
        log(f"  {k}: " + "  ".join(row))
    log("\nTruncated Fourier sums sum_p f_J(theta_p)/pi(sqrt x), f_J = (4/pi) sum_{j<=J} (-1)^((j-1)/2) cos(j t)/j,"
        " log-mean, against the mode prediction (1/pi) sum_{j<=J} (-1)^((j-1)/2) W_j / j:")
    for k in ("27a", "36a"):
        a = AP[k]
        split = a != 0
        th = np.arccos(np.clip(a / (2 * np.sqrt(ps)), -1, 1))
        F = np.zeros(len(ps))
        row = []
        jp = -1
        for J in (1, 3, 9, 41):
            for j in range(jp + 2, J + 1, 2):
                F += np.where(split, (4 / math.pi) * (-1) ** ((j - 1) // 2) * np.cos(j * th) / j, 0.0)
            jp = J
            pred = sum((-1) ** ((j - 1) // 2) * RN[k][j][1] / (math.pi * j) for j in range(1, J + 1, 2))
            row.append(f"J={J}: {logmean_norm(ps, np.cumsum(F)):+.3f} (pred {pred:+.3f})")
        log(f"  {k}: " + "  ".join(row))

    # -----------------------------------------------------------------------------------------
    log(f"### 4b. CM curves to {args.xcm:.0e} (lattice enumeration; agrees with section 1 below 10^6)\n")
    t = time.time()
    XC = int(args.xcm)
    PC, APC = cm_extended(XC)
    nn = len(ps)
    for k in CM:
        assert np.array_equal(APC[k][:nn].astype(np.int64), AP[k]), k
    log(f"{len(PC)} primes, {time.time() - t:.1f} s; equal to the section-1 values for p < {X:.0e}: True")
    xsC = [x for x in (1e4, 1e5, 1e6, 1e7, 1e8, 1e9) if x <= XC]
    log("\nP(x): Bateman-Horn line model.  Q(x) = pi(sqrt x) (1/pi) sum_{j odd <= sqrt x} (-1)^((j-1)/2) W_j / j: "
        "the Hecke-mode model (W_j = W(psi^j); 64a: (-1)^((j-1)/2) W_j = +1 for all j [gaussian-primes.md]; "
        "27a, 36a: the period-12 pattern of the table above, assumed for j > 41).")
    log("\n| curve | x | S(x) | P(x) | Q(x) | S/sqrt x | S/pi(sqrt x) | P/pi(sqrt x) | Q/pi(sqrt x) | frac S<0 | "
        "log-frac S<0 | sign changes |")
    log("|---|---|---|---|---|---|---|---|---|---|---|---|")

    def align(k, j):
        if k == "64a":
            return 1
        return (-1) ** ((j - 1) // 2) * RN[k][(j - 1) % 12 + 1][1]
    LMC = {}
    for k in ("64a", "36a", "27a", "32a"):
        sgC = np.sign(APC[k]).astype(np.int64)
        SC, rows = race_stats(PC, sgC, xsC)
        LMC[k] = logmean_norm(PC, SC)
        for r in rows:
            x = r["x"]
            Pv = bh_integral(k, x, H4, H3, lwc) if k != "32a" else float("nan")
            pis = pi_sqrt(PC, x)
            Qv = (pis / math.pi * sum(align(k, j) / j for j in range(1, math.isqrt(int(x)) + 1, 2))
                  if k != "32a" else float("nan"))
            log(f"| {k} | {x:.0e} | {r['S']:+d} | {Pv:+.1f} | {Qv:+.1f} | {r['S'] / math.sqrt(x):+.4f} | "
                f"{r['S'] / pis:+.3f} | {Pv / pis:+.3f} | {Qv / pis:+.3f} | {r['frac_neg']:.4f} | "
                f"{r['lfrac_neg']:.4f} | {r['changes']} |")
        last_neg = PC[np.nonzero(SC < 0)[0][-1]] if np.any(SC < 0) else None
        last_pos = PC[np.nonzero(SC > 0)[0][-1]] if np.any(SC > 0) else None
        last_np = PC[np.nonzero(SC <= 0)[0][-1]] if np.any(SC <= 0) else None
        log(f"  {k}: min S = {SC.min():+d}, max S = {SC.max():+d}, last p with S < 0: {last_neg}, "
            f"last p with S <= 0: {last_np}, last p with S > 0: {last_pos}")
    log(f"\nlog-mean of S/pi(sqrt x) over [10^4, {XC:.0e}]: " + ", ".join(f"{k} {LMC[k]:+.3f}" for k in LMC))
    log("\nMode biases to " + f"{XC:.0e}" + ": log-mean over [10^4, X] of sum_p cos(j theta_p)/pi(sqrt x) (pred W/4):")
    for k in ("27a", "36a"):
        a = APC[k].astype(float)
        split = a != 0
        th = np.arccos(np.clip(a / (2 * np.sqrt(PC)), -1, 1))
        row = []
        for j in (1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23):
            Mj = np.cumsum(np.where(split, np.cos(j * th), 0.0))
            row.append(f"{j}: {logmean_norm(PC, Mj):+.2f} ({RN[k][j][1] / 4:+.2f})")
        log(f"  {k}: " + "  ".join(row))
        F = np.zeros(len(PC))
        row = []
        jp = -1
        for J in (1, 3, 9, 41, 101):
            for j in range(jp + 2, J + 1, 2):
                F += np.where(split, (4 / math.pi) * (-1) ** ((j - 1) // 2) * np.cos(j * th) / j, 0.0)
            jp = J
            if J <= 41:
                pred = sum((-1) ** ((j - 1) // 2) * RN[k][j][1] / (math.pi * j) for j in range(1, J + 1, 2))
                row.append(f"J={J}: {logmean_norm(PC, np.cumsum(F)):+.3f} (pred {pred:+.3f})")
            else:
                row.append(f"J={J}: {logmean_norm(PC, np.cumsum(F)):+.3f}")
        log(f"  {k} truncated Fourier sums: " + "  ".join(row))
    del APC, PC
    _LM_CACHE.clear()
    log("")

    # -----------------------------------------------------------------------------------------
    log("## 5. Non-CM curves: Sym^j expansion, predicted bias, discreteness\n")
    log("c_j = (2/pi)(-1)^((j-1)/2)(1/j + 1/(j+2)): " +
        ", ".join(f"c_{j} = {cj(j):+.4f}" for j in (1, 3, 5, 7, 9)) +
        f";  sum_j c_j = {sum(cj(j) for j in range(1, 400001, 2)):.6f} (= 2/pi = {2 / math.pi:.6f})")
    R = sum(cj(j) * kron_m2(j) for j in range(3, 400001, 2))
    log(f"R = sum_(j>=3) c_j (-2/j) = {R:+.6f};  B_E = c_1 (1/2 - r) + (1/2) W(E) R  "
        "(prime squares: +1/2 per mode; central zeros: -r_j; W(Sym^j E) = (-2/j) W(E) for semistable E)")
    log("\nW(Sym^3 E) by the functional equation of L(s, Sym^3 E) (conductor N^3), and L(1/2, Sym^3 E):")
    ps_small = ps[ps < 400000]
    for k in ("11a1", "14a1", "37a1", "389a1"):
        N = conductor[k]
        N3 = N ** 3
        nmax = int(min(390000, max(3000, 45 * math.sqrt(N3))))
        amap = dict(zip(ps_small.tolist(), AP[k][:len(ps_small)].tolist()))
        lam = sym3_coeffs(amap, N, nmax, ps_small)
        ratios, Lh = sym3_test(lam, N3)
        W3 = int(round(ratios[0]))
        log(f"  {k}: N^3 = {N3}, terms {nmax}: Theta(1/y)/(y Theta(y)) = {ratios[0]:+.10f}, {ratios[1]:+.10f}"
            f"  => W(Sym^3) = {W3:+d} (W(E) = {WE[k]:+d})" +
            (f";  L(1/2, Sym^3 E) = {Lh:.6f}" if W3 == 1 else ";  L(1/2, Sym^3 E) = 0 (odd)"))
    log("\n| curve | rank r | W | B_E | Delta_E (torsion) | Delta_E (model) | B + Delta | observed log-mean S/pi(sqrt x) | "
        "S/pi(sqrt x) at 10^6 | race a_p/sqrt p log-mean (pred 1/2 - r) | S - c_1 race (obs.) | "
        "(1/2) sum_(j>=3) c_j W_j + Delta (pred.) |")
    log("|---|---|---|---|---|---|---|---|---|---|---|---|")
    PRED = {}
    for k in names:
        r, m = NONCM[k][2], NONCM[k][3]
        B = predicted_B(r, WE[k])
        Dt = torsion_mu(m) / math.pi
        Mod = {"11a1": 5, "14a1": 12}.get(k, 12)
        Dm = logmean_norm(ps, discreteness_model(ps, AP[k], Mod))
        race = np.cumsum(np.where(conductor[k] % ps != 0, AP[k] / np.sqrt(ps), 0.0))
        PRED[k] = (B, Dt)
        lr = logmean_norm(ps, race)
        log(f"| {k} | {r} | {WE[k]:+d} | {B:+.3f} | {Dt:+.3f} | {Dm:+.3f} (mod {Mod}) | {B + Dt:+.3f} | "
            f"{LM[k]:+.3f} | {SUM[k][-1] / pi_sqrt(ps, X):+.3f} | {lr:+.3f} | {LM[k] - cj(1) * lr:+.3f} | "
            f"{B - cj(1) * (0.5 - r) + Dt:+.3f} |")
    log("\nSmall a_p: #{a_p = a} for a = -6..6 (the torsion congruence a_p = p + 1 mod m forbids some values):")
    for k in names:
        log(f"  {k}: " + " ".join(f"{a}:{int(np.sum(AP[k] == a))}" for a in range(-6, 7)))
    log("\nMode sums M_j(x) = sum_{p<=x} U_j(cos theta_p), log-mean of M_j/pi(sqrt x), against 1/2 - r_j "
        "(r_j = (1 - W_j)/2 for j >= 3, W_j = (-2/j) W(E)):")
    F101, REM = {}, {}
    for k in names:
        a = AP[k]
        good = conductor[k] % ps != 0
        th = np.arccos(np.clip(a / (2 * np.sqrt(ps)), -1, 1))
        st = np.sin(th)
        row = []
        for j in (1, 3, 5, 7, 9, 11):
            U = np.where(good, np.sin((j + 1) * th) / st, 0.0)
            pred = 0.5 - NONCM[k][2] if j == 1 else 0.5 * kron_m2(j) * WE[k]
            row.append(f"{j}: {logmean_norm(ps, np.cumsum(U)):+.2f} ({pred:+.1f})")
        F = np.zeros(len(ps))
        tr = []
        jp = -1
        for J in (1, 3, 9, 31, 101):
            for j in range(jp + 2, J + 1, 2):
                F += cj(j) * np.where(good, np.sin((j + 1) * th) / st, 0.0)
            jp = J
            tr.append(f"{J}: {logmean_norm(ps, np.cumsum(F)):+.2f}")
            if J == 31:
                REM31 = LM[k] - logmean_norm(ps, np.cumsum(F))
        F101[k] = F
        REM[k] = (REM31, LM[k] - logmean_norm(ps, np.cumsum(F)))
        log(f"  {k}: M_j " + "  ".join(row) + " | truncated sum_(j<=J) c_j M_j: " + "  ".join(tr))
    log("\nRemainder S - sum_(j<=J) c_j M_j (log-means; the part of the race not carried by the modes j <= J, "
        "i.e. the scale |a_p| < 2 sqrt(p)/J), against the discreteness term Delta_E:")
    for k in names:
        log(f"  {k}: J = 31: {REM[k][0]:+.3f}   J = 101: {REM[k][1]:+.3f}   Delta_E (torsion) = "
            f"{torsion_mu(NONCM[k][3]) / math.pi:+.3f}")
    log("")

    # -----------------------------------------------------------------------------------------
    log("## 6. Quadratic twist families (|d| <= 150, gcd(d, 5N) = 1)\n")
    spf2 = spf_table(9000)
    fam_rows = []
    for base in ("11a1", "37a1"):
        N0 = conductor[base]
        W0 = WE[base]
        a0 = AP[base]
        sg0 = np.sign(a0)
        ds = [d for d in fundamental_discriminants(150) if math.gcd(d, 5 * N0) == 1]
        for d in ds:
            chi = kron_primes(d, ps)
            N = N0 * d * d
            chiN = int(kron_primes(d, np.array([N0]))[0])      # N0 = 11, 37 prime
            W = W0 * chiN * (1 if d > 0 else -1)
            sg = chi * sg0
            S = np.cumsum(sg)
            lm = logmean_norm(ps, S)
            ad = chi * a0
            nmax = int(min(8800, 9 * math.sqrt(N) + 50))
            amap = dict(zip(ps[:1200].tolist(), ad[:1200].tolist()))
            an = an_from_ap(amap, N, nmax, spf2)
            lv = lvalues(an, N, W)
            if W == 1:
                r = 0 if abs(lv) > 1e-6 else 2
            else:
                r = 1 if abs(lv) > 1e-6 else 3
            race = np.cumsum(np.where(chi * (N0 % ps != 0) != 0, ad / np.sqrt(ps), 0.0))
            B = predicted_B(r, W0, twist_sign=d, chiN=chiN)
            rem = lm - logmean_norm(ps, np.cumsum(chi * F101[base]))
            fam_rows.append((base, d, N, W, r, lv, B, lm, S[-1] / pi_sqrt(ps, X), logmean_norm(ps, race), rem))
    log("| family | rank (numerical) | W | sign of d | #twists | mean B | mean observed log-mean S/pi(sqrt x) | std | "
        "mean race a_p/sqrt p (pred 1/2 - r) | mean S - c_1 race | pred (1/2) sum_(j>=3) c_j W_j |")
    log("|---|---|---|---|---|---|---|---|---|---|---|")
    for base in ("11a1", "37a1"):
        for r in (0, 1, 2, 3):
            for sgn_d in (1, -1):
                rows = [f for f in fam_rows if f[0] == base and f[4] == r and (f[1] > 0) == (sgn_d > 0)]
                if not rows:
                    continue
                obs = np.array([f[7] for f in rows])
                res = np.array([f[7] - cj(1) * f[9] for f in rows])
                tl = np.array([f[6] - cj(1) * (0.5 - f[4]) for f in rows])
                log(f"| {base} | {r} | {rows[0][3]:+d} | {'+' if sgn_d > 0 else '-'} | {len(rows)} | "
                    f"{np.mean([f[6] for f in rows]):+.3f} | {np.mean(obs):+.3f} | {np.std(obs):.3f} | "
                    f"{np.mean([f[9] for f in rows]):+.3f} | {np.mean(res):+.3f} (se {np.std(res) / math.sqrt(len(rows)):.3f}) | "
                    f"{np.mean(tl):+.3f} |")
    resid = np.array([f[7] - cj(1) * f[9] for f in fam_rows])
    tails = np.array([f[6] - cj(1) * (0.5 - f[4]) for f in fam_rows])
    log(f"S - c_1 race against the predicted higher-mode term over all twists: correlation "
        f"{np.corrcoef(resid, tails)[0, 1]:+.3f}; mean residual where pred > 0: {np.mean(resid[tails > 0]):+.3f}, "
        f"where pred < 0: {np.mean(resid[tails < 0]):+.3f}")
    for base in ("11a1", "37a1"):
        rm = np.array([f[10] for f in fam_rows if f[0] == base])
        log(f"remainder S - sum_(j<=101) c_j M_j over the {len(rm)} twists of {base} (Delta = 0 for all of them): "
            f"mean {np.mean(rm):+.3f}, std {np.std(rm):.3f}, se {np.std(rm) / math.sqrt(len(rm)):.3f}; "
            f"base curve: {REM[base][1]:+.3f} (Delta_E = {torsion_mu(NONCM[base][3]) / math.pi:+.3f})")
    allR = np.array([f[9] for f in fam_rows])
    allS = np.array([f[7] for f in fam_rows])
    sl = np.polyfit(allR, allS, 1)
    log(f"sign race against the race a_p/sqrt p over all twists: correlation {np.corrcoef(allR, allS)[0, 1]:+.3f}, "
        f"least squares S = {sl[0]:.3f} race {sl[1]:+.3f}  (c_1 = 8/(3 pi) = {cj(1):.3f})")
    allB = np.array([f[6] for f in fam_rows])
    allO = np.array([f[7] for f in fam_rows])
    slope = np.polyfit(allB, allO, 1)
    log(f"all {len(fam_rows)} twists: correlation(B, observed) = {np.corrcoef(allB, allO)[0, 1]:+.3f}; "
        f"least squares observed = {slope[0]:.3f} B {slope[1]:+.3f}")
    log("\nTwists of rank >= 2 found: " + "; ".join(
        f"{f[0]} (x) chi_{f[1]} (N = {f[2]}, W = {f[3]:+d}, |L| = {abs(f[5]):.1e}, observed {f[7]:+.2f}, B {f[6]:+.2f})"
        for f in fam_rows if f[4] >= 2))
    log("\nThe pair 11a1 / 11a1 (x) chi_-7 (conductor 539):")
    for f in fam_rows:
        if f[0] == "11a1" and f[1] == -7:
            log(f"  11a1 (x) chi_-7: W = {f[3]:+d}, rank {f[4]} (L'(1) = {f[5]:.6f}), B = {f[6]:+.3f}, "
                f"observed log-mean {f[7]:+.3f}, S/pi(sqrt x) at 10^6 {f[8]:+.3f}")
    log(f"  11a1: W = +1, rank 0, B = {PRED['11a1'][0]:+.3f} (+ Delta = {PRED['11a1'][1]:+.3f}), "
        f"observed log-mean {LM['11a1']:+.3f}\n")

    # -----------------------------------------------------------------------------------------
    log("## 7. Residue classes, blocks, consecutive digits\n")
    for k in ("11a1", "37a1", "5077a1"):
        neg = AP[k] < 0
        row = []
        for Nm in (3, 4, 5, 8, 12):
            fr = [float(np.mean(neg[(ps % Nm == c) & (ps > 5)])) for c in range(Nm) if math.gcd(c, Nm) == 1]
            row.append(f"mod {Nm}: [{min(fr):.4f}, {max(fr):.4f}]")
        log(f"  {k}: fraction of a_p < 0 per unit class: " + "  ".join(row))
    log("  (11a1, mod 5: a_p mod 5 is determined by p mod 5, but the sign is not.)\n")
    log("| sequence | n | density | p(L) = 2^L for L <= | chi^2/dof L = 2, 4, 6, 8, 10 (z) | P(d_k+1 = d_k) | indep. | z |")
    log("|---|---|---|---|---|---|---|---|")
    seqs = [(k + " (all p)", (AP[k] < 0).astype(np.int64)) for k in names]
    seqs += [(k + " (split p)", (AP[k][AP[k] != 0] < 0).astype(np.int64)) for k in CM]
    seqs += [(k + " (all p)", (AP[k] < 0).astype(np.int64)) for k in ("64a", "27a")]
    for nm, d in seqs:
        full = max(L for L in range(1, 13) if complexity(d, L) == 2 ** L)
        ch = []
        for L in (2, 4, 6, 8, 10):
            c2, dof, z = block_chi2(d, L)
            ch.append(f"{c2 / dof:.2f} ({z:+.1f})")
        same, e, z = repeat_stat(d)
        log(f"| {nm} | {len(d)} | {np.mean(d):.4f} | {full} | {', '.join(ch)} | {same:.4f} | {e:.4f} | {z:+.1f} |")
    log("")

    # -----------------------------------------------------------------------------------------
    log("## 8. Congruence (Chebotarev) digits\n")
    log("Defect |C| - nu(C), nu(C) = #{h in G : h^2 in C}.  If the digit [Frob_p in C] were eventually periodic, "
        "then sum_{rho != 1} c_rho ord_{1/2} L(s, rho) = (|C| - nu(C))/2 with algebraic-integer c_rho: impossible "
        "when the defect is odd.  Predicted Chebyshev bias (no central zeros): (|C| - nu(C))/(2|G|) pi(sqrt x).\n")
    log("| l | class C | |C| | nu(C) | |G| | density | defect | parity method | bias coeff. |")
    log("|---|---|---|---|---|---|---|---|---|")
    DEF = {}
    for l in (2, 3, 5, 7):
        for name, C, nu, G in gl2_defects(l):
            dfc = C - nu
            DEF[(l, name)] = (C, nu, G)
            log(f"| {l} | {name} | {C} | {nu} | {G} | {C / G:.4f} | {dfc:+d} | "
                f"{'irrational (odd)' if dfc % 2 else 'no conclusion (even)'} | {dfc / (2 * G):+.4f} |")
    log("\nNumerics (p > 7 of good reduction): density and log-mean of sum_{p<=x}([Frob_p in C] - |C|/|G|)/pi(sqrt x):")
    log("| curve | digit | density obs. | |C|/|G| | log-mean bias | predicted |")
    log("|---|---|---|---|---|---|")
    for k in ("11a1", "37a1", "389a1", "5077a1", "27a"):
        a = AP[k]
        good = (conductor[k] % ps != 0) & (ps > 7)
        digs = [("[a_p even] = [2 | #E(F_p)]", (a % 2 == 0), (2, "det(1-g) = 0  (l | #E(F_p))"))]
        if k in NR:
            digs.append(("[E(F_p)[2] = (Z/2)^2] (3 roots)", NR[k] == 3, (2, "g = 1  (p splits in Q(E[l]))")))
        if k in ("37a1", "389a1", "5077a1"):
            for l in (3, 5):
                digs.append((f"[a_p = 0 mod {l}]", a % l == 0, (l, "tr = 0")))
                digs.append((f"[{l} | #E(F_p)]", (ps + 1 - a) % l == 0, (l, "det(1-g) = 0  (l | #E(F_p))")))
        for nm, ind, key in digs:
            C, nu, G = DEF[key]
            dens_th = C / G
            ind = ind & good
            S = np.cumsum(np.where(good, ind.astype(float) - dens_th, 0.0))
            pred = (C - nu) / (2 * G)
            log(f"| {k} | {nm} | {np.sum(ind) / np.sum(good):.4f} | {dens_th:.4f} | {logmean_norm(ps, S):+.3f} | "
                f"{pred:+.3f} |")
    log("(14a1, 64a, 32a, 36a have a rational 2-torsion point, so [a_p even] has density 1 there; "
        "27a: the 2-division field is Q(cbrt 2, sqrt -3), Galois group S_3.)")

    log(f"\nTotal runtime: {time.time() - T0:.0f} s")


if __name__ == "__main__":
    main()
