#!/usr/bin/env python3
"""The Gaussian Rokicki digit d_p = [a == 3 mod 4], p = a^2 + b^2, a odd > 0, b even > 0.

Numerics for research/gaussian-primes.md.  For every prime p == 1 mod 4 below X_MAX = 10^8 the
representation p = a^2 + b^2 (a odd > 0, b even > 0) is found by enumerating the lattice points
(a, b) of the quarter disc and looking them up in a sieve.  The script prints:

  1. identification checks: chi_4(a) = chi_8(p) sgn(Re pi_0) for the primary pi_0 == 1 mod (2+2i);
     Re pi_0 mod 8 is a function of p mod 16; a mod 4 is NOT a function of p mod N (N | 128);
     |a_p(E)| = 2a and the sign of a_p(E) for the CM curves y^2 = x^3 + D x; Gauss's x^2 + 64 y^2.
  2. the bias table: S(x) = sum_{p <= x, p == 1 mod 4} chi_4(a_p) against pi(sqrt x), sqrt x and
     the Bateman-Horn lattice prediction P(x); the same with the lines a <= A0 removed; the
     control digit [b == 2 mod 4] = [p == 5 mod 8]; the untwisted digit sgn(Re pi_0).
  3. root numbers of L(s, lambda^j) and L(s, lambda^j chi_8) (j odd <= 41, via the Fricke
     involution of the CM forms, mpmath), the Hecke modes sum_p chi_8(p) cos(j theta_p), whose
     prediction is W pi(sqrt x)/4 each (inert primes + central zeros), and the truncated Fourier
     series of the digit; the Bateman-Horn line model P(x) also beyond the sieve (to 10^14).
  4. sign changes and logarithmic means of the normalized sums.

Dependencies: numpy, mpmath.  Runtime: about one to two minutes on one core, memory < 3 GB.
Usage: python3 scripts/gaussian_primes.py [--xmax 1e8]
"""

import argparse
import math
import time

import numpy as np

T0 = time.time()


def log(msg=""):
    print(msg, flush=True)


# ---------------------------------------------------------------------------------------------
# Sieve (odd numbers only) and small tables
# ---------------------------------------------------------------------------------------------

def odd_sieve(n):
    """is_p[k] == True iff 2k+1 is prime, for 2k+1 < n."""
    m = (n + 1) // 2
    s = np.ones(m, dtype=bool)
    s[0] = False
    for k in range(1, (math.isqrt(n) - 1) // 2 + 1):
        if s[k]:
            p = 2 * k + 1
            s[p * p // 2::p] = False
    return s


def spf_table(n):
    spf = np.zeros(n + 1, dtype=np.int64)
    for p in range(2, n + 1):
        if spf[p] == 0:
            spf[p::p][spf[p::p] == 0] = p
    return spf


def chi4(n):
    n = np.asarray(n)
    return np.where(n % 2 == 0, 0, np.where(n % 4 == 1, 1, -1))


def w_line(a, spf):
    """Bateman-Horn correction for the line a fixed: prod_{q | a} (q-1)/(q-1-chi_4(q))."""
    w = 1.0
    while a > 1:
        q = int(spf[a])
        w *= (q - 1) / (q - 1 - (1 if q % 4 == 1 else -1))
        while a % q == 0:
            a //= q
    return w


def bh_integral(x, H):
    """P(x) = sum_{a odd} chi_4(a) H w(a) int_{1/2}^{C+1/2} dc / log(a^2 + 4c^2), C = floor(sqrt(x-a^2)/2).

    Gauss-Legendre (24 nodes) in u = log c, vectorized over the lines; w(a) by a log-sieve."""
    A = math.isqrt(int(x))
    logw = np.zeros(A + 1)
    sv = np.ones(A + 1, dtype=bool); sv[:2] = False
    for q in range(2, math.isqrt(A) + 1):
        if sv[q]:
            sv[q * q::q] = False
    for q in np.nonzero(sv)[0][1:]:
        r = (q - 1) / (q - 1 - (1 if q % 4 == 1 else -1))
        logw[q::q] += math.log(r)
    nodes, weights = np.polynomial.legendre.leggauss(24)
    total = 0.0
    for lo in range(1, A + 1, 2 * 10 ** 6):
        a = np.arange(lo, min(lo + 2 * 10 ** 6, A + 1), 2, dtype=np.float64)
        C = np.floor(np.sqrt(np.maximum(x - a * a, 0)) / 2)
        a = a[C >= 1]; C = C[C >= 1]
        if len(a) == 0:
            continue
        u0, u1 = math.log(0.5), np.log(C + 0.5)
        u = (u1 - u0)[:, None] / 2 * nodes[None, :] + (u1 + u0)[:, None] / 2
        c = np.exp(u)
        I = ((u1 - u0) / 2) * np.sum(weights[None, :] * c / np.log(a[:, None] ** 2 + 4 * c * c), axis=1)
        ai = a.astype(np.int64)
        total += np.sum(np.where(ai % 4 == 1, 1.0, -1.0) * H * np.exp(logw[ai]) * I)
    return total


def root_numbers(jmax=41, M=1500):
    """Root numbers W and central values of the CM forms f_j = sum_{alpha primary} psi(alpha) alpha^j q^{N alpha}
    (weight j+1), psi = 1 (lambda^j) or chi_8(N alpha) (lambda^j chi_8), via the Fricke relation
    phi(1/(N y)) = W N^{w/2} y^w phi(y), phi(y) = sum a_n e^{-2 pi n y}; the level N is found by testing."""
    import mpmath
    from mpmath import mp, mpf, mpc
    mp.dps = 80
    R = math.isqrt(M)
    pts = [(x, y, x * x + y * y) for x in range(-R, R + 1, 1) if x % 2
           for y in range(-R, R + 1, 2) if x * x + y * y <= M and (x + y) % 4 == 1]
    out = {}
    for tw in (0, 1):
        for j in range(1, jmax + 1, 2):
            a = [mpf(0)] * (M + 1)
            for x, y, n in pts:
                c = (mpc(x, y) ** j).real
                a[n] += -c if (tw and n % 8 == 5) else c
            nz = [n for n in range(1, M + 1) if a[n] != 0]
            phi = lambda y: mp.fsum(a[n] * mp.e ** (-2 * mp.pi * n * y) for n in nz)
            w = j + 1
            found = None
            for N in (16, 32, 64, 128, 256):
                rs = [phi(1 / (N * y)) / (mpf(N) ** (mpf(w) / 2) * y ** w * phi(y))
                      for y in (mpf('0.8') / mp.sqrt(N), mpf('1.25') / mp.sqrt(N))]
                if abs(abs(rs[0]) - 1) < 1e-20 and abs(rs[0] - rs[1]) < 1e-20:
                    found = (N, int(mp.nint(rs[0])))
            N, W = found
            cv = (1 + W) * mp.fsum(a[n] * (2 * mp.pi * n) ** (-mpf(w) / 2) *
                                   mp.gammainc(mpf(w) / 2, 2 * mp.pi * n / mp.sqrt(N)) for n in nz)
            out[(tw, j)] = (N, W, float(cv))
    return out


# ---------------------------------------------------------------------------------------------
# Main computation
# ---------------------------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--xmax", type=float, default=1e8)
    args = ap.parse_args()
    XMAX = int(args.xmax)
    R = math.isqrt(XMAX)

    log(f"# Gaussian Rokicki digit: p = a^2 + b^2 <= {XMAX:.0e}, a odd > 0, b even > 0\n")
    isp = odd_sieve(XMAX + 1)
    allp = np.concatenate(([2], 2 * np.nonzero(isp)[0] + 1))
    log(f"sieve: {len(allp)} primes below {XMAX:.0e}  [{time.time()-T0:.1f}s]")
    spf = spf_table(R + 1)

    # Hardy-Littlewood / Bateman-Horn constants.
    q = allp[1:].astype(np.float64)
    c4 = chi4(allp[1:]).astype(np.float64)
    # prod_{q odd} (1 - chi4(q)/(q-1)) = (4/pi) prod (1 - chi4/(q-1)) / (1 - chi4/q)  (abs. conv.)
    corr = np.exp(np.sum(np.log1p(-c4 / (q - 1)) - np.log1p(-c4 / q)))
    HL = 4 / math.pi * corr
    H = 2 * HL
    # K = residue at s = 0 of sum_{d odd sqfree} u(d) d^{-s}, u(q) = chi4(q)(r(q) - 1).
    K = 0.5 * np.exp(np.sum(np.where(c4 > 0, np.log1p(1 / (q * (q - 2))), np.log1p(-1 / q ** 2))))
    log(f"Hardy-Littlewood constant for n^2+1: prod_q odd (1 - chi4(q)/(q-1)) = {HL:.7f}")
    log(f"line constant H = 2 * that = {H:.6f};  K = (1/2) prod_q odd (1+u(q))(1-1/q) = {K:.6f};"
        f"  H K / 8 = {H*K/8:.6f}\n")

    # Thresholds for the tables.
    grid = np.unique(np.concatenate([
        np.round(10 ** np.linspace(4, math.log10(XMAX), 161)).astype(np.int64),
        np.array([10 ** 5, 10 ** 6, 10 ** 7, 15 * 10 ** 6, 10 ** 8], dtype=np.int64)]))
    grid = grid[grid <= XMAX]
    A0S = [1, 3, 5, 7, 9, 11, 25, 99]
    ABOUNDS = [A for A in (1, 3, 5, 7, 9, 11, 15, 21, 31, 63, 127, 255, 511, 1023, 2047, 4095)
               if A < R] + [R]
    P = np.zeros(len(grid))                      # Bateman-Horn sum over all lines
    P_le = {A0: np.zeros(len(grid)) for A0 in A0S}
    P_aA = {}                                    # BH partial sums over a <= A at x = XMAX
    line_check = {}

    rows_p, rows_a, rows_b = [], [], []
    cum_line = 0.0
    for a in range(1, R + 1, 2):
        bmax = math.isqrt(XMAX - a * a)
        if bmax < 2:
            break
        b = np.arange(2, bmax + 1, 2, dtype=np.int64)
        f = a * a + b * b
        m = isp[f // 2]
        rows_p.append(f[m]); rows_b.append(b[m]); rows_a.append(np.full(int(m.sum()), a))
        # Bateman-Horn: expected primes on the line up to x = H w(a) sum_{b <= ...} 1/log f.
        cw = np.cumsum(1.0 / np.log(f.astype(np.float64)))
        idx = np.searchsorted(f, grid, side="right")
        exp_line = H * w_line(a, spf) * np.where(idx > 0, cw[np.maximum(idx - 1, 0)], 0.0)
        s = 1 if a % 4 == 1 else -1
        P += s * exp_line
        for A0 in A0S:
            if a <= A0:
                P_le[A0] += s * exp_line
        cum_line += s * exp_line[-1]
        for A in ABOUNDS:
            if a <= A < a + 2:
                P_aA[A] = cum_line
        if a <= 9:
            line_check[a] = (int(m.sum()), exp_line[-1])
    P_aA[R] = cum_line
    p = np.concatenate(rows_p); a = np.concatenate(rows_a); b = np.concatenate(rows_b)
    o = np.argsort(p, kind="stable")
    p, a, b = p[o], a[o], b[o]
    n14 = int(np.sum(allp % 4 == 1))
    log(f"lattice enumeration: {len(p)} primes p == 1 mod 4 found "
        f"(sieve count {n14}; each found once: {len(p) == n14 and len(np.unique(p)) == len(p)})"
        f"  [{time.time()-T0:.1f}s]\n")

    chi_a = np.where(a % 4 == 1, 1, -1).astype(np.int64)          # chi_4(a_p) = 1 - 2 d_p
    chi8 = np.where(p % 8 == 1, 1, -1).astype(np.int64)           # = 1 - 2[b == 2 mod 4]
    eps = np.where((a + b) % 4 == 1, 1, -1)                       # pi_0 = eps (a + b i)
    re0 = eps * a                                                 # Re pi_0, signed
    theta = np.arctan2(eps * b, eps * a).astype(np.float64)       # arg pi_0

    # -----------------------------------------------------------------------------------------
    log("## 1. Identification\n")
    log(f"chi_4(a_p) == chi_8(p) * sgn(Re pi_0) for all p:  {bool(np.all(chi_a == chi8 * np.sign(re0)))}")
    log(f"[b == 2 mod 4] == [p == 5 mod 8] for all p:     {bool(np.all((b % 4 == 2) == (p % 8 == 5)))}")
    ok16 = all(len(set((re0[p % 16 == r] % 8).tolist())) == 1 for r in (1, 5, 9, 13))
    tab16 = {r: int(re0[p % 16 == r][0] % 8) for r in (1, 5, 9, 13)}
    log(f"Re pi_0 mod 8 is a function of p mod 16: {ok16}  {tab16}  (formula (3 - p)/2 mod 8: "
        f"{bool(np.all(re0 % 8 == ((3 - p) // 2) % 8))})")
    log("a mod 4 against p mod N (fraction of a == 3 mod 4, min and max over classes p == 1 mod 4):")
    for N in (8, 16, 32, 64, 128):
        fr = [np.mean(a[p % N == r] % 4 == 3) for r in range(1, N, 4)]
        log(f"   N = {N:3d}: {len(fr):2d} classes, fraction in [{min(fr):.4f}, {max(fr):.4f}]")
    # CM curves: a_p(E) = -sum_x ((x^3 + D x)/p) for p == 1 mod 4 below 4000.
    log("CM curves y^2 = x^3 + D x, p == 1 mod 4 < 4000:  |a_p| == 2a, and sgn(a_p) vs chi_4(a_p)")
    sel = p < 4000
    u0 = np.sign(re0)
    for D in (-1, 1, -4, 4):
        same = opp = absok = same_u = 0
        for pp, aa in zip(p[sel], a[sel]):
            pp = int(pp); aa = int(aa)
            x = np.arange(pp, dtype=np.int64)
            sq = np.zeros(pp, dtype=np.int64); sq[(x * x) % pp] = 1
            leg = np.where(sq == 1, 1, -1); leg[0] = 0
            ap_ = -int(leg[(x * x % pp * x + D * x) % pp].sum())
            absok += abs(ap_) == 2 * aa
            c = 1 if aa % 4 == 1 else -1
            same += np.sign(ap_) == c; opp += np.sign(ap_) == -c
            same_u += np.sign(ap_) == u0[(p == pp)][0]
        log(f"   D = {D:2d}: |a_p| = 2a for {absok}/{sel.sum()};  sgn a_p = +chi_4(a): {same}, "
            f"= -chi_4(a): {opp};  sgn a_p = +sgn Re pi_0: {same_u}")
    bad = 0; cnt = 0
    for pp, bb in zip(p[(p % 8 == 1) & (p < 10 ** 6)], b[(p % 8 == 1) & (p < 10 ** 6)]):
        cnt += 1
        bad += (pow(2, (int(pp) - 1) // 4, int(pp)) == 1) != (bb % 8 == 0)
    log(f"Gauss (2 is a 4th power mod p iff 8 | b), p == 1 mod 8 < 1e6: {cnt} primes, {bad} exceptions\n")

    # -----------------------------------------------------------------------------------------
    pi_all = np.searchsorted(allp, grid, side="right")
    pi_sqrt = np.searchsorted(allp, np.sqrt(grid), side="right")
    k = np.searchsorted(p, grid, side="right")            # number of p == 1 mod 4 up to x

    def at(arr):
        cs = np.concatenate(([0], np.cumsum(arr)))
        return cs[k]

    S = at(chi_a)
    C = at(chi8)
    U = at(np.sign(re0))
    dec = [i for i, x in enumerate(grid) if x in (10 ** 5, 10 ** 6, 10 ** 7, 15 * 10 ** 6, 10 ** 8)]

    log("## 2. Bias of S(x) = sum_{p <= x} chi_4(a_p), against pi(sqrt x) and Bateman-Horn P(x)\n")
    log("| x | #p | S(x) | pi(sqrt x) | S/pi(sqrt x) | S/sqrt x | BH P(x) | S - P | (S-P)/pi(sqrt x) "
        "| Hecke cutoff Q(x) |")
    log("|---|---|---|---|---|---|---|---|---|---|")
    for i in dec:
        x = grid[i]
        Q = pi_sqrt[i] / math.pi * sum(1 / j for j in range(1, math.isqrt(int(x)) + 1, 2))
        log(f"| {x:.1e} | {k[i]} | {S[i]:+d} | {pi_sqrt[i]} | {S[i]/pi_sqrt[i]:+.3f} | "
            f"{S[i]/math.sqrt(x):+.4f} | {P[i]:+.1f} | {S[i]-P[i]:+.1f} | {(S[i]-P[i])/pi_sqrt[i]:+.3f} "
            f"| {Q:+.0f} |")
    log("Q(x) = pi(sqrt x) (1/pi) sum_{j odd <= sqrt x} 1/j: Hecke modes with root numbers, cut at j = sqrt x")
    log(f"\nasymptotic BH slope H K / 8 = {H*K/8:.4f} (P(x)/sqrt x -> this, with O(1/log x) corrections)")
    log(f"inert-prime term alone (all modes without central zero): +pi(sqrt x)/4 = "
        f"{pi_sqrt[dec[-1]]/4:.1f} at x = {grid[dec[-1]]:.0e}\n")
    log("Bateman-Horn P(x) beyond the sieve range (integral form, all lines a < sqrt x):")
    for e in (8, 10, 12, 14):
        xx = 10.0 ** e
        Pi = bh_integral(xx, H)
        log(f"   x = 1e{e}: P(x)/sqrt x = {Pi/math.sqrt(xx):.4f}   (1/(2 pi) = {1/(2*math.pi):.4f};  "
            f"(P/sqrt x - 1/(2 pi)) log x = {(Pi/math.sqrt(xx) - 1/(2*math.pi))*math.log(xx):.3f})")
    log("")

    log("Bateman-Horn per line (x = XMAX): actual vs predicted number of primes")
    for aa, (act, pred) in line_check.items():
        log(f"   a = {aa}: {act} primes, BH {pred:.1f}")
    log("")

    log("Partial sums over lines a <= A at x = XMAX: actual T(A) vs BH, and (K/2) log A")
    for A in ABOUNDS:
        T = int(chi_a[a <= A].sum())
        log(f"   A = {A:5d}: T(A) = {T:+5d}   BH {P_aA[A]:+8.1f}   "
            f"BH leading (H/(2 log x)) sqrt(x) (K/2) log A = "
            f"{H/(2*math.log(XMAX))*math.sqrt(XMAX)*K/2*math.log(A):8.1f}")
    log("")

    log("Lines a <= A0 removed: S_{a>A0}(x) and BH prediction")
    log("| A0 | " + " | ".join(f"x={grid[i]:.0e}" for i in dec) + " |")
    log("|---|" + "---|" * len(dec))
    for A0 in A0S:
        Sr = at(np.where(a > A0, chi_a, 0))
        log(f"| {A0} | " + " | ".join(f"{Sr[i]:+d} (BH {P[i]-P_le[A0][i]:+.0f})" for i in dec) + " |")
    log("")

    log("Control and untwisted digit")
    log("| x | control C(x) = sum chi_8(p) | C/pi(sqrt x) | U(x) = sum sgn Re pi_0 | U/pi(sqrt x) |")
    log("|---|---|---|---|---|")
    for i in dec:
        log(f"| {grid[i]:.1e} | {C[i]:+d} | {C[i]/pi_sqrt[i]:+.3f} | {U[i]:+d} | {U[i]/pi_sqrt[i]:+.3f} |")
    log("predicted: C ~ -pi(sqrt x)/2 (Rubinstein-Sarnak, square class 1 mod 8); "
        "U ~ (1/pi) L(1,(2/.)) pi(sqrt x) = 0.198 pi(sqrt x) (modes with W = (-2/j)); "
        "lattice model: no sqrt(x) term\n")

    # -----------------------------------------------------------------------------------------
    log("## 3. Hecke modes: M_j(x) = sum_p chi_8(p) cos(j theta_p) and N_j(x) = sum_p cos(j theta_p)\n")
    rn = root_numbers()
    log("Root numbers (Fricke test) and central values of L(s, lambda^j) [level N] and L(s, lambda^j chi_8):")
    log("| j | N | W(lambda^j) | Lambda(1/2) | N | W(lambda^j chi_8) | Lambda(1/2) |")
    log("|---|---|---|---|---|---|---|")
    for j in range(1, 42, 2):
        (N0, W0, c0), (N1, W1, c1) = rn[(0, j)], rn[(1, j)]
        log(f"| {j} | {N0} | {W0:+d} | {c0:.4g} | {N1} | {W1:+d} | {c1:.4g} |")
    log("W(lambda^j) == (-2/j): " + str(all(rn[(0, j)][1] == (1 if j % 8 in (1, 3) else -1) for j in range(1, 42, 2)))
        + ";  W(lambda^j chi_8) == chi_4(j): " + str(all(rn[(1, j)][1] == (1 if j % 4 == 1 else -1) for j in range(1, 42, 2))))
    log("\nprediction: mode bias = (1 - 2 ord_{1/2}) pi(sqrt x)/4 = W pi(sqrt x)/4 (inert primes give +1/4,"
        " a simple central zero gives -1/2)\n")
    log("| j | " + " | ".join(f"M_j/pi(√x) x={grid[i]:.0e}" for i in dec[1:]) +
        " | log-mean M_j | pred W/4 | log-mean N_j | pred W/4 |")
    log("|---|" + "---|" * (len(dec) - 1) + "---|---|---|---|")
    lm_mask = grid >= 10 ** 5
    for j in (1, 3, 5, 7, 9, 11, 13, 15, 21, 31):
        cj = np.cos(j * theta)
        M = at(chi8 * cj)
        N = at(cj)
        log(f"| {j} | " + " | ".join(f"{M[i]/pi_sqrt[i]:+.3f}" for i in dec[1:]) +
            f" | {np.mean(M[lm_mask]/pi_sqrt[lm_mask]):+.3f} | {rn[(1, j)][1]/4:+.2f} "
            f"| {np.mean(N[lm_mask]/pi_sqrt[lm_mask]):+.3f} | {rn[(0, j)][1]/4:+.2f} |")
    log("")
    log("Truncated Fourier series f_J(theta) = (4/pi) sum_{j odd <= J} (-1)^((j-1)/2) cos(j theta)/j "
        "of sgn cos; sum_p chi_8(p) f_J(theta_p) / pi(sqrt x)")
    for J in (1, 3, 9, 31, 101, 301, 1001):
        fJ = np.zeros(len(theta))
        for j in range(1, J + 1, 2):
            fJ += (4 / math.pi) * (-1) ** ((j - 1) // 2) * np.cos(j * theta) / j
        F = at(chi8 * fJ)
        cJ = sum((4 / math.pi) * (-1) ** ((j - 1) // 2) / j for j in range(1, J + 1, 2))
        cW = sum(1 / (math.pi * j) for j in range(1, J + 1, 2))
        log(f"   J = {J:5d}: " + "  ".join(f"x={grid[i]:.0e}: {F[i]/pi_sqrt[i]:+.3f}" for i in dec[1:]) +
            f"   log-mean {np.mean(F[lm_mask]/pi_sqrt[lm_mask]):+.3f}   pred. with W: {cW:+.3f}"
            f"   (without central zeros: {cJ/4:+.3f})")
    log("")

    # -----------------------------------------------------------------------------------------
    log("## 4. Sign changes of prefix sums over the digit index n (p == 1 mod 4 in order)\n")
    log("| sum | terms | sign changes | fraction < 0 | min (at p) | last negative at p | log-mean of sum/pi(sqrt x) |")
    log("|---|---|---|---|---|---|---|")
    for name, s in [("chi_4(a_p)", chi_a), ("control chi_8(p)", chi8), ("sgn Re pi_0", np.sign(re0)),
                    ("chi_4(a_p), a > 1", np.where(a > 1, chi_a, 0)),
                    ("chi_4(a_p), a > 9", np.where(a > 9, chi_a, 0))]:
        cs = np.cumsum(s)
        nz = np.sign(cs[cs != 0])
        ch = int(np.sum(nz[1:] != nz[:-1]))
        neg = np.nonzero(cs < 0)[0]
        imin = int(np.argmin(cs))
        lastneg = f"{p[neg[-1]]}" if len(neg) else "never"
        G = at(s)
        log(f"| {name} | {len(s)} | {ch} | {np.mean(cs < 0):.4f} | {cs[imin]:+d} ({p[imin]}) | {lastneg} | "
            f"{np.mean(G[lm_mask]/pi_sqrt[lm_mask]):+.3f} |")

    log("\n## 5. Consecutive digits (d_k, d_{k+1}), p_k the k-th prime == 1 mod 4 below XMAX\n")
    d = (a % 4 == 3).astype(np.int64)
    n = len(d) - 1
    pairs = np.bincount(2 * d[:-1] + d[1:], minlength=4)
    f1 = d.mean()
    for t, cnt in enumerate(pairs):
        u, v = t >> 1, t & 1
        e = n * (f1 if u else 1 - f1) * (f1 if v else 1 - f1)
        log(f"   ({u},{v}): {cnt}  expected (independent) {e:.0f}  z = {(cnt - e)/math.sqrt(e):+.2f}")
    for L in (3, 4):
        codes = np.zeros(len(d) - L + 1, dtype=np.int64)
        for i in range(L):
            codes = 2 * codes + d[i:len(d) - L + 1 + i]
        cts = np.bincount(codes, minlength=2 ** L)
        e = len(codes) / 2 ** L
        log(f"   blocks of length {L}: chi^2 against uniform = {np.sum((cts - e) ** 2 / e):.1f} "
            f"on {2**L - 1} d.o.f.")
    log(f"\nruntime {time.time()-T0:.1f}s")


if __name__ == "__main__":
    main()
