#!/usr/bin/env python3
"""Numerical evidence on the arithmetic nature of Rokicki's constant.

    rho = sum_{k>=0} d_k / 2^(k+1),   d_k = [p_{k+2} == 3 (mod 4)],

with p_1 = 2, p_2 = 3, ... the primes, so rho = 0.1011001101..._2 = 0.70040013796579773...
The irrationality of rho is proved in this repository (Lean); nothing below proves anything
beyond the rigorous enclosure and the certified continued fraction. Everything else is
*evidence*.

Rigor model.  If r_N = a / 2^N is the partial sum over d_0..d_{N-1} then exactly
r_N <= rho < r_N + 2^-N  (the tail is a sum of at most 2^-N, and it is strictly smaller because
infinitely many digits are 0).  Steps marked "exact" use only integer arithmetic on this
enclosure; floating steps use mpmath with the stated precision.

Subcommands (each prints a Markdown-ready section; results are also written as JSON to the
cache directory):

    value    N = 200000 binary digits, rho to 1000 decimals, certified decimal digit count
    pslq     integer-relation search on 1, x, ..., x^d for rho and three controls
    cf       certified continued fraction of rho and its Gauss-Kuzmin/Khinchin/Levy statistics
    digits   M = 10^6 digits: frequencies, block chi-square, runs, S(n) sign changes,
             subword complexity
    all      everything above, in order (default)

Usage:
    python3 scripts/transcendence_evidence.py [all|value|pslq|cf|digits]
            [--cache DIR] [--jobs J] [--N 200000] [--M 1000000]

Dependencies: Python 3, numpy, mpmath (no scipy/gmpy2/PARI). Output is deterministic apart
from wall-clock timings.
"""

import argparse
import io
import json
import math
import os
import sys
import tempfile
import time
from multiprocessing import Pool

import numpy as np
import mpmath
from mpmath import mp, mpf

sys.set_int_max_str_digits(0)

# ---------------------------------------------------------------------------------------------
# Primes and digits
# ---------------------------------------------------------------------------------------------


def primes_upto(n):
    """All primes <= n, as an int64 numpy array (odd-only Eratosthenes sieve)."""
    if n < 2:
        return np.zeros(0, dtype=np.int64)
    s = np.ones((n + 1) // 2, dtype=bool)  # s[i] <-> 2i+1
    s[0] = False
    for i in range(1, (math.isqrt(n) - 1) // 2 + 1):
        if s[i]:
            p = 2 * i + 1
            s[p * p // 2::p] = False
    return np.concatenate(([2], 2 * np.nonzero(s)[0] + 1)).astype(np.int64)


def sieve_limit(count):
    """A limit L with pi(L) >= count (Rosser-Schoenfeld: p_n < n(ln n + ln ln n) for n >= 6)."""
    n = max(count, 6)
    return int(n * (math.log(n) + math.log(math.log(n)))) + 10


def rho_digits(M):
    """(d_0..d_{M-1} as uint8 array, primes p_2..p_{M+1} as int64 array)."""
    ps = primes_upto(sieve_limit(M + 1))
    odd = ps[1:M + 1]  # p_2 .. p_{M+1}
    assert len(odd) == M
    return (odd & 3 == 3).astype(np.uint8), odd


def bits_to_int(bits):
    """Integer a = sum_k bits[k] 2^(N-1-k)."""
    N = len(bits)
    pad = (-N) % 8
    b = np.packbits(np.concatenate((bits, np.zeros(pad, dtype=np.uint8))))
    return int.from_bytes(b.tobytes(), "big") >> pad


def enclosure(N, cache):
    """(a, N) with a/2^N <= rho < (a+1)/2^N, cached as hex."""
    path = os.path.join(cache, f"rho_enclosure_N{N}.json")
    if os.path.exists(path):
        with open(path) as f:
            js = json.load(f)
        return int(js["a_hex"], 16), N
    bits, odd = rho_digits(N)
    a = bits_to_int(bits)
    with open(path, "w") as f:
        json.dump({"N": N, "last_prime_used": int(odd[-1]),
                   "statement": "a/2^N <= rho < (a+1)/2^N", "a_hex": format(a, "x")}, f)
    return a, N


def rho_mpf(a, N):
    """rho as an mpf at the current precision (exact rational rounded; truncation 2^-N)."""
    return mpf(a) / mpf(2) ** N


def save(cache, name, obj):
    with open(os.path.join(cache, name), "w") as f:
        json.dump(obj, f, indent=1)


def chi2_sf(x, df):
    """Upper tail P(X >= x) of chi-square with df degrees of freedom (mpmath, 30 digits)."""
    with mp.workdps(30):
        return float(mpmath.gammainc(mpf(df) / 2, mpf(x) / 2, mpmath.inf, regularized=True))


# ---------------------------------------------------------------------------------------------
# 1. High-precision value
# ---------------------------------------------------------------------------------------------


def task_value(args):
    t0 = time.time()
    N = args.N
    a, _ = enclosure(N, args.cache)
    bits, odd = rho_digits(N)
    D = int(N * math.log10(2)) + 20
    lo = (a * 10 ** D) >> N            # floor(10^D * a/2^N)
    hi = ((a + 1) * 10 ** D) >> N      # floor(10^D * (a+1)/2^N)
    slo, shi = str(lo).zfill(D), str(hi).zfill(D)
    cert = next((i for i in range(D) if slo[i] != shi[i]), D)
    # rho in [lo, hi) => floor(10^D rho) in [lo, hi], so the common prefix is certified.
    with open(os.path.join(args.cache, f"rho_decimal_N{N}.txt"), "w") as f:
        f.write(f"# rho, certified decimal digits after the point: {cert}\n0.{slo[:cert]}\n")
    first = "".join(map(str, bits[:60]))
    out = {
        "N": N, "last_prime": int(odd[-1]), "binary_start": first,
        "certified_decimals": cert, "ratio": cert / N, "log10_2": math.log10(2),
        "rho_1000": "0." + slo[:1000], "seconds": time.time() - t0,
    }
    save(args.cache, "value.json", out)
    print("## 1. High-precision value\n")
    print(f"- N = {N} binary digits d_0..d_{N-1}, primes p_2..p_{N+1} = {out['last_prime']}")
    print(f"- binary: 0.{first}...")
    print(f"- exact enclosure a/2^N <= rho < (a+1)/2^N stored as hex in "
          f"rho_enclosure_N{N}.json; full decimal in rho_decimal_N{N}.txt")
    print(f"- certified decimal digits: {cert}  (= {cert / N:.5f} N; log10 2 = 0.30103)")
    print(f"- rho to 1000 decimals (truncated, certified):\n")
    s = slo[:1000]
    print("```\n0." + "\n  ".join(s[i:i + 100] for i in range(0, 1000, 100)) + "\n```")
    print(f"\n({out['seconds']:.1f} s)\n")
    return out


# ---------------------------------------------------------------------------------------------
# 2. PSLQ
# ---------------------------------------------------------------------------------------------

DPS = 1200
DEGREES = range(2, 13)
BASE_C = (20, 40, 60)
VERIFY_DPS = 5000

# Controls.  A random degree-5 polynomial with ~10^25 coefficients (fixed seed) gives an
# algebraic number of *large* height that PSLQ must find at C = 40 but not at C = 20.
SMALL_POLY = [1, 0, 0, 0, -3, -1]  # x^5 - 3x - 1, highest degree first


def large_poly():
    rng = np.random.default_rng(20261021)
    coeffs = [int(rng.integers(10 ** 6, 10 ** 7)) * 10 ** 18 + int(rng.integers(0, 10 ** 18))
              for _ in range(6)]
    signs = [1, -1, 1, 1, -1, -1]
    return [c * s for c, s in zip(coeffs, signs)]


def irreducible(coeffs):
    import sympy
    return sympy.Poly(coeffs, sympy.Symbol("x")).is_irreducible


def poly_real_root(coeffs, dps):
    with mp.workdps(dps + 30):
        roots = mpmath.polyroots(coeffs, maxsteps=500, extraprec=4 * dps)
        real = sorted((r.real for r in roots if abs(r.imag) < mpf(10) ** (-dps)), key=abs)
        # largest real root, refined by Newton
        r = max(real)
        r = mpmath.findroot(lambda x: mpmath.polyval(coeffs, x), r)
        return +r


def constant_value(name, dps, enc):
    with mp.workdps(dps + 20):
        if name == "rho":
            return rho_mpf(*enc)
        if name == "pi":
            return +mp.pi
        if name == "alg_small":
            return poly_real_root(SMALL_POLY, dps)
        if name == "alg_large":
            return poly_real_root(large_poly(), dps)
    raise ValueError(name)


class _Tail(io.TextIOBase):
    """Keeps only the last few lines written (mpmath's verbose PSLQ prints every step)."""

    def __init__(self):
        self.buf = ""

    def write(self, s):
        self.buf = (self.buf + s)[-2000:]
        return len(s)


def pslq_job(job):
    name, d, C, dps, enc = job
    mp.dps = dps
    x = constant_value(name, dps, enc)
    vec = [x ** i for i in range(d + 1)]
    tail = _Tail()
    t0 = time.time()
    old = sys.stdout
    sys.stdout = tail
    try:
        rel = mpmath.pslq(vec, maxcoeff=10 ** C, maxsteps=10 ** 6, verbose=True)
    finally:
        sys.stdout = old
    dt = time.time() - t0
    lines = [ln for ln in tail.buf.splitlines() if ln.strip()]
    steps = bound = None
    for ln in lines:
        if ln.startswith("CANCELLING"):
            steps = int(ln.split("step ")[1].split("/")[0])
        if "Norm bound" in ln:
            bound = ln.split("Norm bound: ")[1].strip()
        if ln.startswith("FOUND"):
            steps = int(ln.split("iter ")[1].split("/")[0])
    return {"const": name, "d": d, "C": C, "dps": dps, "relation": rel, "steps": steps,
            "norm_bound": bound, "seconds": dt}


def c_max(d, dps):
    """Largest C (multiple of 10) with d*C + 50 <= 0.75*dps.

    mpmath's default tolerance is 2^-(0.75 prec), i.e. ~0.75*dps digits; a random vector of
    d+1 reals has spurious relations of height ~10^(0.75 dps / d) at that tolerance, so the
    rule of thumb dps >~ d*C + 50 is applied to the *effective* 0.75*dps digits.
    """
    return 10 * int((0.75 * dps - 50) // (10 * d))


def verify_relation(name, rel, enc, dps=VERIFY_DPS):
    with mp.workdps(dps):
        x = constant_value(name, dps, enc)
        val = sum(c * x ** i for i, c in enumerate(rel))
        return mpmath.nstr(abs(val), 5)


def fmt_bound(b):
    if b is None:
        return "-"
    if b == "+inf":
        return b
    b = int(b)
    return str(b) if b < 10 ** 6 else f"{b / 10 ** (len(str(b)) - 1):.2f}e{len(str(b)) - 1}"


def task_pslq(args):
    t0 = time.time()
    enc = enclosure(args.N, args.cache)
    consts = ["rho", "alg_small", "alg_large", "pi"]
    jobs = []
    for name in consts:
        for d in DEGREES:
            Cs = list(BASE_C)
            cm = c_max(d, DPS)
            if cm > max(Cs):
                Cs.append(cm)
            for C in Cs:
                jobs.append((name, d, C, DPS, enc))
    if args.deep_dps:  # one extra, higher-precision run per degree, rho only
        for d in DEGREES:
            jobs.append(("rho", d, c_max(d, args.deep_dps), args.deep_dps, enc))
    # heaviest first for load balancing (steps ~ C (d+1)^2, cost/step ~ (d+1)^2 dps)
    jobs.sort(key=lambda j: -(j[1] + 1) ** 4 * j[2] * j[3])
    with Pool(args.jobs) as pool:
        res = pool.map(pslq_job, jobs, chunksize=1)
    res.sort(key=lambda r: (consts.index(r["const"]), r["dps"], r["d"], r["C"]))
    for r in res:
        if r["relation"] is not None:
            r["check"] = verify_relation(r["const"], r["relation"], enc)
    save(args.cache, "pslq.json", {"dps": DPS, "results": res, "large_poly": large_poly()})

    print("## 2. PSLQ\n")
    print(f"- mpmath.pslq([1, x, ..., x^d], maxcoeff=10^C, maxsteps=10^6) at mp.dps = {DPS} "
          f"(mpmath's default tolerance is 2^-(0.75*prec), about 10^-{int(0.75 * DPS)})")
    print(f"- rho = a/2^N from the N = {args.N} enclosure (error < 2^-{args.N})")
    print("- controls: alg_small = largest real root of x^5 - 3x - 1; "
          "alg_large = the real root of the degree-5 polynomial with coefficients (highest "
          f"degree first) {large_poly()} (height ~10^25; both polynomials are irreducible "
          f"over Q: sympy says {irreducible(SMALL_POLY)}, {irreducible(large_poly())}); pi")
    print("- C = 20, 40, 60 and C_max(d) = 10*floor((0.75*dps - 50)/(10 d)) (rule of thumb "
          "d*C + 50 <= effective digits); deep tier: rho only at "
          f"dps = {args.deep_dps} with C = C_max(d)")
    print(f"- any relation is re-evaluated at {VERIFY_DPS} digits; 'norm bound' is mpmath's "
          "final lower bound for the Euclidean norm of any relation (already divided by 100)\n")
    for name in consts:
        print(f"### {name}\n")
        print("| dps | d | C | result | steps | norm bound | s |")
        print("|---|---|---|---|---|---|---|")
        for r in res:
            if r["const"] != name:
                continue
            if r["relation"] is None:
                out = "None"
            else:
                out = "relation " + str(r["relation"]) + \
                      f" (abs value at {VERIFY_DPS} digits: {r['check']})"
            print(f"| {r['dps']} | {r['d']} | {r['C']} | {out} | {r['steps']} | "
                  f"{fmt_bound(r['norm_bound'])} | {r['seconds']:.1f} |")
        print()
    print(f"({time.time() - t0:.1f} s wall, {args.jobs} processes)\n")
    return res


# ---------------------------------------------------------------------------------------------
# 3. Continued fraction
# ---------------------------------------------------------------------------------------------

KHINCHIN = 2.6854520010653064453
LEVY = math.pi ** 2 / (12 * math.log(2))


def common_cf_prefix(n1, d1, n2, d2):
    """Common prefix of the CF expansions of n1/d1 and n2/d2 (exact Euclid in lockstep).

    If both expansions continue past the prefix, every real number between the two endpoints
    has the same leading partial quotients (cylinder sets are intervals and a rational whose
    expansion is strictly longer than the prefix lies in the interior of the cylinder).
    """
    out = []
    while d1 and d2:
        q1, r1 = divmod(n1, d1)
        q2, r2 = divmod(n2, d2)
        if q1 != q2:
            break
        out.append(q1)
        n1, d1, n2, d2 = d1, r1, d2, r2
    else:
        out.pop()  # one expansion ended: its last quotient is ambiguous, drop it
    return out


def ln_int(q):
    b = q.bit_length()
    if b <= 1000:
        return math.log(q)
    s = b - 64
    return math.log(q >> s) + s * math.log(2)


def task_cf(args):
    t0 = time.time()
    a, N = enclosure(args.N, args.cache)
    cf = common_cf_prefix(a, 1 << N, a + 1, 1 << N)
    n_cert = len(cf)
    with open(os.path.join(args.cache, f"rho_cf_N{N}.txt"), "w") as f:
        f.write(" ".join(map(str, cf)) + "\n")
    # convergent denominators q_n (exact) and ln q_n
    # q_{-1} = 0, q_0 = 1, q_k = a_k q_{k-1} + q_{k-2}; lnq[k] = ln q_k
    lnq = [0.0]
    q_prev, q = 0, 1
    for k in range(1, n_cert):
        q_prev, q = q, cf[k] * q + q_prev
        lnq.append(ln_int(q))
    lnq = np.array(lnq)
    big = cf[1:]
    n = len(big)
    imax = max(range(n), key=lambda i: big[i]) + 1
    counts = [sum(1 for x in big if x == k) for k in (1, 2, 3, 4)]
    counts.append(n - sum(counts))
    gk = [math.log2(1 + 1 / (k * (k + 2))) for k in (1, 2, 3, 4)]
    gk.append(1 - sum(gk))
    chi = sum((c - n * p) ** 2 / (n * p) for c, p in zip(counts, gk))
    logs = np.log(np.array(big, dtype=float))
    geo = {m: math.exp(logs[:m].mean()) for m in (100, 1000, 10000, n)}
    levy = {m: lnq[m] / m for m in (100, 1000, 10000, n - 1)}
    # mu_n = ln q_{n+1} / ln q_n ; mu[k] corresponds to n = k (undefined while q_n = 1)
    with np.errstate(divide="ignore", invalid="ignore"):
        mu = lnq[1:] / lnq[:-1]
    idx = np.arange(len(mu))
    sel = idx >= 100
    order = idx[sel][np.argsort(-mu[sel], kind="stable")][:10]
    top10 = [(int(k), float(mu[k]), int(cf[k + 1])) for k in order]
    mu_ranges = {}
    for lo_n, hi_n in ((100, 1000), (1000, 10000), (10000, len(mu))):
        seg = mu[lo_n:hi_n]
        k = int(np.argmax(seg)) + lo_n
        mu_ranges[f"{lo_n}..{hi_n - 1}"] = (k, float(mu[k]))
    K = big[imax - 1]
    p_max = 1 - (1 - math.log2(1 + 1 / K)) ** n  # P(max >= K) for n i.i.d. Gauss-Kuzmin draws
    out = {"N": N, "certified": n_cert, "first60": cf[:60], "max_pq": big[imax - 1],
           "max_index": imax, "counts": counts, "gauss_kuzmin": gk, "chi2_gk": chi,
           "p_gk": chi2_sf(chi, 4), "geo": geo, "levy": levy, "mu_top10": top10,
           "mu_ranges": mu_ranges, "p_max": p_max, "lnq_last": float(lnq[-1]),
           "seconds": time.time() - t0}
    save(args.cache, "cf.json", out)

    print("## 3. Continued fraction (exact)\n")
    print(f"- endpoints a/2^{N} and (a+1)/2^{N}; common CF prefix = {n_cert} partial quotients "
          f"a_0..a_{n_cert - 1} (certified); ln q_{n_cert - 1} = {lnq[-1]:.1f} "
          f"(vs N ln2 / 2 = {N * math.log(2) / 2:.1f})")
    print(f"- first 60: [{cf[0]}; " + ", ".join(map(str, cf[1:60])) + ", ...]")
    print(f"- largest partial quotient: a_{imax} = {K}; under Gauss-Kuzmin "
          f"P(max(a_1..a_{n}) >= {K}) = {p_max:.2f}")
    top = sorted(range(1, n_cert), key=lambda k: -cf[k])[:5]
    print("- five largest: " + ", ".join(f"a_{k} = {cf[k]}" for k in top))
    print(f"\n| a_n | count (n = 1..{n}) | observed | Gauss-Kuzmin |")
    print("|---|---|---|---|")
    for lab, c, p in zip(("1", "2", "3", "4", ">=5"), counts, gk):
        print(f"| {lab} | {c} | {c / n:.5f} | {p:.5f} |")
    print(f"\nchi-square vs Gauss-Kuzmin: {chi:.2f} (4 df), p = {out['p_gk']:.3f}\n")
    print("| n | (a_1...a_n)^(1/n) | Khinchin | (1/n) ln q_n | Levy |")
    print("|---|---|---|---|---|")
    for (m, g), (m2, l) in zip(geo.items(), levy.items()):
        print(f"| {m} | {g:.5f} | {KHINCHIN:.5f} | {l:.5f} (n={m2}) | {LEVY:.5f} |")
    print("\nmu_n = ln q_{n+1} / ln q_n, ten largest over n >= 100 (since "
          "|rho - p_n/q_n| ~ 1/(q_n q_{n+1}) = q_n^-(1 + mu_n), the irrationality exponent is "
          "1 + limsup mu_n; a generic number has mu_n -> 1):\n")
    print("| n | mu_n | a_{n+1} |")
    print("|---|---|---|")
    for k, m, aa in top10:
        print(f"| {k} | {m:.5f} | {aa} |")
    print("\nmax mu_n by range: " + "; ".join(f"n in {r}: mu_{k} = {m:.5f}"
                                             for r, (k, m) in mu_ranges.items()))
    print(f"\n({out['seconds']:.1f} s)\n")
    return out


# ---------------------------------------------------------------------------------------------
# 4. Digit statistics
# ---------------------------------------------------------------------------------------------


def overlapping_codes(bits, L, circular=False):
    b = bits.astype(np.int64)
    if circular:
        b = np.concatenate((b, b[:L - 1]))
    m = len(b) - L + 1
    code = np.zeros(m, dtype=np.int64)
    for j in range(L):
        code = (code << 1) | b[j:j + m]
    return code


def task_digits(args):
    t0 = time.time()
    M = args.M
    bits, odd = rho_digits(M)
    out = {"M": M, "last_prime": int(odd[-1])}
    print("## 4. Digit statistics\n")
    print(f"- M = {M} digits d_0..d_{M - 1} (primes p_2..p_{M + 1} = {odd[-1]})\n")

    # 4a. frequency of 1 and the Chebyshev bias
    ones = int(bits.sum())
    zeros = M - ones
    chi = np.where(odd & 3 == 1, 1, -1)
    S = np.cumsum(chi)  # S at p_{k+2}: sum over primes 3..p_{k+2} of chi_4(p)
    out.update(ones=ones, zeros=zeros, S_end=int(S[-1]))
    print(f"### Frequencies\n\n#1 = {ones}, #0 = {zeros}, freq(1) = {ones / M:.6f}; "
          f"#1 - #0 = {ones - zeros} = -S({odd[-1]}) with S(x) = sum_(p<=x) chi_4(p) "
          f"= {int(S[-1])}  [check: {ones - zeros == -int(S[-1])}]; "
          f"(#1-#0)/sqrt(M) = {(ones - zeros) / math.sqrt(M):.3f}\n")

    # 4b. block frequencies
    print("### Block frequencies\n")
    print("Non-overlapping blocks (floor(M/L) blocks, 2^L - 1 df) and Good's serial test on "
          "overlapping circular blocks (grad psi^2_L = psi^2_L - psi^2_{L-1}, 2^{L-1} df). "
          "z = (chi2 - df)/sqrt(2 df).\n")
    print("| L | blocks | chi2 (non-ovl) | df | z | p | grad psi^2 (ovl) | df | z | p | "
          "min/max ovl count / expected |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    blocks = []
    psi_prev = 0.0
    for L in range(1, 13):
        nb = M // L
        w = 1 << np.arange(L - 1, -1, -1, dtype=np.int64)
        codes = bits[:nb * L].reshape(nb, L).astype(np.int64) @ w
        cnt = np.bincount(codes, minlength=1 << L)
        e = nb / (1 << L)
        x2 = float(((cnt - e) ** 2).sum() / e)
        df = (1 << L) - 1
        oc = np.bincount(overlapping_codes(bits, L, circular=True), minlength=1 << L)
        psi = float((oc.astype(float) ** 2).sum() * (1 << L) / M - M)
        g = psi - psi_prev
        gdf = 1 << (L - 1)
        psi_prev = psi
        eo = M / (1 << L)
        row = dict(L=L, blocks=nb, chi2=x2, df=df, z=(x2 - df) / math.sqrt(2 * df),
                   p=chi2_sf(x2, df), grad_psi2=g, gdf=gdf,
                   gz=(g - gdf) / math.sqrt(2 * gdf), gp=chi2_sf(g, gdf),
                   omin=float(oc.min() / eo), omax=float(oc.max() / eo))
        blocks.append(row)
        print(f"| {L} | {nb} | {x2:.1f} | {df} | {row['z']:+.2f} | {row['p']:.3f} | "
              f"{g:.1f} | {gdf} | {row['gz']:+.2f} | {row['gp']:.3f} | "
              f"{row['omin']:.3f} / {row['omax']:.3f} |")
    out["blocks"] = blocks

    # 4b'. the bias is the Lemke Oliver-Soundararajan effect: consecutive primes avoid
    # repeating their residue class.  Observed P(d_{k+1} = d_k) by window of primes, against
    # the leading term of their conjecture, 1/2 - (1/4) loglog x / log x (q = 4).
    print("\n### Consecutive-prime bias (Lemke Oliver-Soundararajan)\n")
    print("| digits k in | primes up to | P(d_{k+1} = d_k) | (P - 1/2) sqrt(pairs) | "
          "LO-S leading term at window end |")
    print("|---|---|---|---|---|")
    same = (bits[1:] == bits[:-1])
    los = []
    W = 10
    for w in range(W):
        lo_k, hi_k = w * (M - 1) // W, (w + 1) * (M - 1) // W
        ps = float(same[lo_k:hi_k].mean())
        x = float(odd[hi_k])
        lead = 0.5 - 0.25 * math.log(math.log(x)) / math.log(x)
        los.append((lo_k, hi_k, int(odd[hi_k]), ps, lead))
        print(f"| [{lo_k}, {hi_k}) | {int(odd[hi_k])} | {ps:.5f} | "
              f"{(ps - 0.5) * math.sqrt(hi_k - lo_k):+.1f} | {lead:.5f} |")
    out["lo_s_windows"] = los

    # Order-1 Markov model fitted to the pair frequencies: does it explain the blocks?
    n01 = int(((bits[:-1] == 0) & (bits[1:] == 1)).sum())
    n10 = int(((bits[:-1] == 1) & (bits[1:] == 0)).sum())
    n00 = int(((bits[:-1] == 0) & (bits[1:] == 0)).sum())
    n11 = int(((bits[:-1] == 1) & (bits[1:] == 1)).sum())
    P = np.array([[n00, n01], [n10, n11]], dtype=float)
    P /= P.sum(axis=1, keepdims=True)
    pi1 = P[0, 1] / (P[0, 1] + P[1, 0])
    stat = np.array([1 - pi1, pi1])
    print(f"\nOrder-1 Markov fit: P(0->0) = {P[0, 0]:.5f}, P(1->1) = {P[1, 1]:.5f}. "
          "Non-overlapping L-blocks against the Markov expectation (df = 2^L - 3):\n")
    print("| L | chi2 vs Markov-1 | df | z | p |")
    print("|---|---|---|---|---|")
    mk = []
    for L in range(2, 13):
        nb = M // L
        w = 1 << np.arange(L - 1, -1, -1, dtype=np.int64)
        codes = bits[:nb * L].reshape(nb, L).astype(np.int64) @ w
        cnt = np.bincount(codes, minlength=1 << L)
        allw = (np.arange(1 << L)[:, None] >> np.arange(L - 1, -1, -1)[None, :]) & 1
        e = stat[allw[:, 0]].copy()
        for j in range(1, L):
            e *= P[allw[:, j - 1], allw[:, j]]
        e *= nb
        x2 = float(((cnt - e) ** 2 / e).sum())
        df = (1 << L) - 3
        mk.append((L, x2, df, (x2 - df) / math.sqrt(2 * df), chi2_sf(x2, df)))
        print(f"| {L} | {x2:.1f} | {df} | {mk[-1][3]:+.2f} | {mk[-1][4]:.3g} |")
    out["markov1"] = dict(P00=P[0, 0], P11=P[1, 1], tests=mk)

    # 4c. longest runs
    print("\n### Longest runs\n")
    edges = np.flatnonzero(np.diff(bits.astype(np.int8))) + 1
    starts = np.concatenate(([0], edges))
    ends = np.concatenate((edges, [M]))
    lens = ends - starts
    vals = bits[starts]
    runs = {}
    for v in (0, 1):
        m = vals == v
        i = int(np.argmax(np.where(m, lens, -1)))
        k = int(starts[i])
        runs[v] = dict(length=int(lens[i]), start_index=k, first_prime=int(odd[k]),
                       last_prime=int(odd[k + lens[i] - 1]),
                       count_of_max=int(((lens == lens[i]) & m).sum()))
        print(f"- longest run of {v}s: length {lens[i]} at digits d_{k}..d_{k + lens[i] - 1} "
              f"(primes {odd[k]}..{odd[k + lens[i] - 1]}, all = {3 if v else 1} mod 4)")
    print(f"- heuristic: log2(M) = {math.log2(M):.2f}; for a fair coin the longest run of a "
          f"given symbol is about log2(M/2) = {math.log2(M / 2):.2f} (sd ~ 1.87)")
    for v in (0, 1):
        st_ = P[v, v]
        nr = M * stat[v] * (1 - st_)  # expected number of runs of symbol v
        print(f"- under the order-1 Markov fit (stay probability {st_:.4f}) the longest run "
              f"of {v}s is about log(#runs)/log(1/stay) + 1 = "
              f"{math.log(nr) / math.log(1 / st_) + 1:.1f}")
    out["runs"] = runs

    # 4d. S(n) sign structure.  S(n) = sum_{p <= n} chi_4(p) is constant on [p_j, p_{j+1}).
    print("\n### Sign of S(n) = sum_{p<=n} chi_4(p)\n")
    X = int(odd[-1])
    nxt = np.concatenate((odd[1:], [X + 1]))   # S(n) = S[j] for p_j <= n < nxt[j]
    gap = (nxt - odd).astype(np.int64)
    pos = S > 0
    total = X - 2  # integers n in [3, X]  (S(1)=S(2)=0 omitted)
    frac_neg = gap[S < 0].sum() / total
    frac_zero = gap[S == 0].sum() / total
    frac_pos = gap[S > 0].sum() / total
    logw = np.log(nxt / odd)
    log_neg = logw[S < 0].sum() / logw.sum()
    # maximal intervals of n with S(n) > 0
    d = np.diff(np.concatenate(([0], pos.astype(np.int8), [0])))
    st = np.flatnonzero(d == 1)
    en = np.flatnonzero(d == -1)  # exclusive
    intervals = [(int(odd[s]), int(nxt[e - 1] - 1), int(S[s:e].max())) for s, e in zip(st, en)]
    sgn = np.sign(S)
    nz = sgn[sgn != 0]
    changes = int((nz[1:] != nz[:-1]).sum())
    out.update(frac_neg=float(frac_neg), frac_zero=float(frac_zero), frac_pos=float(frac_pos),
               log_density_neg=float(log_neg), pos_intervals=intervals, sign_changes=changes,
               S_min=int(S.min()), S_max=int(S.max()))
    print(f"- range 3 <= n <= {X}: fraction of n with S(n) < 0: {frac_neg:.6f}, = 0: "
          f"{frac_zero:.6f}, > 0: {frac_pos:.6f}")
    print(f"- logarithmic density of S(n) < 0 on [3, {X}] (weight dn/n): {log_neg:.6f} "
          f"(Rubinstein-Sarnak, under GRH + LI, for x -> oo: delta(4;3,1) = 0.9959)")
    print(f"- strict sign changes of S (zeros skipped): {changes}; "
          f"min S = {S.min()}, max S = {S.max()}")
    print(f"- maximal intervals of n with S(n) > 0 (pi(n;4,1) > pi(n;4,3)): {len(intervals)}; "
          f"first starts at n = {intervals[0][0] if intervals else None}")
    groups = []
    for a_, b_, m_ in intervals:
        if groups and a_ - groups[-1][1] < 10 ** 5:
            g = groups[-1]
            groups[-1] = [g[0], b_, max(g[2], m_), g[3] + 1]
        else:
            groups.append([a_, b_, m_, 1])
    print("- clusters (intervals closer than 10^5 merged): " + "; ".join(
        f"[{g[0]}, {g[1]}] ({g[3]} intervals, max S = {g[2]})" for g in groups))
    out["pos_clusters"] = groups

    # 4e. subword complexity
    print("\n### Subword complexity\n")
    print("| L | p(L) | 2^L | expected for random (M-L+1 windows) |")
    print("|---|---|---|---|")
    comp = []
    for L in range(1, 21):
        c = overlapping_codes(bits, L)
        pL = int(np.count_nonzero(np.bincount(c, minlength=1 << L)))
        W = M - L + 1
        expct = (1 << L) * (1 - math.exp(W * math.log1p(-1 / (1 << L))))
        comp.append((L, pL, 1 << L, expct))
        print(f"| {L} | {pL} | {1 << L} | {expct:.1f} |")
    out["complexity"] = comp
    for L in (15, 16):
        c = np.bincount(overlapping_codes(bits, L), minlength=1 << L)
        miss = [format(i, f"0{L}b") for i in np.flatnonzero(c == 0)]
        out[f"missing_{L}"] = miss
        if len(miss) <= 16:
            print(f"\nmissing blocks of length {L}: " + ", ".join(miss))
    out["seconds"] = time.time() - t0
    save(args.cache, "digits.json", out)
    print(f"\n({out['seconds']:.1f} s)\n")
    return out


# ---------------------------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("task", nargs="?", default="all",
                    choices=["all", "value", "pslq", "cf", "digits"])
    ap.add_argument("--cache", default=os.environ.get(
        "RHO_CACHE", os.path.join(tempfile.gettempdir(), "rokicki-transcendence-cache")))
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    ap.add_argument("--N", type=int, default=200000, help="binary digits for the enclosure")
    ap.add_argument("--M", type=int, default=1000000, help="digits for the statistics")
    ap.add_argument("--deep-dps", type=int, default=2500,
                    help="precision of the extra rho-only PSLQ tier (0 = skip)")
    args = ap.parse_args()
    os.makedirs(args.cache, exist_ok=True)
    tasks = {"value": task_value, "pslq": task_pslq, "cf": task_cf, "digits": task_digits}
    for name in (tasks if args.task == "all" else [args.task]):
        tasks[name](args)
        sys.stdout.flush()


if __name__ == "__main__":
    main()
