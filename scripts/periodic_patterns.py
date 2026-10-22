#!/usr/bin/env python3
"""Periodic stretches in the binary digits of Rokicki's constant.

    rho = sum_{k>=0} d_k / 2^(k+1),   d_k = [p_{k+2} == 3 (mod 4)],   p_1 = 2, p_2 = 3, ...

A *P-periodic stretch* of length L starting at n is a block d_n, ..., d_{n+L-1} with
d_{i+P} = d_i for n <= i < n + L - P; its *excess* is E = L - P (the number of digits forced by
the first P). Writing e_i = [d_{i+P} = d_i], maximal P-periodic stretches of positive excess are
exactly the maximal runs of 1s in e: a run of r ones starting at n is a stretch with E = r.

Why this is the Diophantine statistic (see research/diophantine.md, section 1). With
T_n = sum_j d_{n+j} 2^{-j-1} the tails and Q = 2^n (2^P - 1),
    Q rho = (integer) + T_{n+P} - T_n,   |T_{n+P} - T_n| <= 2^{-E},
so ||Q rho|| <= 2^{-E}, i.e. |rho - a/Q| <= Q^{-(1 + E / log2 Q)} with log2 Q < n + P.
Conversely a good approximation with denominator 2^s q' (q' odd, P = ord_{q'} 2) produces a
P-periodic stretch starting at s whose excess is about (mu - 1) log2 q (up to O(P)). So the
quantity measuring "how Liouville-like" a stretch is is E / (n + P), and mu(rho) = 2 restricted
to the denominators 2^n (2^P - 1) means E / (n + P) -> 0 along every period P.

Random model (heuristic). For i.i.d. fair digits and fixed P the indicators e_i are i.i.d. fair
bits (for fixed d_0..d_{P-1} the map d -> e is a bijection on windows), so the number of maximal
stretches with excess >= t is about M 2^{-(t+1)} and the longest has excess
R ~ log2(M/2) + gamma/ln 2 - 1/2 = log2 M - 0.667 (std about 1.87), i.e.
L_max(P) ~ P + log2 M - 0.67 ~ P + 22.6 for M = 10^7. The digits of rho are not fair coin flips
at small P (Lemke Oliver-Soundararajan: consecutive primes avoid repeating their residue), so we
also give the prediction with the observed match frequency f = mean(e):
R ~ log_{1/f}(M (1 - f)) + gamma/ln(1/f) - 1/2.

Rigor. The digits are exact (integer sieve, checked against pi(10^8) = 5761455). Everything
labelled "model" is heuristic. The Breusch check (for every integer 7 <= x <= X both classes
mod 4 have a prime in (x, 2x]) is exact over the stated range.

Usage:
    python3 scripts/periodic_patterns.py [--M 10000000] [--Pmax 64] [--nmin 100] [--cache DIR]

Dependencies: Python 3, numpy. Runtime about a minute for M = 10^7.
"""

import argparse
import json
import math
import os
import sys
import tempfile
import time

import numpy as np

EULER_GAMMA = 0.5772156649015329


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


def runs_of_ones(e):
    """(starts, lengths) of the maximal runs of True in the boolean array e."""
    x = np.concatenate(([0], e.view(np.int8), [0]))
    dx = np.diff(x)
    starts = np.flatnonzero(dx == 1)
    ends = np.flatnonzero(dx == -1)
    return starts, ends - starts


def minimal_period(word):
    """Smallest p >= 1 with word[i + p] = word[i] for all valid i."""
    n = len(word)
    for p in range(1, n + 1):
        if np.array_equal(word[p:], word[:n - p]):
            return p
    return n


def expected_longest(M, f):
    """Mean longest run of successes in M Bernoulli(f) trials (Schilling's approximation)."""
    lf = math.log(1 / f)
    return math.log(M * (1 - f)) / lf + EULER_GAMMA / lf - 0.5


def tail_prob_longest(M, f, r):
    """P(longest run >= r) for M Bernoulli(f) trials, Poisson clumping approximation."""
    lam = M * (1 - f) * f ** r
    return -math.expm1(-lam)


def breusch_check(primes):
    """Exact check of Breusch's theorem below the sieve limit: returns (X, data) such that for
    every integer 7 <= x < X each class 1, 3 mod 4 has a prime in (x, 2x]. If q < q' are
    consecutive primes of a class, the first prime of that class above any x in [q, q') is q', so
    the statement holds for all such x >= 7 iff q' <= 2 max(q, 7)."""
    data, X = {}, None
    for a in (1, 3):
        cls = primes[(primes & 3) == a]
        q, qn = cls[:-1], cls[1:]
        lo = np.maximum(q, 7)
        rel = qn > 7  # pairs with q' <= 7 cover no x >= 7
        bad = np.flatnonzero(rel & (qn > 2 * lo))
        data[a] = {"violations": int(bad.size),
                   "max_ratio_next_over_prev": float(np.max(qn[rel] / lo[rel]))}
        X = int(cls[-1]) if X is None else min(X, int(cls[-1]))
    return X, data


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--M", type=int, default=10_000_000)
    ap.add_argument("--Pmax", type=int, default=64)
    ap.add_argument("--nmin", type=int, default=100)
    ap.add_argument("--cache", default=os.environ.get(
        "RHO_CACHE", os.path.join(tempfile.gettempdir(), "rokicki-periodic-cache")))
    args = ap.parse_args()
    os.makedirs(args.cache, exist_ok=True)
    M, Pmax, nmin = args.M, args.Pmax, args.nmin
    t0 = time.time()

    lim = 2 * sieve_limit(M + 1)  # up to 2 p_{M+1}: pi(2p) - pi(p) at every start is exact
    ps = primes_upto(lim)
    odd = ps[1:M + 1]  # p_2 .. p_{M+1}; odd[n] is the prime behind d_n
    assert len(odd) == M
    d = (odd & 3 == 3).astype(np.uint8)
    assert "".join(map(str, d[:10])) == "1011001101"
    if lim >= 10 ** 8:
        assert int(np.searchsorted(ps, 10 ** 8, side="right")) == 5761455
    out = {"M": M, "last_prime": int(odd[-1]), "sieve_limit": lim}
    print(f"## Periodic stretches in the first M = {M} digits\n")
    chk = ", pi(10^8) = 5761455 checked" if lim >= 10 ** 8 else ""
    print(f"- digits d_0..d_{M - 1} from the primes 3..{odd[-1]} (exact; sieve to {lim}{chk})")
    print(f"- frequency of 1s: {d.mean():.6f}\n")

    # ---- runs (P = 1), with the Breusch bound -----------------------------------------------
    # pi(2p) - pi(p) for the prime p = odd[n] behind the start of each run.
    def pi_of(x):
        return np.searchsorted(ps, x, side="right")

    starts, lens = runs_of_ones(d[1:] == d[:-1])  # a run of r equalities = r + 1 equal digits
    run_len = lens + 1
    # maximal runs of equal digits also include singletons; only the long ones matter here
    order = np.argsort(-run_len, kind="stable")[:10]
    print("### Runs of equal digits (strings of congruent consecutive primes)\n")
    print("| rank | run length L | start n | digit | first prime p | pi(2p) - pi(p) "
          "| L / (pi(2p)-pi(p)) | L / n |")
    print("|---|---|---|---|---|---|---|---|")
    top_runs = []
    for rank, i in enumerate(order, 1):
        n, L = int(starts[i]), int(run_len[i])
        p = int(odd[n])
        gap = int(pi_of(2 * p) - pi_of(p)) if 2 * p <= lim else None
        top_runs.append({"n": n, "L": L, "digit": int(d[n]), "p": p, "breusch_bound": gap})
        g = f"{gap}" if gap is not None else "n/a"
        rr = f"{L / gap:.2e}" if gap else "n/a"
        print(f"| {rank} | {L} | {n} | {d[n]} | {p} | {g} | {rr} | {L / max(n, 1):.2e} |")
    out["top_runs"] = top_runs
    # worst ratio of run length to the Breusch bound, and run length / n, over n >= nmin
    sel = starts >= nmin
    sp, sl = starts[sel], run_len[sel]
    pp = odd[sp]
    keep = 2 * pp <= lim
    gaps = pi_of(2 * pp[keep]) - pi_of(pp[keep])
    ratio_b = sl[keep] / gaps
    jb = int(np.argmax(ratio_b))
    jn = int(np.argmax(sl / (sp + 1)))
    print(f"\nOver runs starting at n >= {nmin}: max L / (pi(2p) - pi(p)) = {ratio_b[jb]:.3e} "
          f"(run of {sl[keep][jb]} at n = {sp[keep][jb]}); max L / (n + 1) = "
          f"{sl[jn] / (sp[jn] + 1):.4f} (run of {sl[jn]} at n = {sp[jn]}).")
    out["runs_max_L_over_breusch"] = float(ratio_b[jb])
    out["runs_max_L_over_n"] = float(sl[jn] / (sp[jn] + 1))
    # longest run of each digit
    for dig in (0, 1):
        m = d[starts] == dig
        k = int(np.argmax(np.where(m, run_len, 0)))
        print(f"- longest run of {dig}s: {run_len[k]} digits from n = {starts[k]} "
              f"(primes {odd[starts[k]]} .. {odd[starts[k] + run_len[k] - 1]})")
    print()

    # ---- Breusch check ----------------------------------------------------------------------
    X, bc = breusch_check(ps)
    out["breusch_check"] = {"X": X, **{str(k): v for k, v in bc.items()}}
    print(f"Breusch's theorem checked exactly for 7 <= x < {X}: violations "
          f"class 1: {bc[1]['violations']}, class 3: {bc[3]['violations']}; "
          f"max (next prime in class)/max(q, 7): class 1 {bc[1]['max_ratio_next_over_prev']:.4f},"
          f" class 3 {bc[3]['max_ratio_next_over_prev']:.4f}.\n")

    # ---- all periods ------------------------------------------------------------------------
    print(f"### Longest P-periodic stretch, P = 1..{Pmax}\n")
    print("E = L - P is the excess; 'fair' is the i.i.d. fair-bit prediction for the longest "
          "excess, 'f-model' uses the observed match frequency f = P(d_{i+P} = d_i); "
          "p = P(longest excess >= observed) under the f-model; 'min per' is the minimal period "
          f"of the record stretch; last column: max E/(n+P) over stretches starting at "
          f"n >= {nmin}.\n")
    print("| P | f | L_max | E_max | fair | f-model | p | start n | prime p_{n+2} | min per "
          f"| max E/(n+P), n >= {nmin} | at n |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    fair = expected_longest(M, 0.5)
    per_P = []
    best_global = (-1.0, None)
    bins = [10 ** k for k in range(2, int(math.log10(M)) + 2)]
    best_by_bin = {b: (-1.0, None) for b in bins[:-1]}
    top_ratios = []
    count_thresholds = list(range(14, 27, 2))
    tail_counts = {}
    for P in range(1, Pmax + 1):
        e = d[P:] == d[:-P]
        f = float(e.mean())
        st, rl = runs_of_ones(e)
        k = int(np.argmax(rl))
        n0, E0 = int(st[k]), int(rl[k])
        L0 = E0 + P
        mp_ = minimal_period(d[n0:n0 + L0])
        expf = expected_longest(len(e), f)
        pval = tail_prob_longest(len(e), f, E0)
        # exponent proxy E/(n+P) over n >= nmin: a run (s, r) contributes, at n = max(s, nmin),
        # excess r - (n - s) (later starts inside the run are dominated).
        n_eff = np.maximum(st, nmin)
        E_eff = rl - (n_eff - st)
        ok = E_eff > 0
        ratio = np.where(ok, E_eff / (n_eff + P), 0.0)
        j = int(np.argmax(ratio))
        per_P.append({"P": P, "f": f, "L_max": L0, "E_max": E0, "start": n0,
                      "prime": int(odd[n0]), "min_period": mp_, "fair": fair,
                      "f_model": expf, "p_value": pval,
                      "max_ratio": float(ratio[j]), "max_ratio_n": int(n_eff[j]),
                      "max_ratio_E": int(E_eff[j])})
        print(f"| {P} | {f:.4f} | {L0} | {E0} | {fair:.1f} | {expf:.1f} | {pval:.2f} | {n0} "
              f"| {odd[n0]} | {mp_} | {ratio[j]:.4f} | {n_eff[j]} |")
        if ratio[j] > best_global[0]:
            best_global = (float(ratio[j]), (P, int(n_eff[j]), int(E_eff[j])))
        for lo, hi in zip(bins[:-1], bins[1:]):
            m = ok & (n_eff >= lo) & (n_eff < hi)
            if m.any():
                jj = int(np.argmax(np.where(m, ratio, 0.0)))
                if ratio[jj] > best_by_bin[lo][0]:
                    best_by_bin[lo] = (float(ratio[jj]), (P, int(n_eff[jj]), int(E_eff[jj])))
        idx = np.argsort(-ratio)[:5]
        top_ratios += [(float(ratio[i]), P, int(n_eff[i]), int(E_eff[i])) for i in idx]
        naive = np.where(ok, (E_eff + P) / (n_eff + 1), 0.0)
        jn_ = int(np.argmax(naive))
        if naive[jn_] > out.get("naive_max", (0.0,))[0]:
            out["naive_max"] = (float(naive[jn_]), P, int(n_eff[jn_]), int(E_eff[jn_]))
        tail_counts[P] = [int(np.count_nonzero(rl >= t)) for t in count_thresholds]
    out["per_P"] = per_P

    print(f"\nmax over P <= {Pmax} and stretches starting at n >= {nmin} of E/(n+P): "
          f"{best_global[0]:.4f} (P, n, E) = {best_global[1]}\n")
    out["max_ratio"] = {"value": best_global[0], "P_n_E": best_global[1]}
    v, P_, n_, E_ = out["naive_max"]
    print(f"(The naive statistic L/(n+1) = (E+P)/(n+1) has maximum {v:.4f} at (P, n, E) = "
          f"({P_}, {n_}, {E_}); it is dominated by the trivial P/(n+1), since every block of "
          f"length P is P-periodic, and is not a Diophantine quantity.)\n")

    print("Max of E/(n+P) over all P <= %d, by starting position (random model: "
          "about log2(n)/n):\n" % Pmax)
    print("| n in | max E/(n+P) | (P, n, E) | log2(n_lo)/n_lo |")
    print("|---|---|---|---|")
    out["max_ratio_by_bin"] = {}
    for lo, hi in zip(bins[:-1], bins[1:]):
        v, w = best_by_bin[lo]
        out["max_ratio_by_bin"][f"{lo}-{hi}"] = {"value": v, "P_n_E": w}
        print(f"| [{lo}, {hi}) | {v:.5f} | {w} | {math.log2(lo) / lo:.5f} |")

    top_ratios.sort(reverse=True)
    print(f"\nTen largest E/(n+P) (n >= {nmin}, P <= {Pmax}):\n")
    print("| E/(n+P) | P | n | E | approximation |rho - a/Q| <= Q^-(1+E/(n+P)), Q = "
          "2^n(2^P-1) |")
    print("|---|---|---|---|---|")
    for v, P, n, E in top_ratios[:10]:
        print(f"| {v:.4f} | {P} | {n} | {E} | exponent >= {1 + v:.4f} |")

    print("\nNumber of maximal stretches with excess E >= t, versus the fair model "
          "(M - P) 2^-(t+1):\n")
    sel_P = [P for P in (1, 2, 3, 4, 5, 8, 16, 32, 64) if P <= Pmax]
    print("| t | " + " | ".join(f"P={P}" for P in sel_P) + " | fair model |")
    print("|---|" + "---|" * (len(sel_P) + 1))
    for i, t in enumerate(count_thresholds):
        row = " | ".join(str(tail_counts[P][i]) for P in sel_P)
        print(f"| {t} | {row} | {M * 2.0 ** -(t + 1):.1f} |")
    out["tail_counts"] = {str(P): dict(zip(count_thresholds, tail_counts[P])) for P in sel_P}

    # P = 1, 2 against an order-2 Markov model of the repeat/switch indicator: d_{i+1} = d_i
    # iff the gap p_{i+3} - p_{i+2} is 0 mod 4, so runs (P = 1) are strings of gaps = 0 mod 4 and
    # alternating stretches (the nonconstant P = 2 pattern) are strings of gaps = 2 mod 4.
    rep = d[1:] == d[:-1]
    print("\nP = 1, 2 against an order-2 Markov model of the indicator [d_{i+1} = d_i] "
          "(heuristic):\n")
    print("| t | runs with >= t repeats | Markov | alternating stretches with >= t+1 switches "
          "| Markov |")
    print("|---|---|---|---|---|")
    stats = {}
    for name, x in (("repeat", rep), ("switch", ~rep)):
        f1 = float(x.mean())
        f2 = float((x[1:] & x[:-1]).sum() / x[:-1].sum())
        stats[name] = (f1, f2, runs_of_ones(x)[1])
    (r1, r2, rl_r), (s1, s2, rl_s) = stats["repeat"], stats["switch"]
    for t in range(10, 25, 2):
        print(f"| {t} | {int((rl_r >= t).sum())} | {M * (1 - r1) * r1 * r2 ** (t - 1):.1f} "
              f"| {int((rl_s >= t + 1).sum())} | {M * (1 - s1) * s1 * s2 ** t:.1f} |")
    print(f"\nP(repeat) = {r1:.4f}, P(repeat | repeat) = {r2:.4f}, P(switch | switch) = {s2:.4f}.")
    out["markov"] = {"repeat": [r1, r2], "switch": [s1, s2]}

    # summary over P of (L_max - P) - model
    dev = np.array([r["E_max"] - r["f_model"] for r in per_P])
    print(f"\nE_max - f-model over P = 1..{Pmax}: mean {dev.mean():+.2f}, sd {dev.std():.2f}, "
          f"min {dev.min():+.1f}, max {dev.max():+.1f} (model sd about 1.87).")
    out["E_max_minus_model"] = {"mean": float(dev.mean()), "sd": float(dev.std())}
    out["seconds"] = time.time() - t0
    with open(os.path.join(args.cache, f"periodic_M{M}_P{Pmax}.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"\n({out['seconds']:.1f} s)")


if __name__ == "__main__":
    sys.exit(main())
