# Rokicki's constant: numerical evidence on transcendence

`ρ = Σ_{k≥0} d_k / 2^(k+1)` with `d_k = [p_{k+2} ≡ 3 (mod 4)]` (`p_1 = 2`), so
`ρ = 0.1011001101…₂ = 0.70040013796579773…`. Irrationality of ρ is proved in this repository (Lean);
everything here is numerical. Only the enclosure (§1) and the continued fraction (§3) are rigorous
(exact integer arithmetic); everything else is evidence, not proof.

Reproduce: `python3 scripts/transcendence_evidence.py [all|value|pslq|cf|digits] [--cache DIR] [--jobs J] [--N 200000] [--M 1000000] [--deep-dps 2500]`
(Python 3.12, numpy 1.26, mpmath 1.3, sympy 1.14; no scipy/gmpy2/PARI). The output is deterministic apart from timings. The sections below are the script's own output.
Wall times on 24 cores: value 0.3 s, cf 3.4 s, digits 0.7 s, pslq 19.6 min (8100 CPU-s; the
dps-2500 tier accounts for most of it, so `--deep-dps 0` skips it and the base grid takes about 3.5 min).

## Summary

| Test | Parameters | Outcome |
|---|---|---|
| Enclosure | N = 200000 bits, primes to p_200001 = 2750161 | `a/2^N ≤ ρ < (a+1)/2^N` exactly; **60205 certified decimals** (0.30102 N) |
| PSLQ on ρ, base grid | dps 1200; d = 2..12; C = 20, 40, 60 and C_max(d) = 420, 280, 210, 170, 140, 120, 100, 90, 80, 70, 70 | **None in all 44 runs**. mpmath's final norm bound is ≥ 10^C every time, so ρ satisfies no polynomial of degree ≤ d with coefficient norm below that bound |
| PSLQ on ρ, deep tier | dps 2500; d = 2..12; C = C_max(d) = 910, 600, 450, 360, 300, 260, 220, 200, 180, 160, 150 | **None in all 11 runs**: no relation of degree ≤ 12 with norm < 10^150 (degree ≤ 2: < 10^910) |
| Control: root of x^5 − 3x − 1 | same grid as ρ | None for d ≤ 4. For every d ≥ 5 and every C it returns x^(d−5)·(x^5 − 3x − 1), which is exactly 0 at 5000 digits |
| Control: degree-5 root, height ~10^25 | same grid as ρ | None for d ≤ 4 and for C = 20 (below the height). For d ≥ 5 and C ≥ 40 it returns the minimal polynomial or a multiple of it (|P(x)| ≈ 10^-4977 at 5000 digits) |
| Control: π | same grid as ρ | None in all 44 runs; its norm bounds behave just like ρ's |
| Continued fraction | exact CF of both endpoints, common prefix | **58330 certified partial quotients** a_0..a_58329; largest a_37317 = 114099 (P = 0.52 under Gauss–Kuzmin) |
| Gauss–Kuzmin | a_1..a_58329 binned 1, 2, 3, 4, ≥5 | χ² = 6.69 with 4 df, p = 0.15 |
| Khinchin | geometric mean at n = 58329 | 2.69246 vs K₀ = 2.68545 |
| Lévy | (1/n) ln q_n at n = 58328 | 1.18835 vs 1.18657 |
| Irrationality exponent proxy | μ_n = ln q_{n+1}/ln q_n, n ≥ 100 | max 1.0270 at n = 101; the maximum falls to 1.0052 on n ∈ [1000, 10^4) and to 1.00053 on n ≥ 10^4. No sign of μ(ρ) = 1 + limsup μ_n > 2 |
| Digit frequency | M = 10^6, primes to 15485867 | #1 − #0 = 404 = −S(15485867), z = 0.40 (Chebyshev bias, invisible at this scale) |
| Block frequencies (L = 2..12) | non-overlapping χ² and overlapping serial test | **Strongly rejected** (z = +180 to +3235): consecutive digits repeat with probability 0.437, not 0.5. This is the Lemke Oliver–Soundararajan bias between consecutive primes; an order-1 Markov fit explains L = 2 but not L ≥ 3 |
| Longest runs | M = 10^6 | 0s: 16 (primes 12270077..12270317); 1s: 15. A fair coin predicts ≈ 18.9; the Markov fit predicts ≈ 16.2 |
| Sign of S(n) | n ≤ 15485867 | S(n) < 0 for 99.78% of n; first S(n) > 0 at n = 26861; 128 maximal intervals with S > 0, in 3 clusters (26861; 616841–633798; 12306137–12382326); 124 strict sign changes; min −433, max +24 |
| Subword complexity | L = 1..20 | p(L) = 2^L for L ≤ 14; 8 blocks of length 15 are missing (all contain long runs); below the random expectation for L ≥ 15 |

### Interpretation

* **Algebraicity.** PSLQ finds nothing for ρ anywhere in the tested range: degree ≤ 12 with
  coefficient norm up to 10^70 at dps 1200, and up to 10^150 (degree 12) through 10^910 (degree 2)
  at dps 2500. The same code recovers both algebraic controls, including the one of height
  ~10^25, as soon as d and C allow it. On π it behaves exactly as on ρ. This is evidence, not
  proof, that ρ is not algebraic of small degree and height. A *None* only excludes relations
  below mpmath's norm bound (Euclidean norm, so max-norm below bound/√(d+1)), and it does so
  numerically, not rigorously.
* **Continued fraction.** The 58330 certified partial quotients look like those of a "generic"
  real number. They match Gauss–Kuzmin (p = 0.15), Khinchin's constant to 0.3% and Lévy's constant
  to 0.15%. The largest quotient is exactly the size expected among 58k draws. The proxy μ_n is
  decreasing toward 1, so there is no evidence of an irrationality exponent above 2. Why a large
  quotient would be needed: |ρ − p_n/q_n| ≈ 1/(a_{n+1} q_n²), so |ρ − p/q| < q^(−μ) infinitely
  often requires a_{n+1} ≳ q_n^(μ−2) infinitely often, i.e. partial quotients exponentially large
  in n. The largest one seen is 114099 ≈ q_n^(0.0003) at n = 37317.
* **Digits.** This is where the expected picture breaks. The **single-digit** frequency is
  consistent with 1/2, and the Chebyshev bias shows up in S(n): S < 0 for 99.8% of n, with the
  famous first positive value at 26861. But **block** statistics at M = 10^6 are emphatically
  *not* those of i.i.d. fair bits. Consecutive primes avoid repeating their residue class mod 4
  (Lemke Oliver–Soundararajan 2016), so `00` and `11` each occur about 12.5% less often than 1/4 and `01`, `10` about 12.5% more often.
  The defect shrinks slowly with the size of the primes: P(repeat) rises from 0.426 to 0.441
  across the ten windows, consistent with the slow log log x / log x decay their conjecture
  predicts. Runs
  are correspondingly shorter, and 8 of the 32768 blocks of length 15 are absent. Normality of ρ
  in base 2 is still the conjectural expectation, since the Hardy–Littlewood heuristics behind
  Lemke Oliver–Soundararajan make every pattern of consecutive residues asymptotically
  equidistributed. But it is approached so slowly that no finite-range frequency test can
  support it. The data say nothing for or against normality in the limit, and none of this bears
  on transcendence.

## 1. High-precision value

- N = 200000 binary digits d_0..d_199999, primes p_2..p_200001 = 2750161
- binary: 0.101100110100110101101100011001101010110101001111001010101001...
- exact enclosure a/2^N <= rho < (a+1)/2^N stored as hex in rho_enclosure_N200000.json; full decimal in rho_decimal_N200000.txt
- certified decimal digits: 60205  (= 0.30102 N; log10 2 = 0.30103)
- rho to 1000 decimals (truncated, certified):

```
0.7004001379657977336858046527471056545289598309491354984600596541107702902781458257749248212028538325
  6589581827162841555745367191947181183340777916517906450562348235699547586616535218711251514842327933
  4285483649893475277925535833472577529274168086854983213320956766525975935913114602691461101000448640
  6352437134893610699317019997020635865018752446598078257367929386656340457867968295174226373416930444
  5899103251110585032563978755675045297592937140654104558359748698207667547573984974286367486021116818
  0578428384041426384381405939381472085303693551946310774543466103668797370484688817976638003761087867
  7219589488575129709007600226686209431418599202745014486766871876702191233336719437409861326560197625
  4163573300745733395621433122671373916945123473612518495630022089202564136468770605642217220692093589
  8258183787408596514624083672021698117783254179527407070506314357815929554012861609404030880331385291
  4356770426394098223832215413621133757850985453114017190219934857951889704781633815166427856673757269
```

(0.1 s)

## 2. PSLQ

- mpmath.pslq([1, x, ..., x^d], maxcoeff=10^C, maxsteps=10^6) at mp.dps = 1200 (mpmath's default tolerance is 2^-(0.75*prec), about 10^-900)
- rho = a/2^N from the N = 200000 enclosure (error < 2^-200000)
- controls: alg_small = largest real root of x^5 - 3x - 1; alg_large = the real root of the degree-5 polynomial with coefficients (highest degree first) [7895516025895432750735599, -2936036163051900077717247, 8385865052086956486276592, 2160118285191680550403530, -5948574908342044969666157, -8340740219947930859913809] (height ~10^25; both polynomials are irreducible over Q: sympy says True, True); pi
- C = 20, 40, 60 and C_max(d) = 10*floor((0.75*dps - 50)/(10 d)) (rule of thumb d*C + 50 <= effective digits); deep tier: rho only at dps = 2500 with C = C_max(d)
- any relation is re-evaluated at 5000 digits; 'norm bound' is mpmath's final lower bound for the Euclidean norm of any relation (already divided by 100)

### rho

| dps | d | C | result | steps | norm bound | s |
|---|---|---|---|---|---|---|
| 1200 | 2 | 20 | None | 110 | 2.87e20 | 0.1 |
| 1200 | 2 | 40 | None | 216 | 1.61e40 | 0.1 |
| 1200 | 2 | 60 | None | 312 | 1.00e60 | 0.2 |
| 1200 | 2 | 420 | None | 2276 | 1.83e420 | 1.3 |
| 1200 | 3 | 20 | None | 312 | 1.24e20 | 0.3 |
| 1200 | 3 | 40 | None | 563 | 1.13e40 | 0.6 |
| 1200 | 3 | 60 | None | 851 | 1.30e60 | 0.9 |
| 1200 | 3 | 280 | None | 3796 | 1.53e280 | 3.7 |
| 1200 | 4 | 20 | None | 523 | 1.10e20 | 0.8 |
| 1200 | 4 | 40 | None | 1028 | 1.25e40 | 1.6 |
| 1200 | 4 | 60 | None | 1521 | 1.04e60 | 2.3 |
| 1200 | 4 | 210 | None | 5427 | 1.19e210 | 7.9 |
| 1200 | 5 | 20 | None | 909 | 1.03e20 | 1.9 |
| 1200 | 5 | 40 | None | 1755 | 1.10e40 | 3.7 |
| 1200 | 5 | 60 | None | 2600 | 1.02e60 | 5.4 |
| 1200 | 5 | 170 | None | 7297 | 1.03e170 | 14.8 |
| 1200 | 6 | 20 | None | 1429 | 1.14e20 | 3.9 |
| 1200 | 6 | 40 | None | 2709 | 1.05e40 | 7.4 |
| 1200 | 6 | 60 | None | 4013 | 1.07e60 | 10.8 |
| 1200 | 6 | 140 | None | 9365 | 1.12e140 | 24.9 |
| 1200 | 7 | 20 | None | 2001 | 1.00e20 | 7.1 |
| 1200 | 7 | 40 | None | 3931 | 1.13e40 | 14.0 |
| 1200 | 7 | 60 | None | 5743 | 1.01e60 | 20.3 |
| 1200 | 7 | 120 | None | 11217 | 1.05e120 | 39.3 |
| 1200 | 8 | 20 | None | 2737 | 1.01e20 | 12.1 |
| 1200 | 8 | 40 | None | 5192 | 1.04e40 | 23.1 |
| 1200 | 8 | 60 | None | 7692 | 1.01e60 | 33.7 |
| 1200 | 8 | 100 | None | 12702 | 1.06e100 | 54.8 |
| 1200 | 9 | 20 | None | 3464 | 1.04e20 | 18.9 |
| 1200 | 9 | 40 | None | 6636 | 1.05e40 | 36.4 |
| 1200 | 9 | 60 | None | 9804 | 1.01e60 | 53.2 |
| 1200 | 9 | 90 | None | 14585 | 1.20e90 | 79.8 |
| 1200 | 10 | 20 | None | 4452 | 1.08e20 | 29.6 |
| 1200 | 10 | 40 | None | 8543 | 1.02e40 | 55.9 |
| 1200 | 10 | 60 | None | 12641 | 1.02e60 | 83.4 |
| 1200 | 10 | 80 | None | 16669 | 1.01e80 | 112.7 |
| 1200 | 11 | 20 | None | 5314 | 1.01e20 | 42.8 |
| 1200 | 11 | 40 | None | 10277 | 1.05e40 | 81.8 |
| 1200 | 11 | 60 | None | 15217 | 1.08e60 | 124.9 |
| 1200 | 11 | 70 | None | 17720 | 1.11e70 | 144.2 |
| 1200 | 12 | 20 | None | 6481 | 1.09e20 | 60.6 |
| 1200 | 12 | 40 | None | 12444 | 1.03e40 | 120.1 |
| 1200 | 12 | 60 | None | 18283 | 1.03e60 | 173.5 |
| 1200 | 12 | 70 | None | 21168 | 1.04e70 | 200.0 |
| 2500 | 2 | 910 | None | 4916 | 1.84e910 | 9.0 |
| 2500 | 3 | 600 | None | 7976 | 1.30e600 | 24.8 |
| 2500 | 4 | 450 | None | 11436 | 1.08e450 | 51.0 |
| 2500 | 5 | 360 | None | 15561 | 1.14e360 | 98.5 |
| 2500 | 6 | 300 | None | 19736 | 1.02e300 | 164.7 |
| 2500 | 7 | 260 | None | 24304 | 1.02e260 | 262.5 |
| 2500 | 8 | 220 | None | 27768 | 1.04e220 | 352.0 |
| 2500 | 9 | 200 | None | 32183 | 1.01e200 | 486.4 |
| 2500 | 10 | 180 | None | 36852 | 1.07e180 | 650.2 |
| 2500 | 11 | 160 | None | 40091 | 1.03e160 | 840.1 |
| 2500 | 12 | 150 | None | 44609 | 1.01e150 | 1067.3 |

### alg_small

| dps | d | C | result | steps | norm bound | s |
|---|---|---|---|---|---|---|
| 1200 | 2 | 20 | None | 122 | 2.12e20 | 0.1 |
| 1200 | 2 | 40 | None | 239 | 1.57e40 | 0.1 |
| 1200 | 2 | 60 | None | 349 | 1.45e60 | 0.2 |
| 1200 | 2 | 420 | None | 2259 | 1.00e420 | 1.3 |
| 1200 | 3 | 20 | None | 303 | 1.25e20 | 0.3 |
| 1200 | 3 | 40 | None | 556 | 1.04e40 | 0.6 |
| 1200 | 3 | 60 | None | 799 | 1.21e60 | 0.8 |
| 1200 | 3 | 280 | None | 3601 | 1.03e280 | 3.6 |
| 1200 | 4 | 20 | None | 731 | 1.12e20 | 1.1 |
| 1200 | 4 | 40 | None | 1397 | 1.31e40 | 2.1 |
| 1200 | 4 | 60 | None | 2054 | 1.09e60 | 3.0 |
| 1200 | 4 | 210 | None | 6972 | 1.08e210 | 10.1 |
| 1200 | 5 | 20 | relation [-1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.0 |
| 1200 | 5 | 40 | relation [-1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.0 |
| 1200 | 5 | 60 | relation [-1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.0 |
| 1200 | 5 | 170 | relation [-1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.0 |
| 1200 | 6 | 20 | relation [0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 6 | 40 | relation [0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.0 |
| 1200 | 6 | 60 | relation [0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 6 | 140 | relation [0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 7 | 20 | relation [0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 7 | 40 | relation [0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 7 | 60 | relation [0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 7 | 120 | relation [0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 8 | 20 | relation [0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 8 | 40 | relation [0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 8 | 60 | relation [0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 8 | 100 | relation [0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 9 | 20 | relation [0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 9 | 40 | relation [0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 9 | 60 | relation [0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 9 | 90 | relation [0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 10 | 20 | relation [0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 10 | 40 | relation [0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 10 | 60 | relation [0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 10 | 80 | relation [0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 11 | 20 | relation [0, 0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 11 | 40 | relation [0, 0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 11 | 60 | relation [0, 0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 11 | 70 | relation [0, 0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 12 | 20 | relation [0, 0, 0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 12 | 40 | relation [0, 0, 0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 12 | 60 | relation [0, 0, 0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.1 |
| 1200 | 12 | 70 | relation [0, 0, 0, 0, 0, 0, 0, -1, -3, 0, 0, 0, 1] (abs value at 5000 digits: 0.0) | 16 | - | 0.2 |

### alg_large

| dps | d | C | result | steps | norm bound | s |
|---|---|---|---|---|---|---|
| 1200 | 2 | 20 | None | 109 | 1.94e20 | 0.1 |
| 1200 | 2 | 40 | None | 222 | 1.62e40 | 0.1 |
| 1200 | 2 | 60 | None | 332 | 1.48e60 | 0.2 |
| 1200 | 2 | 420 | None | 2238 | 1.05e420 | 1.3 |
| 1200 | 3 | 20 | None | 296 | 1.17e20 | 0.3 |
| 1200 | 3 | 40 | None | 527 | 1.67e40 | 0.5 |
| 1200 | 3 | 60 | None | 774 | 1.20e60 | 0.8 |
| 1200 | 3 | 280 | None | 3664 | 1.79e280 | 3.7 |
| 1200 | 4 | 20 | None | 559 | 1.63e20 | 0.8 |
| 1200 | 4 | 40 | None | 1080 | 1.08e40 | 1.6 |
| 1200 | 4 | 60 | None | 1543 | 1.36e60 | 2.4 |
| 1200 | 4 | 210 | None | 5427 | 1.11e210 | 7.9 |
| 1200 | 5 | 20 | None | 919 | 1.03e20 | 2.0 |
| 1200 | 5 | 40 | relation [-8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599] (abs value at 5000 digits: 9.4226e-4977) | 1040 | - | 2.2 |
| 1200 | 5 | 60 | relation [-8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599] (abs value at 5000 digits: 9.4226e-4977) | 1040 | - | 2.2 |
| 1200 | 5 | 170 | relation [-8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599] (abs value at 5000 digits: 9.4226e-4977) | 1040 | - | 2.3 |
| 1200 | 6 | 20 | None | 1451 | 1.14e20 | 4.0 |
| 1200 | 6 | 40 | relation [-8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599, 0] (abs value at 5000 digits: 9.4226e-4977) | 1633 | - | 4.5 |
| 1200 | 6 | 60 | relation [-8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599, 0] (abs value at 5000 digits: 9.4226e-4977) | 1633 | - | 4.5 |
| 1200 | 6 | 140 | relation [-8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599, 0] (abs value at 5000 digits: 9.4226e-4977) | 1633 | - | 4.5 |
| 1200 | 7 | 20 | None | 2026 | 1.01e20 | 7.2 |
| 1200 | 7 | 40 | relation [0, 8340740219947930859913809, -2392165311605885890247652, -8108693193533725520069687, -6225746766895275935873062, 11321901215138856563993839, -10831552188947332828452846, 7895516025895432750735599] (abs value at 5000 digits: 9.4226e-4977) | 2312 | - | 8.2 |
| 1200 | 7 | 60 | relation [0, 8340740219947930859913809, -2392165311605885890247652, -8108693193533725520069687, -6225746766895275935873062, 11321901215138856563993839, -10831552188947332828452846, 7895516025895432750735599] (abs value at 5000 digits: 9.4226e-4977) | 2312 | - | 8.2 |
| 1200 | 7 | 120 | relation [0, 8340740219947930859913809, -2392165311605885890247652, -8108693193533725520069687, -6225746766895275935873062, 11321901215138856563993839, -10831552188947332828452846, 7895516025895432750735599] (abs value at 5000 digits: 9.4226e-4977) | 2312 | - | 8.2 |
| 1200 | 8 | 20 | None | 2643 | 1.11e20 | 11.6 |
| 1200 | 8 | 40 | relation [0, 0, 0, 8340740219947930859913809, 5948574908342044969666157, -2160118285191680550403530, -8385865052086956486276592, 2936036163051900077717247, -7895516025895432750735599] (abs value at 5000 digits: 9.4226e-4977) | 3031 | - | 13.4 |
| 1200 | 8 | 60 | relation [0, 0, 0, 8340740219947930859913809, 5948574908342044969666157, -2160118285191680550403530, -8385865052086956486276592, 2936036163051900077717247, -7895516025895432750735599] (abs value at 5000 digits: 9.4226e-4977) | 3031 | - | 13.3 |
| 1200 | 8 | 100 | relation [0, 0, 0, 8340740219947930859913809, 5948574908342044969666157, -2160118285191680550403530, -8385865052086956486276592, 2936036163051900077717247, -7895516025895432750735599] (abs value at 5000 digits: 9.4226e-4977) | 3031 | - | 13.3 |
| 1200 | 9 | 20 | None | 3476 | 1.14e20 | 19.1 |
| 1200 | 9 | 40 | relation [0, 0, 0, 0, 8340740219947930859913809, 5948574908342044969666157, -2160118285191680550403530, -8385865052086956486276592, 2936036163051900077717247, -7895516025895432750735599] (abs value at 5000 digits: 0.0) | 3901 | - | 21.1 |
| 1200 | 9 | 60 | relation [0, 0, 0, 0, 8340740219947930859913809, 5948574908342044969666157, -2160118285191680550403530, -8385865052086956486276592, 2936036163051900077717247, -7895516025895432750735599] (abs value at 5000 digits: 0.0) | 3901 | - | 21.3 |
| 1200 | 9 | 90 | relation [0, 0, 0, 0, 8340740219947930859913809, 5948574908342044969666157, -2160118285191680550403530, -8385865052086956486276592, 2936036163051900077717247, -7895516025895432750735599] (abs value at 5000 digits: 0.0) | 3901 | - | 21.5 |
| 1200 | 10 | 20 | None | 4311 | 1.01e20 | 28.4 |
| 1200 | 10 | 40 | relation [0, 0, -8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599, 0, 0, 0] (abs value at 5000 digits: 9.4226e-4977) | 4895 | - | 32.1 |
| 1200 | 10 | 60 | relation [0, 0, -8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599, 0, 0, 0] (abs value at 5000 digits: 9.4226e-4977) | 4895 | - | 32.1 |
| 1200 | 10 | 80 | relation [0, 0, -8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599, 0, 0, 0] (abs value at 5000 digits: 9.4226e-4977) | 4895 | - | 33.1 |
| 1200 | 11 | 20 | None | 5480 | 1.00e20 | 44.1 |
| 1200 | 11 | 40 | relation [0, 0, 0, 0, 8340740219947930859913809, 5948574908342044969666157, -2160118285191680550403530, -8385865052086956486276592, 2936036163051900077717247, -7895516025895432750735599, 0, 0] (abs value at 5000 digits: 0.0) | 6142 | - | 49.1 |
| 1200 | 11 | 60 | relation [0, 0, 0, 0, 8340740219947930859913809, 5948574908342044969666157, -2160118285191680550403530, -8385865052086956486276592, 2936036163051900077717247, -7895516025895432750735599, 0, 0] (abs value at 5000 digits: 0.0) | 6142 | - | 52.1 |
| 1200 | 11 | 70 | relation [0, 0, 0, 0, 8340740219947930859913809, 5948574908342044969666157, -2160118285191680550403530, -8385865052086956486276592, 2936036163051900077717247, -7895516025895432750735599, 0, 0] (abs value at 5000 digits: 0.0) | 6142 | - | 51.7 |
| 1200 | 12 | 20 | None | 6441 | 1.06e20 | 60.6 |
| 1200 | 12 | 40 | relation [0, 0, -8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599, 0, 0, 0, 0, 0] (abs value at 5000 digits: 9.4226e-4977) | 7223 | - | 71.4 |
| 1200 | 12 | 60 | relation [0, 0, -8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599, 0, 0, 0, 0, 0] (abs value at 5000 digits: 9.4226e-4977) | 7223 | - | 71.1 |
| 1200 | 12 | 70 | relation [0, 0, -8340740219947930859913809, -5948574908342044969666157, 2160118285191680550403530, 8385865052086956486276592, -2936036163051900077717247, 7895516025895432750735599, 0, 0, 0, 0, 0] (abs value at 5000 digits: 9.4226e-4977) | 7223 | - | 71.2 |

### pi

| dps | d | C | result | steps | norm bound | s |
|---|---|---|---|---|---|---|
| 1200 | 2 | 20 | None | 123 | 1.15e20 | 0.1 |
| 1200 | 2 | 40 | None | 231 | 1.34e40 | 0.1 |
| 1200 | 2 | 60 | None | 334 | 3.23e60 | 0.2 |
| 1200 | 2 | 420 | None | 2262 | 1.11e420 | 1.4 |
| 1200 | 3 | 20 | None | 286 | 1.00e20 | 0.3 |
| 1200 | 3 | 40 | None | 556 | 1.25e40 | 0.6 |
| 1200 | 3 | 60 | None | 807 | 1.32e60 | 0.9 |
| 1200 | 3 | 280 | None | 3653 | 1.06e280 | 3.7 |
| 1200 | 4 | 20 | None | 525 | 1.18e20 | 0.8 |
| 1200 | 4 | 40 | None | 1033 | 1.05e40 | 1.5 |
| 1200 | 4 | 60 | None | 1549 | 1.04e60 | 2.3 |
| 1200 | 4 | 210 | None | 5306 | 1.14e210 | 7.8 |
| 1200 | 5 | 20 | None | 952 | 1.17e20 | 1.9 |
| 1200 | 5 | 40 | None | 1769 | 1.21e40 | 3.7 |
| 1200 | 5 | 60 | None | 2618 | 1.10e60 | 5.4 |
| 1200 | 5 | 170 | None | 7251 | 1.03e170 | 14.7 |
| 1200 | 6 | 20 | None | 1443 | 1.10e20 | 3.9 |
| 1200 | 6 | 40 | None | 2724 | 1.00e40 | 7.3 |
| 1200 | 6 | 60 | None | 4018 | 1.17e60 | 10.9 |
| 1200 | 6 | 140 | None | 9168 | 1.11e140 | 24.7 |
| 1200 | 7 | 20 | None | 2061 | 1.15e20 | 7.2 |
| 1200 | 7 | 40 | None | 3941 | 1.18e40 | 14.0 |
| 1200 | 7 | 60 | None | 5796 | 1.17e60 | 20.6 |
| 1200 | 7 | 120 | None | 11304 | 1.01e120 | 39.3 |
| 1200 | 8 | 20 | None | 2679 | 1.01e20 | 11.7 |
| 1200 | 8 | 40 | None | 5094 | 1.08e40 | 22.3 |
| 1200 | 8 | 60 | None | 7487 | 1.10e60 | 32.9 |
| 1200 | 8 | 100 | None | 12504 | 1.24e100 | 53.8 |
| 1200 | 9 | 20 | None | 3562 | 1.04e20 | 19.4 |
| 1200 | 9 | 40 | None | 6757 | 1.08e40 | 37.3 |
| 1200 | 9 | 60 | None | 9927 | 1.14e60 | 54.3 |
| 1200 | 9 | 90 | None | 14744 | 1.03e90 | 80.1 |
| 1200 | 10 | 20 | None | 4402 | 1.10e20 | 29.3 |
| 1200 | 10 | 40 | None | 8366 | 1.02e40 | 55.0 |
| 1200 | 10 | 60 | None | 12372 | 1.10e60 | 80.6 |
| 1200 | 10 | 80 | None | 16376 | 1.02e80 | 110.5 |
| 1200 | 11 | 20 | None | 5467 | 1.18e20 | 43.9 |
| 1200 | 11 | 40 | None | 10497 | 1.13e40 | 83.6 |
| 1200 | 11 | 60 | None | 15454 | 1.07e60 | 125.9 |
| 1200 | 11 | 70 | None | 18003 | 1.20e70 | 146.1 |
| 1200 | 12 | 20 | None | 6477 | 1.02e20 | 60.7 |
| 1200 | 12 | 40 | None | 12397 | 1.22e40 | 118.2 |
| 1200 | 12 | 60 | None | 18208 | 1.26e60 | 172.5 |
| 1200 | 12 | 70 | None | 21206 | 1.08e70 | 200.1 |

(1178.5 s wall, 24 processes)

## 3. Continued fraction (exact)

- endpoints a/2^200000 and (a+1)/2^200000; common CF prefix = 58330 partial quotients a_0..a_58329 (certified); ln q_58329 = 69314.3 (vs N ln2 / 2 = 69314.7)
- first 60: [0; 1, 2, 2, 1, 24, 3, 2, 3, 5, 1, 3, 3, 2, 4, 1, 7, 5, 2, 3, 6, 1, 3, 1, 31, 53, 1, 1, 430, 19, 1, 3, 3, 8, 20, 2, 1, 5, 1, 36, 1, 16, 1, 5, 1, 1, 1, 1, 1, 6, 1, 23, 2, 16, 3, 2, 1, 65, 1, 3, ...]
- largest partial quotient: a_37317 = 114099; under Gauss-Kuzmin P(max(a_1..a_58329) >= 114099) = 0.52
- five largest: a_37317 = 114099, a_1790 = 66290, a_7754 = 38839, a_1737 = 20547, a_52438 = 19990

| a_n | count (n = 1..58329) | observed | Gauss-Kuzmin |
|---|---|---|---|
| 1 | 24168 | 0.41434 | 0.41504 |
| 2 | 9790 | 0.16784 | 0.16993 |
| 3 | 5419 | 0.09290 | 0.09311 |
| 4 | 3566 | 0.06114 | 0.05889 |
| >=5 | 15386 | 0.26378 | 0.26303 |

chi-square vs Gauss-Kuzmin: 6.69 (4 df), p = 0.153

| n | (a_1...a_n)^(1/n) | Khinchin | (1/n) ln q_n | Levy |
|---|---|---|---|---|
| 100 | 2.95686 | 2.68545 | 1.26352 (n=100) | 1.18657 |
| 1000 | 2.62605 | 2.68545 | 1.16817 (n=1000) | 1.18657 |
| 10000 | 2.73317 | 2.68545 | 1.20055 (n=10000) | 1.18657 |
| 58329 | 2.69246 | 2.68545 | 1.18835 (n=58328) | 1.18657 |

mu_n = ln q_{n+1} / ln q_n, ten largest over n >= 100 (since |rho - p_n/q_n| ~ 1/(q_n q_{n+1}) = q_n^-(1 + mu_n), the irrationality exponent is 1 + limsup mu_n; a generic number has mu_n -> 1):

| n | mu_n | a_{n+1} |
|---|---|---|
| 101 | 1.02700 | 30 |
| 162 | 1.01998 | 48 |
| 126 | 1.01816 | 16 |
| 116 | 1.01759 | 12 |
| 146 | 1.01524 | 14 |
| 103 | 1.01491 | 6 |
| 106 | 1.01412 | 6 |
| 163 | 1.01400 | 16 |
| 107 | 1.01348 | 6 |
| 342 | 1.01289 | 139 |

max mu_n by range: n in 100..999: mu_101 = 1.02700; n in 1000..9999: mu_1789 = 1.00524; n in 10000..58328: mu_14619 = 1.00053

(4.0 s)

## 4. Digit statistics

- M = 1000000 digits d_0..d_999999 (primes p_2..p_1000001 = 15485867)

### Frequencies

#1 = 500202, #0 = 499798, freq(1) = 0.500202; #1 - #0 = 404 = -S(15485867) with S(x) = sum_(p<=x) chi_4(p) = -404  [check: True]; (#1-#0)/sqrt(M) = 0.404

### Block frequencies

Non-overlapping blocks (floor(M/L) blocks, 2^L - 1 df) and Good's serial test on overlapping circular blocks (grad psi^2_L = psi^2_L - psi^2_{L-1}, 2^{L-1} df). z = (chi2 - df)/sqrt(2 df).

| L | blocks | chi2 (non-ovl) | df | z | p | grad psi^2 (ovl) | df | z | p | min/max ovl count / expected |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 1000000 | 0.2 | 1 | -0.59 | 0.686 | 0.2 | 1 | -0.59 | 0.686 | 1.000 / 1.000 |
| 2 | 500000 | 7927.6 | 3 | +3235.20 | 0.000 | 15663.2 | 2 | +7830.59 | 0.000 | 0.874 / 1.125 |
| 3 | 333333 | 10499.2 | 7 | +2804.15 | 0.000 | 16154.6 | 4 | +5710.10 | 0.000 | 0.726 / 1.228 |
| 4 | 250000 | 12270.5 | 15 | +2237.54 | 0.000 | 16739.0 | 8 | +4182.76 | 0.000 | 0.590 / 1.365 |
| 5 | 200000 | 13330.1 | 31 | +1688.98 | 0.000 | 17119.9 | 16 | +3023.57 | 0.000 | 0.462 / 1.502 |
| 6 | 166666 | 14012.7 | 63 | +1242.74 | 0.000 | 17472.8 | 32 | +2180.10 | 0.000 | 0.354 / 1.662 |
| 7 | 142857 | 14503.2 | 127 | +902.04 | 0.000 | 17857.6 | 64 | +1572.75 | 0.000 | 0.271 / 1.827 |
| 8 | 125000 | 15233.2 | 255 | +663.24 | 0.000 | 18306.6 | 128 | +1136.16 | 0.000 | 0.195 / 2.026 |
| 9 | 111111 | 15722.4 | 511 | +475.82 | 0.000 | 18716.2 | 256 | +815.83 | 0.000 | 0.141 / 2.231 |
| 10 | 100000 | 16713.8 | 1023 | +346.89 | 0.000 | 19383.8 | 512 | +589.74 | 0.000 | 0.098 / 2.524 |
| 11 | 90909 | 17953.5 | 2047 | +248.60 | 0.000 | 20186.8 | 1024 | +423.44 | 0.000 | 0.074 / 2.857 |
| 12 | 83333 | 20438.7 | 4095 | +180.60 | 0.000 | 21581.3 | 2048 | +305.21 | 0.000 | 0.049 / 3.273 |

### Consecutive-prime bias (Lemke Oliver-Soundararajan)

| digits k in | primes up to | P(d_{k+1} = d_k) | (P - 1/2) sqrt(pairs) | LO-S leading term at window end |
|---|---|---|---|---|
| [0, 99999) | 1299721 | 0.42638 | -23.3 | 0.45304 |
| [99999, 199999) | 2750161 | 0.43514 | -20.5 | 0.45454 |
| [199999, 299999) | 4256249 | 0.43520 | -20.5 | 0.45536 |
| [299999, 399999) | 5800139 | 0.43721 | -19.9 | 0.45593 |
| [399999, 499999) | 7368791 | 0.43690 | -20.0 | 0.45635 |
| [499999, 599999) | 8960467 | 0.43808 | -19.6 | 0.45669 |
| [599999, 699999) | 10570849 | 0.44029 | -18.9 | 0.45698 |
| [699999, 799999) | 12195263 | 0.44133 | -18.6 | 0.45722 |
| [799999, 899999) | 13834127 | 0.44242 | -18.2 | 0.45743 |
| [899999, 999999) | 15485867 | 0.44128 | -18.6 | 0.45762 |

Order-1 Markov fit: P(0->0) = 0.43720, P(1->1) = 0.43765. Non-overlapping L-blocks against the Markov expectation (df = 2^L - 3):

| L | chi2 vs Markov-1 | df | z | p |
|---|---|---|---|---|
| 2 | 1.6 | 1 | +0.45 | 0.201 |
| 3 | 478.7 | 5 | +149.79 | 3.19e-101 |
| 4 | 815.5 | 13 | +157.39 | 6.47e-166 |
| 5 | 1101.4 | 29 | +140.82 | 3.02e-213 |
| 6 | 1295.2 | 61 | +111.74 | 1.03e-230 |
| 7 | 1493.7 | 125 | +86.56 | 6.22e-233 |
| 8 | 1658.0 | 253 | +62.46 | 9.97e-205 |
| 9 | 2026.0 | 509 | +47.54 | 1.57e-179 |
| 10 | 2602.5 | 1021 | +35.00 | 1.22e-138 |
| 11 | 3777.4 | 2045 | +27.09 | 2.99e-106 |
| 12 | 5857.7 | 4093 | +19.50 | 5.26e-67 |

### Longest runs

- longest run of 0s: length 16 at digits d_804582..d_804597 (primes 12270077..12270317, all = 1 mod 4)
- longest run of 1s: length 15 at digits d_613489..d_613503 (primes 9177431..9177611, all = 3 mod 4)
- heuristic: log2(M) = 19.93; for a fair coin the longest run of a given symbol is about log2(M/2) = 18.93 (sd ~ 1.87)
- under the order-1 Markov fit (stay probability 0.4372) the longest run of 0s is about log(#runs)/log(1/stay) + 1 = 16.2
- under the order-1 Markov fit (stay probability 0.4377) the longest run of 1s is about log(#runs)/log(1/stay) + 1 = 16.2

### Sign of S(n) = sum_{p<=n} chi_4(p)

- range 3 <= n <= 15485867: fraction of n with S(n) < 0: 0.997773, = 0: 0.000250, > 0: 0.001978
- logarithmic density of S(n) < 0 on [3, 15485867] (weight dn/n): 0.966885 (Rubinstein-Sarnak, under GRH + LI, for x -> oo: delta(4;3,1) = 0.9959)
- strict sign changes of S (zeros skipped): 124; min S = -433, max S = 24
- maximal intervals of n with S(n) > 0 (pi(n;4,1) > pi(n;4,3)): 128; first starts at n = 26861
- clusters (intervals closer than 10^5 merged): [26861, 26862] (1 intervals, max S = 1); [616841, 633798] (52 intervals, max S = 8); [12306137, 12382326] (75 intervals, max S = 24)

### Subword complexity

| L | p(L) | 2^L | expected for random (M-L+1 windows) |
|---|---|---|---|
| 1 | 2 | 2 | 2.0 |
| 2 | 4 | 4 | 4.0 |
| 3 | 8 | 8 | 8.0 |
| 4 | 16 | 16 | 16.0 |
| 5 | 32 | 32 | 32.0 |
| 6 | 64 | 64 | 64.0 |
| 7 | 128 | 128 | 128.0 |
| 8 | 256 | 256 | 256.0 |
| 9 | 512 | 512 | 512.0 |
| 10 | 1024 | 1024 | 1024.0 |
| 11 | 2048 | 2048 | 2048.0 |
| 12 | 4096 | 4096 | 4096.0 |
| 13 | 8192 | 8192 | 8192.0 |
| 14 | 16384 | 16384 | 16384.0 |
| 15 | 32760 | 32768 | 32768.0 |
| 16 | 65307 | 65536 | 65536.0 |
| 17 | 128352 | 131072 | 131008.3 |
| 18 | 240022 | 262144 | 256364.9 |
| 19 | 403489 | 524288 | 446442.6 |
| 20 | 585855 | 1048576 | 644528.8 |

missing blocks of length 15: 000000000000011, 000000000001001, 001100000000000, 100000001000000, 111111101111000, 111111111101110, 111111111110111, 111111111111011

(0.9 s)

