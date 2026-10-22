# Rational approximations to Rokicki's constant: periodic stretches of prime residues

**Status.** Direction 3 of `PROGRAM.md`. The dictionary between rational approximations and
periodic digit stretches (§1) is proved here, one direction of it in Lean. The dyadic theorem
(§2) is formalized *conditionally on Breusch's theorem* in `RokickiConstant/General/Diophantine.lean`
(no `sorry`), with an explicit constant obtained from Mathlib's Chebyshev bounds. The statistics
in §3 are reproduced by `python3 scripts/periodic_patterns.py` (18 s, about 2 GB).

Notation. `p_1 = 2, p_2 = 3, …` are the primes, `d_k = [p_{k+2} ≡ 3 (mod 4)]`, and

    ρ = Σ_{k≥0} d_k 2^{-(k+1)} = 0.1011001101…₂,    T_n = Σ_{j≥0} d_{n+j} 2^{-(j+1)} = {2^n ρ}.

`T_n` is the tail at `n` (`binaryTail` in `RokickiConstant/BinaryExpansion.lean`). Since `ρ` is
irrational, every `T_n` lies strictly between `0` and `1` and is not a dyadic rational, so binary
expansions are unique throughout. `‖y‖` is the distance from `y` to the nearest integer.

A **`P`-periodic stretch** of length `L` starting at `n` is a block `d_n, …, d_{n+L-1}` with
`d_{i+P} = d_i` for `n ≤ i < n + L - P`. Its **excess** is `E = L - P`: the number of digits
forced by the first `P`. Every block of length `≤ P` is `P`-periodic, so only the excess carries
information.

## 1. The dictionary: rational approximations are periodic stretches

**Proposition 1.1** (stretch ⇒ approximation; formalized as
`exists_abs_tsum_sub_div_le_of_periodic`, for any binary digit sequence). If
`d_{i+P} = d_i` for `n ≤ i < n + E` and `P ≥ 1`, then with `Q = 2^n (2^P - 1)` there is an
integer `a` with

    | ρ - a/Q | ≤ 1 / (2^{n+E} (2^P - 1)) = 2^{-E} / Q.

Since `Q < 2^{n+P}`, this is `|ρ - a/Q| ≤ Q^{-(1 + E/(n+P))}`.

*Proof.* `2^k ρ = N_k + T_k` with `N_k` an integer (`two_pow_mul_tsum_sub_binaryTail`), so
`Q ρ = 2^{n+P} ρ - 2^n ρ = (N_{n+P} - N_n) + (T_{n+P} - T_n)`. The tails `T_n` and `T_{n+P}`
agree in their first `E` digits, so `|T_n - T_{n+P}| ≤ 2^{-E}`: by induction on `E`, using
`T_{k+1} = 2 T_k - d_k`, the difference halves with each agreeing digit and starts in `[-1, 1]`
(`abs_binaryTail_sub_binaryTail_add_le`). ∎

**Proposition 1.2** (approximation ⇒ stretch). Let `q = 2^s q'` with `q'` odd, and let
`P = ord_{q'}(2)` (`P = 1` if `q' = 1`). If `|ρ - a/q| < δ/q`, set
`K = ⌊log₂(q' / (δ (2^P - 1)))⌋`. Then `d_{i+P} = d_i` for `s ≤ i < s + K - P - 1`: there is a
`P`-periodic stretch starting at `s` with excess at least `K - P - 1`.

*Proof.* Since `q' | 2^P - 1`, put `Q = 2^s (2^P - 1) = q (2^P - 1)/q'`. Then
`‖Q ρ‖ ≤ ((2^P - 1)/q') ‖q ρ‖ < 2^{-K}`, and `Q ρ ≡ T_{s+P} - T_s (mod 1)`. So
`y = T_s` and `z = T_{s+P}` (with digits `y_j = d_{s+j}`, `z_j = d_{s+P+j}`) are within `2^{-K}`
on the circle `ℝ/ℤ`.

*Case `|y - z| < 2^{-K}`.* Let `j` be the first index with `y_j ≠ z_j`; if `j ≥ K` we are done.
Otherwise say `y_j = 0`, `z_j = 1`, and let `c` be the dyadic point `0.y_0…y_{j-1}1`. Then
`z - y = (z - c) + (c - y) = Σ_{i>j} z_i 2^{-i-1} + Σ_{i>j} (1 - y_i) 2^{-i-1} < 2^{-K}`, so
`z_i = 0` and `y_i = 1` for `j < i < K`. If `K - j - 1 > P`, the index `i = j + 1 + P < K` gives
`d_{s+j+1+P} = y_{j+1+P} = 1` and `d_{s+P+j+1} = z_{j+1} = 0`, which is absurd. Hence
`j ≥ K - P - 1`, and `y_i = z_i` for `i < K - P - 1`. The case `y_j = 1`, `z_j = 0` is symmetric.

*Case `|y - z ± 1| < 2^{-K}`* (wrap-around). Then one of `y, z` is `< 2^{-K}` and the other
`> 1 - 2^{-K}`, so one block `d_{s}, …, d_{s+K-1}` is all `0` and the block shifted by `P` is all
`1` (or the reverse). They overlap if `K > P`, which is absurd; so `K ≤ P` and the claim is
vacuous. ∎

**Consequences.**

1. *Exponent bookkeeping.* An approximation `|ρ - a/q| < q^{-μ}` gives `δ = q^{1-μ}` and a
   `P`-periodic stretch starting at `s = v₂(q)` with excess
   `E ≥ (μ - 1) log₂ q - log₂((2^P - 1)/q') - P - 2`. For the "Mersenne" denominators
   `q = 2^s (2^P - 1)` this is `E ≥ (μ - 1) log₂ q - P - 2`; together with Proposition 1.1, for
   each fixed `P` the irrationality exponent of `ρ` along the family `{2^n (2^P - 1) : n ≥ 0}` is
   exactly `1 + limsup_n E_P(n)/n`, where `E_P(n)` is the excess of the maximal `P`-periodic
   stretch starting at `n`. The quantity to measure is therefore `E/(n + P)`, **not** `L/n`:
   `L/(n+1) ≥ P/(n+1)` holds for every block, periodic or not.
2. *Visibility.* Proposition 1.2 says something only when `K > P + 1`, i.e. roughly when
   `P < (μ - 1) log₂ q + log₂ q' - P`, so when the period `ord_{q'}(2)` is `O(log q)`. For a
   typical odd `q'`, `ord_{q'}(2)` is a power of `q'`, and the "periodic stretch" of
   `a/q` is longer than the whole block of digits that the approximation controls. Such
   approximations are invisible in the stretch picture (§4).
3. *Dyadic case* `q = 2^m` (`q' = 1`, `P = 1`): a `1`-periodic stretch is a run of equal
   digits, i.e. a string of consecutive primes `p_{m+2}, p_{m+3}, …` in one class modulo `4`.
   Here the dictionary is exact and elementary (Theorem 2.1).

## 2. Dyadic denominators: runs of congruent primes

**Theorem 2.1** (separation; formalized as `one_div_two_pow_le_abs_tsum_sub_div_two_pow`, for any
binary digit sequence `d` with value `x`). If `d_{m+k} ≠ d_m`, then for every integer `a`

    | x - a / 2^m | ≥ 2^{-(m + k + 1)}.

*Proof.* One of `d_m`, `d_{m+k}` is `1` and the other `0`, so the tail `T_m` contains a `1` and
a `0` among its first `k + 1` digits; hence `T_m ≥ 2^{-(k+1)}` and
`1 - T_m = Σ_j (1 - d_{m+j}) 2^{-j-1} ≥ 2^{-(k+1)}` (`binaryTail_mem_Icc_of_ne`). With
`2^m x = N + T_m`, `N ∈ ℤ`, the distance from `2^m x` to the integer `a` is
`|N - a + T_m| ≥ min(T_m, 1 - T_m) ≥ 2^{-(k+1)}`. Divide by `2^m`. ∎

Equivalently: `|ρ - a/2^m| < 2^{-(m+L)}` forces `d_m = d_{m+1} = ⋯ = d_{m+L-1}`, a run of `L`
congruent consecutive primes starting at `p_{m+2}`. Conversely (Proposition 1.1 with `P = 1`), a
run of length `L` at `m` gives `|ρ - N/2^m| ≤ 2^{-(m+L-1)}`. So the dyadic approximations of
`ρ` are governed exactly by the run lengths `R(m)` (length of the run of equal digits starting
at index `m`):

    2^{-(m + R(m) + 1)} ≤ min_a |ρ - a/2^m| ≤ 2^{-(m + R(m) - 1)}.

**Breusch's theorem** (R. Breusch, Math. Z. 34 (1932), 505–526). For every real `x ≥ 7` each of
the classes `1` and `3 (mod 4)` contains a prime in `(x, 2x]`. In Lean this is the hypothesis
`RokickiConstant.BreuschFour` (stated for natural `x`, which is equivalent). `scripts/
periodic_patterns.py` checks it exactly for all `7 ≤ x < 3.78·10^8`; the extreme ratios of
consecutive primes in one class are `13/7 = 1.857` (class 1) and `19/11 = 1.727` (class 3).

**Theorem 2.2** (formalized, conditional on Breusch). Assume `BreuschFour`. Then:

1. (`exists_rokickiDigit_ne_of_breuschFour`) for every `n` there is
   `1 ≤ k ≤ π(2 p_{n+2}) - π(p_{n+2})` with `d_{n+k} ≠ d_n`, i.e.
   `R(n) ≤ π(2p) - π(p)` for `p = p_{n+2}`;
2. (`exists_rokickiDigit_ne_le_of_breuschFour`) `R(n) ≤ 27 (n + 2)`;
3. (`one_div_two_pow_le_abs_rokickiConstant_sub_of_breuschFour'` and unprimed) for all `m ≥ 0`
   and `a ∈ ℤ`,

       |ρ - a/2^m| ≥ 2^{-(m + π(2p_{m+2}) - π(p_{m+2}) + 1)} ≥ 2^{-(28m + 55)};

4. (`one_div_two_pow_pow_le_abs_rokickiConstant_sub_of_breuschFour`) for `m ≥ 1`,
   `|ρ - a/2^m| ≥ (2^m)^{-83}`. So `ρ` has no dyadic approximations of Liouville type, and its
   dyadic irrationality exponent is at most `28`.

*Proof.* (1) Let `p = p_{n+2} ≥ 7` (`n ≥ 2`; for `n = 0, 1` use the primes `5` and `7`). Breusch
gives a prime `p'` of the other class in `(p, 2p]`; it is `p_{n+2+k}` with
`k = π(p') - π(p) ≤ π(2p) - π(p)`, and `d_{n+k} ≠ d_n`. (2) `π(p_{n+2}) = n + 2`
(`primeCounting_oddPrime`), and `π(2x) ≤ 28 π(x)` for `x ≥ 6` (`Nat.primeCounting_two_mul_le`,
below). (3) Theorem 2.1 with `k ≤ 27(m + 2)`. (4) `28m + 55 ≤ 83m` for `m ≥ 1`. ∎

*The Chebyshev input.* Mathlib has `Chebyshev.pi_le_log4_mul_div`:
`π(y) ≤ log 4 · y / log √y + √y` for `y > 1`, and `Chebyshev.pi_ge`:
`π(n) ≥ (n log 2 - log(n+1)) / log n`. With `√y log y ≤ 2y` (from `log t ≤ t - 1`) the first
gives `π(2x) log x ≤ (8 log 2 + 4) x`; with `(x + 1)² ≤ 2^x` for `x ≥ 6` the second gives
`x log 2 ≤ 2 π(x) log x`; and `log 2 > 2/3` (`Real.log_two_gt_d9`) yields
`π(2x) ≤ (16 + 8/log 2) π(x) ≤ 28 π(x)`. The constant is far from optimal, see below.

**Theorem 2.3** (sharper constants, not formalized; conditional on Breusch only through the
first inequality). With the Montgomery–Vaughan form of Brun–Titchmarsh,
`π(x + y) - π(x) ≤ 2y / log y` (`x ≥ 1`, `y ≥ 2`), and Rosser–Schoenfeld's `π(x) > x / log x`
(`x ≥ 17`): `R(m) ≤ π(2p) - π(p) ≤ 2p / log p < 2 π(p) = 2(m + 2)` for `m ≥ 5`, hence

    |ρ - a/2^m| ≥ 2^{-(3m + 5)}    (m ≥ 5, a ∈ ℤ, assuming Breusch).

With the prime number theorem, `π(2p) - π(p) ~ π(p)`, so `R(m) ≤ (1 + o(1)) m` and the dyadic
exponent is `≤ 2`.

**Theorem 2.4** (unconditional, not formalized; the true order of the bound). Let
`μ₂(x) = sup{μ : |x - a/2^m| < 2^{-μ m} for infinitely many m and some a}`; always `μ₂ ≥ 1`.

1. The prime number theorem in progressions modulo `4` gives, for every `δ > 0` and
   `x ≥ x₀(δ)`, primes of both classes in `(x, (1 + δ)x]`. Hence `R(m) ≤ (δ + o(1)) m` and
   **`μ₂(ρ) = 1`**. (Breusch's theorem is only needed for an explicit, formalizable version.)
2. Primes in short intervals in progressions with fixed modulus (Huxley's zero-density estimate,
   intervals `[x, x + x^θ]` with `θ > 7/12`; see `transcendence.md` §4) give, for every `ε > 0`
   and `m ≥ m₀(ε)`,

       |ρ - a/2^m| ≥ 2^{-(m + m^{7/12 + ε})}.

   Any exponent `θ` for which `[x, x + x^θ]` contains primes of both classes for large `x` gives
   `m^{θ+ε}` in place of `m^{7/12+ε}`; under GRH for `L(s, χ₄)`, `θ = 1/2 + ε`.
3. Heuristically (Cramér / Hardy–Littlewood) `R(m) = O(log m)`, i.e.
   `|ρ - a/2^m| ≥ 2^{-m} m^{-O(1)}`; §3 is consistent with this (the longest run among the first
   `10^7` digits has `17` digits; `log(10^7)/log(1/0.427) ≈ 19`).

## 3. Numerics (`scripts/periodic_patterns.py`, `M = 10^7` digits)

The digits `d_0, …, d_{9999999}` come from the primes `3, …, 179424691` by an exact sieve
(to `3.78·10^8`, checked against `π(10^8) = 5761455`). Every number in the tables below is an
exact count or position; the columns labelled *model* are heuristic.

*Random model.* For i.i.d. fair digits and fixed `P`, the indicators `e_i = [d_{i+P} = d_i]` are
i.i.d. fair bits (for fixed `d_0, …, d_{P-1}` the map `d ↦ e` is a bijection on windows), and
maximal `P`-periodic stretches of positive excess are maximal runs of `1`s in `e`. So the number
of stretches with excess `≥ t` is about `M 2^{-(t+1)}`, and the longest has excess
`≈ log₂ M - 0.67 = 22.6` (standard deviation `≈ 1.87`): `L_max(P) ≈ P + 22.6`. The
*f-model* replaces `1/2` by the observed match frequency `f = mean(e)`.

**Runs of equal digits (`P = 1`).** Longest runs: `17` digits from `n = 6067261` (the seventeen
consecutive primes `105639091, …, 105639463`, all `≡ 3 (mod 4)`) and from `n = 8489730`; longest
run of `0`s: `16` digits from `n = 804582` (primes `12270077 … 12270317`). At the start of the
longest run, Breusch allows `π(2p) - π(p) = 5600928`: the bound of Theorem 2.2(1) is slack by a
factor `3·10^5`. Over all runs starting at `n ≥ 100`, `max R/(π(2p) - π(p)) = 0.041` and
`max R/(n + 1) = 0.033` (a run of `5` at `n = 151`).

**Longest `P`-periodic stretch, `P = 1, …, 64`.** `p` is the f-model probability that the
longest excess is at least the observed one; the last column is the Diophantine statistic of §1,
`max E/(n + P)` over maximal stretches starting at `n ≥ 100` (with its position).

| P | f | L_max | E_max | f-model | p | start n | p_{n+2} | max E/(n+P), n ≥ 100 (n) |
|---|---|---|---|---|---|---|---|---|
| 1 | 0.4449 | 17 | 16 | 19.4 | 1.00 | 6067261 | 105639091 | 0.0263 (151) |
| 2 | 0.4902 | 27 | 25 | 22.0 | 0.09 | 2643156 | 43679609 | 0.0882 (100) |
| 3 | 0.4949 | 25 | 22 | 22.3 | 0.62 | 1974402 | 32010331 | 0.0439 (111) |
| 4 | 0.4959 | 27 | 23 | 22.3 | 0.39 | 2643156 | 43679609 | 0.0673 (100) |
| 5 | 0.4972 | 26 | 21 | 22.4 | 0.88 | 6739830 | 118103717 | 0.0249 (196) |
| 6 | 0.4978 | 28 | 22 | 22.4 | 0.66 | 8768301 | 156106177 | 0.0472 (100) |
| 7 | 0.4978 | 30 | 23 | 22.4 | 0.42 | 759687 | 11538853 | 0.0500 (233) |
| 8 | 0.4979 | 31 | 23 | 22.5 | 0.42 | 5446589 | 94209827 | 0.0350 (135) |
| 9 | 0.4984 | 31 | 22 | 22.5 | 0.67 | 604151 | 9027547 | 0.0431 (107) |
| 10 | 0.4990 | 36 | 26 | 22.5 | 0.07 | 1547124 | 24679243 | 0.0488 (154) |
| 11 | 0.4987 | 33 | 22 | 22.5 | 0.68 | 4301767 | 73321327 | 0.0432 (174) |
| 12 | 0.4987 | 36 | 24 | 22.5 | 0.24 | 4005891 | 67973627 | 0.0306 (184) |
| 13 | 0.4984 | 35 | 22 | 22.5 | 0.67 | 7033557 | 123575047 | 0.0345 (103) |
| 14 | 0.4988 | 38 | 24 | 22.5 | 0.25 | 1730881 | 27819161 | 0.0650 (109) |
| 15 | 0.4990 | 36 | 21 | 22.5 | 0.90 | 1256630 | 19765943 | 0.0446 (187) |
| 16 | 0.4994 | 37 | 21 | 22.5 | 0.90 | 4205411 | 71578063 | 0.0379 (248) |
| 17 | 0.4990 | 39 | 22 | 22.5 | 0.68 | 2210162 | 36102461 | 0.0514 (197) |
| 18 | 0.4990 | 40 | 22 | 22.5 | 0.68 | 1782957 | 28712443 | 0.0341 (158) |
| 19 | 0.4990 | 41 | 22 | 22.5 | 0.68 | 6526312 | 114138847 | 0.0286 (121) |
| 20 | 0.4995 | 41 | 21 | 22.6 | 0.90 | 9310760 | 166361161 | 0.0510 (137) |
| 21 | 0.4992 | 47 | 26 | 22.5 | 0.07 | 4971184 | 85501391 | 0.0417 (123) |
| 22 | 0.4993 | 43 | 21 | 22.5 | 0.90 | 8659974 | 154064969 | 0.0267 (128) |
| 23 | 0.4994 | 44 | 21 | 22.5 | 0.90 | 896761 | 13781153 | 0.0340 (271) |
| 24 | 0.4996 | 47 | 23 | 22.6 | 0.44 | 1812299 | 29217757 | 0.0392 (129) |
| 25 | 0.4999 | 46 | 21 | 22.6 | 0.91 | 7334638 | 129186433 | 0.0552 (120) |
| 26 | 0.4996 | 55 | 29 | 22.6 | 0.01 | 1001995 | 15518411 | 0.0576 (113) |
| 27 | 0.4998 | 50 | 23 | 22.6 | 0.45 | 2942697 | 48967099 | 0.0370 (108) |
| 28 | 0.4994 | 49 | 21 | 22.6 | 0.90 | 9530760 | 170523553 | 0.0216 (203) |
| 29 | 0.4992 | 51 | 22 | 22.5 | 0.68 | 1095816 | 17074553 | 0.0374 (158) |
| 30 | 0.4994 | 53 | 23 | 22.5 | 0.44 | 2654646 | 43882291 | 0.0299 (137) |
| 31 | 0.4991 | 52 | 21 | 22.5 | 0.90 | 2255617 | 36895447 | 0.0231 (142) |
| 32 | 0.4991 | 58 | 26 | 22.5 | 0.07 | 799199 | 12182279 | 0.0385 (280) |
| 33 | 0.4994 | 55 | 22 | 22.5 | 0.69 | 6226558 | 108580319 | 0.0301 (133) |
| 34 | 0.4991 | 60 | 26 | 22.5 | 0.07 | 585206 | 8723531 | 0.0324 (182) |
| 35 | 0.4997 | 59 | 24 | 22.6 | 0.25 | 9663074 | 173031913 | 0.0563 (107) |
| 36 | 0.4994 | 58 | 22 | 22.5 | 0.69 | 1989404 | 32270377 | 0.0459 (247) |
| 37 | 0.4999 | 62 | 25 | 22.6 | 0.14 | 9142521 | 163178417 | 0.0323 (118) |
| 38 | 0.4994 | 62 | 24 | 22.5 | 0.25 | 9050441 | 161435713 | 0.0341 (138) |
| 39 | 0.4996 | 62 | 23 | 22.6 | 0.44 | 3876143 | 65640581 | 0.0338 (109) |
| 40 | 0.4999 | 64 | 24 | 22.6 | 0.26 | 6384110 | 111500083 | 0.0282 (173) |
| 41 | 0.5001 | 63 | 22 | 22.6 | 0.70 | 4346288 | 74129173 | 0.0368 (231) |
| 42 | 0.4997 | 66 | 24 | 22.6 | 0.25 | 3769850 | 63728317 | 0.0307 (121) |
| 43 | 0.5001 | 69 | 26 | 22.6 | 0.07 | 8098688 | 143498639 | 0.0365 (176) |
| 44 | 0.4999 | 69 | 25 | 22.6 | 0.14 | 8004615 | 141737249 | 0.0398 (157) |
| 45 | 0.4999 | 67 | 22 | 22.6 | 0.69 | 7608542 | 134310289 | 0.0183 (174) |
| 46 | 0.4997 | 69 | 23 | 22.6 | 0.45 | 6921104 | 121479587 | 0.0377 (113) |
| 47 | 0.4997 | 68 | 21 | 22.6 | 0.90 | 6818188 | 119564513 | 0.0442 (134) |
| 48 | 0.5000 | 70 | 22 | 22.6 | 0.70 | 6519524 | 114012667 | 0.0276 (206) |
| 49 | 0.4997 | 73 | 24 | 22.6 | 0.25 | 4676555 | 80130719 | 0.0481 (138) |
| 50 | 0.5000 | 73 | 23 | 22.6 | 0.45 | 5048258 | 86909099 | 0.0286 (230) |
| 51 | 0.4997 | 72 | 21 | 22.6 | 0.90 | 5290081 | 91336379 | 0.0280 (199) |
| 52 | 0.5000 | 73 | 21 | 22.6 | 0.91 | 6938865 | 121811423 | 0.0369 (219) |
| 53 | 0.4997 | 75 | 22 | 22.6 | 0.69 | 7267855 | 127941937 | 0.0294 (253) |
| 54 | 0.4999 | 77 | 23 | 22.6 | 0.45 | 2883172 | 47910971 | 0.0303 (177) |
| 55 | 0.4998 | 79 | 24 | 22.6 | 0.26 | 8583379 | 152623421 | 0.0325 (498) |
| 56 | 0.4999 | 79 | 23 | 22.6 | 0.45 | 2486883 | 40932233 | 0.0317 (196) |
| 57 | 0.4993 | 83 | 26 | 22.5 | 0.07 | 8841181 | 157481573 | 0.0337 (121) |
| 58 | 0.4996 | 80 | 22 | 22.6 | 0.69 | 1233666 | 19380037 | 0.0273 (162) |
| 59 | 0.4998 | 82 | 23 | 22.6 | 0.45 | 725817 | 10988639 | 0.0255 (137) |
| 60 | 0.4996 | 88 | 28 | 22.6 | 0.02 | 4830852 | 82936849 | 0.0288 (148) |
| 61 | 0.4997 | 87 | 26 | 22.6 | 0.07 | 72094 | 911087 | 0.0321 (157) |
| 62 | 0.4997 | 87 | 25 | 22.6 | 0.14 | 9152879 | 163372267 | 0.0363 (131) |
| 63 | 0.4996 | 85 | 22 | 22.6 | 0.69 | 6399770 | 111790807 | 0.0197 (191) |
| 64 | 0.4998 | 86 | 22 | 22.6 | 0.69 | 5898515 | 102524033 | 0.0704 (135) |

Every record stretch has minimal period exactly `P`, except `P = 4`, whose record is the `P = 2`
record (alternating digits) seen with period `4`. Over `P = 1, …, 64`, `E_max - (f-model)` has
mean `+0.50` and standard deviation `1.89` (model: `≈ 1.87`); the extremes are `P = 26`
(`E = 29`, `p = 0.01`), `P = 60` (`E = 28`, `p = 0.02`) and `P = 1` (`E = 16`, *shorter* than the
model). Among 64 tests, two `p`-values `≤ 0.02` is what chance gives.

**The Diophantine statistic.** Over all `P ≤ 64` and all stretches starting at `n ≥ 100`,

    max E/(n + P) = 0.0882    (P = 2, n = 100, E = 9: exponent 1.088 for Q = 3·2^100),

and by range of the starting position (random model: about `log₂(n)/n`):

| n in | max E/(n+P) | (P, n, E) | log₂(n)/n at the left end |
|---|---|---|---|
| [10^2, 10^3) | 0.08824 | (2, 100, 9) | 0.06644 |
| [10^3, 10^4) | 0.01085 | (26, 1172, 13) | 0.00997 |
| [10^4, 10^5) | 0.00155 | (3, 12289, 19) | 0.00133 |
| [10^5, 10^6) | 0.00021 | (12, 108923, 23) | 0.00017 |
| [10^6, 10^7) | 0.00003 | (26, 1001995, 29) | 0.00002 |

So along every family `{2^n (2^P - 1)}`, `P ≤ 64`, the approximation exponents decay like
`1 + O(log n / n)`, exactly as for a random number: no trace of `μ > 2` behaviour, and in fact
the excesses never exceed `29` in the first `10^7` digits. (The naive ratio `L/(n + 1)` reaches
`0.676` at `P = 64`, `n = 104`, but that is the trivial `P/(n+1)` and measures nothing.) For
general denominators, see the continued fraction of `ρ` in `transcendence-evidence.md` §3
(`max_n ln q_{n+1}/ln q_n = 1.027` over `n ≥ 100`), which probes all `q`, not only the visible
families.

**Number of maximal stretches with excess `≥ t`** (fair model `M 2^{-(t+1)}`):

| t | P=1 | P=2 | P=3 | P=4 | P=5 | P=8 | P=16 | P=32 | P=64 | fair model |
|---|---|---|---|---|---|---|---|---|---|---|
| 14 | 17 | 566 | 359 | 376 | 346 | 386 | 372 | 362 | 326 | 305.2 |
| 16 | 2 | 167 | 83 | 102 | 92 | 113 | 96 | 95 | 83 | 76.3 |
| 18 | 0 | 55 | 21 | 37 | 19 | 31 | 22 | 25 | 30 | 19.1 |
| 20 | 0 | 20 | 5 | 12 | 2 | 7 | 6 | 8 | 4 | 4.8 |
| 22 | 0 | 10 | 2 | 2 | 0 | 3 | 0 | 4 | 1 | 1.2 |
| 24 | 0 | 2 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 0.3 |

For `P ≥ 3` the counts follow the fair model (`10`–`25%` above it at `t = 14`, within noise for
`t ≥ 18`; the small surplus reflects residual dependence between digits and was not explored
further). The two small periods deviate in opposite directions,
and for the same reason: `d_{i+1} = d_i` iff the gap `p_{i+3} - p_{i+2}` is `≡ 0 (mod 4)`, and
consecutive primes avoid repeating their residue (Lemke Oliver–Soundararajan): `P(repeat) =
0.4449`. Runs of equal digits (`P = 1`) are strings of gaps `≡ 0 (mod 4)` and are rarer than
fair; alternating stretches (the non-constant `P = 2` pattern) are strings of gaps `≡ 2 (mod 4)`
and are more frequent. Even an order-2 Markov model of the repeat indicator does not capture the
tails: runs are rarer still (two consecutive gaps of `4` are impossible modulo `3`), alternations
more frequent:

| t | runs with `≥ t` repeats | Markov | alternations with `≥ t+1` switches | Markov |
|---|---|---|---|---|
| 10 | 807 | 1165.7 | 5960 | 5289.8 |
| 14 | 17 | 38.8 | 561 | 452.7 |
| 18 | 0 | 1.3 | 55 | 38.7 |
| 22 | 0 | 0.0 | 10 | 3.3 |

(`P(repeat | repeat) = 0.4270`, `P(switch | switch) = 0.5409`.) These are constant-factor
effects on the frequency of patterns; they shift the records by `O(1)` and do not affect the
exponent. The right model for them is Hardy–Littlewood for prime constellations, not coin flips.

## 4. General denominators: what a theorem would need

By §1, `μ(ρ) = 2` (the generic value, by Khinchin) is the statement that for every `ε > 0` there
are only finitely many `q` with `‖qρ‖ < q^{-1-ε}`. In the stretch picture:

* **Visible denominators** (`ord_{q'}(2) = P` small compared with `log q`). For each fixed `P`
  one needs: every `P`-periodic stretch starting at `n` has excess `E_P(n) = o(n)` (for
  `μ = 2` along the family) or `≤ C n` (for `μ < ∞`). For `P = 1` this is Theorem 2.2/2.4.
  For `P ≥ 2` the non-constant `P`-periodic patterns must be broken, and this is a statement
  about **consecutive** primes, not about counts of primes in intervals. Already for `P = 2`
  the only non-constant pattern is alternation `1, 3, 1, 3, …`, broken exactly by two
  consecutive primes in the same class (a gap `≡ 0 (mod 4)`). An alternating stretch over all
  primes in `(x, 2x]` is compatible with every possible count `π(2x; 4, a) - π(x; 4, a)`, so no
  Bertrand/Breusch/Huxley-type theorem (which controls counts) can rule it out. What is needed
  is: *every interval `(x, 2x]` (or `(x, x + h(x)]`) contains `P` consecutive primes in one
  class* — a non-constant `P`-periodic word contains no constant block of length `P` (otherwise
  every residue class modulo `P` would carry the same digit). Given that for all `x ≥ x₀(P)`,
  every non-constant `P`-periodic stretch starting at `p_{n+2} ≥ x₀(P)` has length
  `≤ π(2p) - π(p) + P`, and Theorem 2.1's argument gives
  `|ρ - a/(2^n(2^P - 1))| ≥ 2^{-C n}` for `n ≥ n₀(P)` (together with the constant patterns,
  handled by §2).

  *Status.* Strings of `P` consecutive congruent primes exist infinitely often (Shiu 2000, by
  Maier's matrix method; Banks–Freiberg–Turnage-Butterbaugh 2015, with bounded gaps, by the
  Maynard–Tao sieve). The Maynard–Tao sieve is a lower bound for a weighted sum over
  `x ≤ n < 2x` valid for all large `x`, so I expect its proof to give such a string in every
  dyadic interval `(x, 2x]` for `x ≥ x₀(P)`; I have not checked the published arguments for this
  form, and `x₀(P)` is not explicit. This would settle each fixed visible family `P`, but not
  uniformly in `P`: the sieve produces strings of length `P` only once
  `log log x ≫ P`, so it reaches periods `P ≲ log log n`, a negligible set of denominators.

* **Invisible denominators** (`ord_{q'}(2) ≫ log q`, which is the typical case: `ord_{q'}(2)`
  is at least `q'^{1/2}` for almost all primes `q'`). The digits of `a/q'` over the block that
  the approximation controls (length `≈ μ log₂ q`) are not periodic within the block; the
  constraint is that the block is one of the `q'` words read off the expansions of `a/q'`, a set
  with no structure visible to prime-residue statistics. A theorem here needs control of
  `‖qρ‖` for all `q`, i.e. genuine Diophantine information about the real number `ρ`
  (equivalently its continued fraction), which nothing in the prime-pattern dictionary provides.
  Note that `μ(ρ) = 2` is the generic behaviour, but no non-trivial upper bound
  `μ(ρ) < ∞` is known either; `ρ` could a priori be a Liouville number, and only the dyadic part
  of that possibility is excluded (Theorem 2.4; Theorem 2.2 conditionally and formally).

So the honest summary is: **period 1 is a theorem about primes in progressions; period `P ≥ 2`
is a theorem about consecutive primes (Maynard–Tao territory, and then only for fixed `P`);
periods comparable to the denominator are not about primes at all.**

## 5. Mathlib: what is there, and what formalizing Breusch would take

Survey of the Mathlib in this project (`v4.34.1`):

| Topic | Declarations | Usable here? |
|---|---|---|
| Bertrand | `Nat.exists_prime_lt_and_le_two_mul (n) (hn0 : n ≠ 0)`: a prime in `(n, 2n]`; proof via `centralBinom`, with an explicit prime chain for `n < 512` (`Nat.exists_prime_lt_and_le_two_mul_succ`) | gives `R(n) ≤ π(2p) - π(p)` only for "some prime", not a prime of the other class |
| Chebyshev upper | `primorial_le_four_pow` (alias `primorial_le_4_pow`, deprecated 2026-03-21); `Chebyshev.theta_le_log4_mul_x`; `Chebyshev.psi_le`; `Chebyshev.pi_le_log4_mul_div` (explicit); `Chebyshev.eventually_primeCounting_le` (`π x ≤ (log 4 + ε) x / log x` eventually) | yes: used for `π(2x) ≤ 28 π(x)` |
| Chebyshev lower | `Chebyshev.psi_ge`, `Chebyshev.theta_ge`, `Chebyshev.pi_ge` (`π n ≥ (n log 2 - log(n+1))/log n`), `Nat.two_pow_le_mul_lcmUpto` | yes: used for `π(2x) ≤ 28 π(x)` |
| `π` growth | `Nat.primeCounting'_add_le`, `Nat.primeCounting_add_le` (`π(k + n) ≤ π k + φ(a)(n/a + 1)`), `Nat.primeCounting'_nth_eq`, `Nat.monotone_primeCounting` | linear in `n` only; the nth-prime API is what links runs to `π` |
| PNT | not in Mathlib (external project PrimeNumberTheoremAnd) | no |
| Primes in APs | `Nat.forall_exists_prime_gt_and_eq_mod` (Dirichlet, qualitative, via `L`-series); `Nat.exists_prime_gt_modEq_one` (cyclotomic, elementary) | no bound on *where* the prime is, so no run bound |
| Liouville | `Liouville x`, `Liouville.transcendental`, `LiouvilleWith p x` (`∃ C, ∃ᶠ n, ∃ m, x ≠ m/n ∧ |x - m/n| < C/n^p`), `volume_iUnion_setOfPred_liouvilleWith` | `LiouvilleWith` quantifies over all denominators `n`, so a dyadic bound does not refute it; no irrationality-exponent definition |
| Dirichlet approximation | `Real.exists_int_int_abs_mul_sub_le`, `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, `Real.exists_rat_eq_convergent` (Legendre) | the generic side; not needed here |

The dyadic bound therefore had to be stated directly (Theorem 2.2(4)); a `LiouvilleWith`-style
conclusion would need all denominators and is not available.

**Formalizing Breusch.** The finite part is cheap: as in Mathlib's Bertrand (`n < 512`), a
*doubling chain* of certified primes in each class (each `≤ 2×` the previous, from `7` up to the
threshold `x₀` of the analytic part) proves the statement below `x₀`; it has about `log₂ x₀`
primes per class, each checked by `norm_num`'s primality extension. The real work is the explicit
statement for `x ≥ x₀`: `θ(2x; 4, a) - θ(x; 4, a) > 0`. Writing
`θ(x; 4, ±1) = (θ(x) - log 2 ± θ_χ(x))/2` with `θ_χ(x) = Σ_{p≤x} χ₄(p) log p`, one needs

1. a *sharp* explicit Chebyshev lower bound for `θ(2x) - θ(x)`. Mathlib's constants (`log 2`
   below, `log 4` above) give `θ(2x) - θ(x) ≥ 2x log 2 - x log 4 - (error) < 0`: useless. One
   needs Chebyshev's own constants (from the factorial ratio `30! n!/((15n)!(10n)!(6n)!)`-type
   identities, `0.92 x < ψ(x) < 1.11 x`) or an Erdős-style central-binomial argument with
   explicit bounds — Mathlib's Bertrand is the latter, but it only shows `θ(2x) - θ(x) > 0`, not
   `≥ c x`;
2. an explicit bound `|θ_χ(2x) - θ_χ(x)| < θ(2x) - θ(x)`, from the twisted identity
   `Σ_{n≤x} χ₄(n) log n = Σ_{d≤x} Λ(d) χ₄(d) S(x/d)` with `S(y) = Σ_{m≤y} χ₄(m) ∈ {0, 1}`, which
   is the Chebyshev-type route to Dirichlet's theorem for modulus `4` with explicit constants
   (or an Erdős-style product, e.g. of `m² + 1` for the class `1`).

Breusch's paper proceeds by explicit Chebyshev-type estimates of this kind; elementary proofs in
Erdős's binomial style exist for small moduli (Erdős 1935 and later work on Bertrand in
progressions, surveyed by Moree). I have not re-derived either in this session, so the following
is an estimate, not a plan: items 1 and 2 are each roughly 1000–2000 lines of Lean on top of
Mathlib's `Chebyshev`/`Bertrand` infrastructure (real-analysis inequalities with explicit
constants are the bulk), plus a short certified chain; in total about 2000–4000 lines, a few
person-weeks of focused work. The main risk is the size of `x₀` produced by the explicit
constants (it decides whether the chain stays within `norm_num` primality range). Since the
formal dyadic theorem only uses Breusch through `BreuschFour`, discharging it would make
Theorem 2.2 unconditional with no other change.

## 6. Lean summary (`RokickiConstant/General/Diophantine.lean`)

| Lean name | Statement |
|---|---|
| `one_div_two_pow_le_binaryTail` | `d (n + j) = 1 → 1/2^(j+1) ≤ T_n` |
| `binaryTail_add_binaryTail_one_sub` | `T_n(d) + T_n(1 - d) = 1` |
| `binaryTail_le_one_sub_one_div_two_pow` | `d (n + j) = 0 → T_n ≤ 1 - 1/2^(j+1)` |
| `binaryTail_mem_Icc_of_ne` | `d (m + k) ≠ d m → T_m ∈ [2^{-(k+1)}, 1 - 2^{-(k+1)}]` |
| `exists_two_pow_mul_tsum_sub_binaryTail_eq_intCast` | `2^n x - T_n ∈ ℤ` |
| `one_div_two_pow_le_abs_tsum_sub_div_two_pow` | Theorem 2.1 |
| `abs_binaryTail_sub_binaryTail_add_le` | `E` agreeing digits ⇒ `|T_n - T_{n+P}| ≤ 2^{-E}` |
| `exists_abs_tsum_sub_div_le_of_periodic` | Proposition 1.1 |
| `Nat.primeCounting_two_mul_le` | `6 ≤ x → π(2x) ≤ 28 π(x)` |
| `RokickiConstant.BreuschFour` | Breusch's theorem, as a `Prop` |
| `RokickiConstant.primeCounting_oddPrime` | `π(p_{n+2}) = n + 2` |
| `RokickiConstant.exists_oddPrime_add_eq` | a prime `p > p_{n+2}` is `p_{n+2+k}`, `k = π(p) - π(p_{n+2})` |
| `RokickiConstant.rokickiDigit_ne_of_mod_four_ne` | different classes ⇒ different digits |
| `RokickiConstant.exists_rokickiDigit_ne_of_prime` | a prime of the other class in `(p, 2p]` ends the run |
| `RokickiConstant.exists_rokickiDigit_ne_of_breuschFour` | Theorem 2.2(1) |
| `RokickiConstant.exists_rokickiDigit_ne_le_of_breuschFour` | Theorem 2.2(2) |
| `RokickiConstant.one_div_two_pow_le_abs_rokickiConstant_sub_of_breuschFour'` | Theorem 2.2(3), `π`-form |
| `RokickiConstant.one_div_two_pow_le_abs_rokickiConstant_sub_of_breuschFour` | Theorem 2.2(3), `2^{-(28m+55)}` |
| `RokickiConstant.one_div_two_pow_pow_le_abs_rokickiConstant_sub_of_breuschFour` | Theorem 2.2(4), `(2^m)^{-83}` |

## 7. Open statements

1. **Breusch in Lean.** `RokickiConstant.BreuschFour` (§5). Discharging it makes the dyadic
   bound `|ρ - a/2^m| ≥ 2^{-(28m+55)}` unconditional.
2. **Dyadic exponent `1` in Lean.** `μ₂(ρ) = 1` needs primes of both classes in `(x, (1+δ)x]`
   for every `δ > 0` and `x ≥ x₀(δ)` (PNT in progressions modulo `4`, Theorem 2.4(1)).
3. **Strings of congruent primes in dyadic intervals.** For each `P ≥ 2`: for all
   `x ≥ x₀(P)`, `(x, 2x]` contains `P` consecutive primes `≡ 1 (mod 4)` (or `≡ 3`). This implies
   `|ρ - a/(2^n(2^P - 1))| ≥ 2^{-C n}` for `n ≥ n₀(P)` (§4). Expected to follow from the
   Maynard–Tao sieve; not checked.
4. **`μ(ρ) < ∞`.** Open; equivalent to controlling `‖qρ‖` for denominators `q` whose odd part
   has large multiplicative order of `2`, where the prime-pattern dictionary gives nothing.
   Numerically (§3 and `transcendence-evidence.md` §3) `ρ` behaves like a number with `μ = 2`.

## References

* R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates, daß zwischen x und 2x stets
  Primzahlen liegen*, Math. Z. 34 (1932), 505–526.
* P. Erdős, *Über die Primzahlen gewisser arithmetischer Reihen*, Math. Z. 39 (1935), 473–491.
* P. Moree, *Bertrand's postulate for primes in arithmetical progressions*, Comput. Math. Appl.
  26 (1993), 35–43.
* H. L. Montgomery, R. C. Vaughan, *The large sieve*, Mathematika 20 (1973), 119–134.
* J. B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois J. Math. 6 (1962), 64–94.
* M. N. Huxley, *On the difference between consecutive primes*, Invent. Math. 15 (1972),
  164–170.
* D. K. L. Shiu, *Strings of congruent primes*, J. London Math. Soc. (2) 61 (2000), 359–373.
* W. D. Banks, T. Freiberg, C. L. Turnage-Butterbaugh, *Consecutive primes in tuples*, Acta
  Arith. 167 (2015), 261–266.
* R. J. Lemke Oliver, K. Soundararajan, *Unexpected biases in the distribution of consecutive
  primes*, Proc. Natl. Acad. Sci. USA 113 (2016), E4446–E4454.
