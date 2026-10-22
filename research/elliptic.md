# The Rokicki constant of an elliptic curve: the sign of `a_p`

**Status.** Research, with no Lean (Round 4, item 4 of `PROGRAM.md`). Nothing new is proved
formally. Each claim carries one of four labels:

* **[proved]**: a complete argument is given here, or it is elementary;
* **[literature]**: a published theorem, cited;
* **[numerical]**: printed by `python3 scripts/elliptic.py` (all `78 498` primes below `10^6` for
  every curve, and all `50 847 534` primes below `10^9` for the four CM curves; about 3 minutes
  on 24 cores);
* **[heuristic]**: a conjecture, with its derivation.

**Notation.**

* `p_0 = 2 < p_1 = 3 < …` are all the primes.
* For `E/ℚ` with minimal model `E`, `a_p = p + 1 − #Ẽ(𝔽_p)`, where `Ẽ` is the reduction mod `p`
  counted with its singular point, if any. So `a_p = 0, +1, −1` at additive, split and nonsplit
  bad primes.
* The digit is `d_k = [a_{p_k} < 0]`: it is `1` exactly when `Ẽ` has more than `p + 1` points.
* The constant is `ρ_E = Σ_k d_k 2^{−(k+1)}`.
* The sign race is `S_E(x) = Σ_{p≤x} sgn a_p = #{p ≤ x : a_p > 0} − #{p ≤ x : a_p < 0}`, with
  `sgn 0 = 0`. On the index scale, `D_E(n) = #{k < n : a_{p_k} < 0} − #{k < n : a_{p_k} > 0}`
  equals `−S_E(p_{n−1})`.
* `θ_p ∈ [0, π]` is defined by `a_p = 2√p cos θ_p`, and `π(√x) ≈ 2√x/log x`. Biases are quoted in
  units of `π(√x)`; "log-mean" is the logarithmic average over `x ∈ [10^4, X]`, sampled at the
  primes with weight `1/p`.
* `r` is the rank, `W(E)` the root number, and `U_j` the Chebyshev polynomials of the second kind:
  `U_j(cos θ) = sin((j+1)θ)/sin θ = tr Sym^j`.

Indexing by the good primes only deletes finitely many terms from the digit sequence. Deleting
finitely many terms neither creates nor destroys eventual periodicity, so the irrationality
question is the same for both conventions. The values below use all primes.

## 0. Summary

1. **CM curves have biases of order `√x`, and three of the four are explicit.**
   * `y² = x³ + x` (64a): `+√x/(2π)` (`gaussian-primes.md`).
   * `y² = x³ + 1` (36a): `+√x/(6π)` **[heuristic, new]**.
   * `y² + y = x³` (27a): `−√x/(6π)` **[heuristic, new]**.
   * `y² = x³ − x` (32a): a Chebyshev-size bias only.

   For 36a and 27a, the two independent heuristics (Bateman–Horn on lines, Hecke modes with root
   numbers) agree on the leading constant. The root numbers `W(ψ^j)`, computed for `j ≤ 41`,
   align with the Fourier coefficients on average by exactly `+1/3` and `−1/3`, which is what the
   lattice model requires (§4).
2. **Non-CM curves have biases of order `√x/log x`, and the direction follows the rank.**
   Expanding `sgn cos θ` in `U_j` gives explicit coefficients `c_j`. The prime-square terms of all
   `L(s, Sym^j E)` give `+½` per mode, and central zeros give `−r_j`. For semistable `E`,
   `W(Sym^j E) = (−2/j) W(E)` (checked for `j = 3` on four curves). The predicted mean is
   `B_E = (8/(3π))(½ − r) + ½ W(E) R`, with `R = −0.38158`. It is positive exactly when `r = 0`,
   and each unit of rank costs `8/(3π) = 0.849`. Over 139 quadratic twists:
   * the correlation between `B` and the observed bias is `+0.67`;
   * the sign race is `0.832 ×` the classical race `Σ a_p/√p`, with intercept `0.007`, against
     `c_1 = 0.849`;
   * the modes `j ≥ 3` are not detected at `10^6`.
3. **Rational torsion adds a "discreteness" term [heuristic, new].** The congruence
   `a_p ≡ p + 1 (mod m)` shifts the lattice of possible values of `a_p` asymmetrically. This adds
   `Δ_E = μ̄(m)/π`, giving `−0.239` for 11a1 (`m = 5`) and `+0.318` for 14a1 (`m = 6`). After the
   modes `j ≤ 101` are removed, the remainder is `+0.30` for 14a1, against `+0.006 ± 0.06` for
   twists with `Δ = 0`.
4. **Irrationality of `ρ_E` is open for every `E`.** The method would need all `Sym^j` at once,
   uniformly in `j`. *Congruence* digits `[Frob_p ∈ C]` are different. They are finite
   combinations of Artin `L`-functions, and the project's parity argument transfers: the digit is
   not eventually periodic whenever the defect `|C| − ν(C)` is odd. The digit `[a_p even]` has
   defect `0` and is **not** settled. The digits `[E(𝔽_p)[2] ≅ (ℤ/2)²]`, `[3 | #E(𝔽_p)]`,
   `[a_p ≡ t (mod ℓ)]` (`t ≢ 0`, `ℓ = 3, 5, 7`, surjective image), and others have odd defect
   (§6).

## 1. Curves and computation [numerical]

| curve | model (minimal) | `N` | rank | `W` | torsion | CM |
|---|---|---|---|---|---|---|
| 11a1 | `y² + y = x³ − x² − 10x − 20` | 11 | 0 | +1 | ℤ/5 | — |
| 14a1 | `y² + xy + y = x³ + 4x − 6` | 14 | 0 | +1 | ℤ/6 | — |
| 37a1 | `y² + y = x³ − x` | 37 | 1 | −1 | 0 | — |
| 389a1 | `y² + y = x³ + x² − 2x` | 389 | 2 | +1 | 0 | — |
| 5077a1 | `y² + y = x³ − 7x + 6` | 5077 | 3 | −1 | 0 | — |
| 64a | `y² = x³ + x` | 64 | 0 | +1 | ℤ/2 | `ℤ[i]` |
| 32a | `y² = x³ − x` | 32 | 0 | +1 | (ℤ/2)² | `ℤ[i]` |
| 36a | `y² = x³ + 1` | 36 | 0 | +1 | ℤ/6 | `ℤ[ω]` |
| 27a | `y² + y = x³` (≅ `y² = x³ + 16`; isogenous to `y² = x³ − 432`) | 27 | 0 | +1 | ℤ/3 | `ℤ[ω]` |

**How `a_p` is computed.**

* **Non-CM curves.** For odd `p`,

      a_p = −Σ_{x mod p} ((4x³ + b₂x² + 2b₄x + b₆)/p),

  obtained by completing the square, which is valid for good and bad `p`. The sum is vectorized in
  numpy over 24 processes (about 85 s for five curves). For `p = 2` the points of the long model
  are counted directly.
* **CM curves.** Classical formulas (Gauss, Jacobi; Ireland–Rosen [IR] ch. 18), checked against
  the Legendre sum for all `p < 10^4`:
  * 64a: `p = a² + b²`, `a` odd `> 0`: `a_p = 2aχ₄(a)`;
  * 32a: `a_p = 2aχ₄(a)χ₈(p) = 2 Re π₀`, with `π₀ ≡ 1 mod (2+2i)`;
  * 36a: `p = t² + 3s²` with `t ≡ 1 (mod 3)`: `a_p = 2t`;
  * 27a: `4p = L² + 27M²` with `L ≡ 2 (mod 3)`: `a_p = L`;
  * `a_p = 0` at the inert primes, `p ≡ 3 (mod 4)` or `p ≡ 2 (mod 3)`.

  Lattice enumeration takes these to `10^9` in 15 s.

**Checks.**

* the Hasse bound;
* `a_p ≡ p + 1 (mod 5)` for 11a1 and `(mod 6)` for 14a1;
* the Fricke relation `φ(1/(Ny)) = W N y² φ(y)` of `f = Σ a_n qⁿ`, to `10^{−12}`, at the stated
  level `N` with the stated `W`, for all nine curves;
* `L(E,1) = 0.25384` (11a1) and `0.33022` (14a1); `L'(E,1) = 0.30600` (37a1);
  `L(E,1) = 0` for 389a1 and `L'(E,1) = 0` for 5077a1, to `10^{−16}`.

The ranks are Cremona's; the computation only confirms analytic rank `0, 0, 1, ≥ 2, ≥ 3`.

## 2. The constants [numerical, exact]

Each value is certified by an exact enclosure `A/2^{200} ≤ ρ_E ≤ (A+1)/2^{200}` from `200` exact
digits; the 40-decimal truncations of both ends agree. The script also prints `A` in hex. The
digits are `d_0 d_1 … d_63`, with `d_0` the digit of `p = 2`.

| curve | `ρ_E` (40 decimals) | first 64 digits |
|---|---|---|
| 11a1 | 0.8224672455503711848667521611079929385038 | `1101001010001101001101101010000110101011100010000001111001110000` |
| 14a1 | 0.7671301146470256983990435814925321822257 | `1100010001100010101000111010001000101111100010100110110011111001` |
| 37a1 | 0.9852644274125864184187179948159457081488 | `1111110000111010010010100001110110100110001100111001010011000110` |
| 389a1 | 0.9955367968911638299559402320701818610325 | `1111111011011011011111111110000010011100101101010110100101011101` |
| 5077a1 | 0.9996334327217896535896387880694358119494 | `1111111111100111111110100000010110000111001111101101101010101011` |
| 64a | 0.0156407385730413795024802789952622425909 | `0000010000000001000010000000110010101000000100000100100000000000` |
| 32a | 0.1262250106095451718341917133399881124432 | `0010000001010000010010000100010010000001010110000000100010100100` |
| 36a | 0.0632350445521554541119753416860594134937 | `0001000000110000001011000000000001010000000001110100000001000010` |
| 27a | 0.0668988600557556268905993486605982163490 | `0001000100100000010010001010000000010100010000110100000000000010` |

* **The leading digits encode the rank.** For curves of high rank, `#Ẽ(𝔽_p)` tends to be large
  for small `p` (the Birch–Swinnerton-Dyer heuristic `Π_{p≤x} #Ẽ(𝔽_p)/p ≈ C (log x)^r`). Hence
  `ρ_{5077a1} = 0.9996…`: `a_p < 0` for all eleven primes `p ≤ 31`.
* **CM curves have one-digits only at split primes.** So `ρ_E` is small for them, and the digits
  have density `1/4`.

## 3. The sign race [numerical]

| curve | x | `S` | `S/√x` | `S log x/√x` | `S/π(√x)` | frac `S<0` | log-frac `S<0` | sign changes | density of 1s | `#{a_p=0}` |
|---|---|---|---|---|---|---|---|---|---|---|
| 11a1 | 1e4 | +16 | +0.160 | +1.47 | +0.64 | 0.172 | 0.782 | 23 | 0.4874 | 15 |
| 11a1 | 1e5 | +53 | +0.168 | +1.93 | +0.82 | 0.239 | 0.748 | 147 | 0.4951 | 41 |
| 11a1 | 1e6 | +222 | +0.222 | +3.07 | +1.32 | 0.064 | 0.703 | 261 | 0.4980 | 98 |
| 14a1 | 1e4 | −5 | −0.050 | −0.46 | −0.20 | 0.205 | 0.669 | 26 | 0.4923 | 24 |
| 14a1 | 1e5 | +59 | +0.187 | +2.15 | +0.91 | 0.324 | 0.657 | 125 | 0.4932 | 71 |
| 14a1 | 1e6 | +9 | +0.009 | +0.12 | +0.05 | 0.343 | 0.627 | 247 | 0.4986 | 205 |
| 37a1 | 1e4 | +2 | +0.020 | +0.18 | +0.08 | 0.834 | 0.964 | 37 | 0.4955 | 9 |
| 37a1 | 1e5 | −23 | −0.073 | −0.84 | −0.35 | 0.552 | 0.923 | 126 | 0.4996 | 31 |
| 37a1 | 1e6 | −164 | −0.164 | −2.27 | −0.98 | 0.715 | 0.907 | 360 | 0.5005 | 82 |
| 389a1 | 1e4 | −51 | −0.510 | −4.70 | −2.04 | 1.000 | 1.000 | 0 | 0.5175 | 8 |
| 389a1 | 1e5 | −44 | −0.139 | −1.60 | −0.68 | 0.953 | 0.998 | 22 | 0.5008 | 28 |
| 389a1 | 1e6 | −192 | −0.192 | −2.65 | −1.14 | 0.994 | 0.998 | 22 | 0.5008 | 72 |
| 5077a1 | 1e4 | −54 | −0.540 | −4.97 | −2.16 | 1.000 | 1.000 | 0 | 0.5167 | 13 |
| 5077a1 | 1e5 | −103 | −0.326 | −3.75 | −1.58 | 1.000 | 1.000 | 0 | 0.5033 | 39 |
| 5077a1 | 1e6 | −326 | −0.326 | −4.50 | −1.94 | 1.000 | 1.000 | 0 | 0.5015 | 92 |
| 64a | 1e6 | +245 | +0.245 | +3.39 | +1.46 | 0 | 0 | 0 | 0.2480 | 39323 |
| 32a | 1e6 | +51 | +0.051 | +0.71 | +0.30 | 0.054 | 0.261 | 149 | 0.2492 | 39323 |
| 36a | 1e6 | +145 | +0.145 | +2.00 | +0.86 | 0.005 | 0.125 | 33 | 0.2490 | 39267 |
| 27a | 1e6 | +7 | +0.007 | +0.10 | +0.04 | 0.608 | 0.429 | 377 | 0.2498 | 39267 |

* "frac" is over the prefixes `p ≤ x`; "log-frac" weights them by `1/p`.
* The log-means of `S/π(√x)` over `[10^4, 10^6]` are:
  * 11a1 `+0.43`, 14a1 `+0.28`, 37a1 `−0.11`, 389a1 `−1.05`, 5077a1 `−2.07`;
  * 64a `+1.20`, 32a `+0.29`, 36a `+0.49`, 27a `−0.26`.
* On the index scale, `D_E(78498) = −S_E(10^6)`.

The non-CM rows are ordered by rank, and the order of the biases is the order of the ranks. The
CM curves to `10^9` are in §4.4.

## 4. Theory

### 4.1 Equidistribution: density of the digit [literature / proved]

* **Non-CM `E`.** Sato–Tate holds: `θ_p` is equidistributed for `μ_ST = (2/π) sin²θ dθ`
  (Clozel–Harris–Shepherd-Barron–Taylor [CHT, HSBT, T] for non-integral `j`, which covers all five
  curves here; Barnet-Lamb–Geraghty–Harris–Taylor [BGHT] in general). So the digit has density
  `½`. Moreover `#{p ≤ x : a_p = 0} = o(π(x))` (Serre [Se]), and the set is infinite
  (Elkies [El]).
* **CM `E` with field `K`.** By Deuring, `a_p = 0` at the primes inert in `K`, and
  `a_p = ψ(𝔭) + ψ(𝔭̄)` at split `p` for a Grössencharacter `ψ`. By Hecke, `arg ψ(𝔭)` is
  equidistributed (uniform measure) on the split primes. So the digit has density `½` along the
  split primes and `¼` along all primes.
* **`[a_p < 0]` is not a function of `p mod N` [proved, given the literature].** Newton–Thorne
  [NT] prove `Sym^j E` cuspidal automorphic on `GL_{j+1}` for every `j`. Then
  `L(s, Sym^j E ⊗ χ)` does not vanish on `Re s = 1` (Jacquet–Shalika), so Sato–Tate holds in
  every class `p ≡ c (mod N)`, and each class has digit density `½`. A digit equal to
  `f(p mod N)` on a set of density `1` would have density `0` or `1` in each class. For CM curves
  this is `gaussian-primes.md` Prop. 2. **[numerical]** Over the unit classes mod
  `3, 4, 5, 8, 12`, the fraction of `a_p < 0` lies in:
  * `[0.495, 0.501]` for 11a1, even though `a_p mod 5` *is* a function of `p mod 5` there;
  * `[0.498, 0.504]` for 37a1;
  * `[0.499, 0.508]` for 5077a1.

### 4.2 The expansion of the sign [proved]

In `L²(μ_ST)`,

    sgn(cos θ) = Σ_{j odd} c_j U_j(cos θ),    c_j = (2/π) (−1)^{(j−1)/2} (1/j + 1/(j+2)),

and `c_j = 0` for even `j`.

*Derivation.* Use `sin((j+1)θ) sin θ = ½(cos jθ − cos(j+2)θ)` and, for odd `m`,
`∫_0^π sgn(cos θ) cos(mθ) dθ = 2 sin(mπ/2)/m`.

Properties:

* `c_1 = 8/(3π) = 0.8488`, `c_3 = −0.3395`, `c_5 = 0.2183`, `c_7 = −0.1617`.
* `Σ c_j = 2/π`, by telescoping the Leibniz series.
* The series `Σ c_j sin((j+1)θ)` is the Fourier sine series of `sgn(cos θ) sin θ`, which is
  piecewise smooth. So the expansion converges **pointwise** on `(0, π)`, to `sgn cos θ` and to `0`
  at `θ = π/2`; this matches `sgn 0 = 0`.

Hence, for every `x`, exactly,

    S_E(x) = Σ_{j odd} c_j M_j(x),     M_j(x) = Σ_{p ≤ x, good} U_j(cos θ_p) = Σ_{p≤x} λ_{Sym^j E}(p).

The sign digit is an infinite combination of symmetric-power traces. Its coefficients decay like
`(4/π)/j`, as in the Gaussian case.

### 4.3 Prime squares, central zeros, root numbers

**Prime squares [proved, given [NT]].** Let `g_p = diag(e^{iθ_p}, e^{−iθ_p})`. Then

    log L(s, Sym^j E) = Σ_p U_j(cos θ_p) p^{−s} + ½ Σ_p tr Sym^j(g_p²) p^{−2s} + (holomorphic for Re s > 1/3).

* We have `tr Sym^j(g²) = tr Sym²(Sym^j)(g) − tr Λ²(Sym^j)(g)`.
* For odd `j`, `Sym^j` is **symplectic**: `Λ²Sym^j` contains the trivial representation once,
  and `Sym²Sym^j` does not.
* Both are sums of `Sym^m` with `m ≤ 2j`, which are automorphic by [NT] and regular and nonzero
  at `s = 1` for `m ≥ 1`.
* Hence `Σ_p tr Sym^j(g_p²) p^{−2s} = −log 1/(2s−1) + O(1)` as `s → ½⁺`. The sign is the
  Frobenius–Schur indicator `−1`. For `j = 1` this is the familiar `E_ST[a_p²/p − 2] = −1`.

So, if `L(s, Sym^j E)` has no real zeros in `(½, 1)` and vanishes to order `r_j` at `½`,

    Σ_p U_j(cos θ_p) p^{−s} = (½ − r_j) log 1/(2s−1) + O_j(1),      s → ½⁺.

In the Rubinstein–Sarnak dictionary [RS] (GRH, and LI for the limiting distribution), mode `j`
has mean bias `(½ − r_j) π(√x)`. For `j = 1` this is Sarnak's `1 − 2r` in units of `√x/log x`
[Sa].

**Root numbers [derivation; checked for `j = 3`].** Let `E` be semistable and `j` odd.

* At infinity, `Sym^j` has Hodge types `(j−i, i)`, so
  `W_∞ = Π_{i<j/2} i^{j−2i+1} = (−1)^{m(m+1)/2}`, with `m = (j+1)/2`.
* At a multiplicative prime, `Sym^j(sp(2) ⊗ μ) = sp(j+1) ⊗ μ^j`, whose root number is
  `(−μ^j(Frob))^j = −μ(Frob) = w_p(E)`.
* Hence

      W(Sym^j E) = −W_∞(Sym^j) W(E) = (−2/j) W(E):  + for j ≡ 1, 3 (mod 8), − for j ≡ 5, 7 (mod 8).

* For a quadratic twist `E_d`, with `(d, N) = 1`,
  `W(Sym^j E_d) = W(Sym^j E) χ_d(N) ε_d^{j+1}`, where `ε_d = 1` for `d > 0` and `i` for `d < 0`.
  For `j = 1` this reduces to the classical `W(E_d) = χ_d(−N) W(E)`.

**[numerical]** The functional equation of `L(s, Sym³E)` (conductor `N³`, gamma factor
`Γ_ℂ(s+½)Γ_ℂ(s+3/2)`, theta kernel `8π²t K₁(4π√t)`) holds to `10^{−10}` with:

| curve | `W(Sym³E)` | `W(E)` | `L(½, Sym³E)` |
|---|---|---|---|
| 11a1 | +1 | +1 | 1.1402 |
| 14a1 | +1 | +1 | 1.2589 |
| 37a1 | −1 | −1 | 0 (odd) |
| 389a1 | +1 | +1 | 4.4986 |

The central values were computed only for `j = 3`.

**The predicted bias [heuristic].** Assume minimal vanishing, `r_j = (1 − W_j)/2` for `j ≥ 3`,
so that `½ − r_j = ½W_j`. Assume also that the modes may be summed. Then

    S_E(x) ≈ B_E π(√x),    B_E = c_1(½ − r) + ½ W(E) R,    R = Σ_{j≥3} c_j (−2/j) = −0.381582.

`c_j(−2/j) = (2/π)(2/j)(1/j + 1/(j+2))`, so the series for `R` converges **absolutely**. This is
the decisive difference from the CM case (§4.6), where root numbers and coefficients align and
the mode sum diverges.

| rank | `W` | `B_E` | mean of `(log x/√x) S_E` (`= 2B_E`) |
|---|---|---|---|
| 0 | +1 | +0.234 | +0.47 |
| 1 | −1 | −0.234 | −0.47 |
| 2 | +1 | −1.464 | −2.93 |
| 3 | −1 | −1.931 | −3.86 |

* For semistable `E` without the term of §4.4, the race is biased towards `a_p > 0` iff `r = 0`.
* Each unit of rank lowers the mean by `c_1 = 8/(3π)` (twists: `W_j` from the formula above).
* This is the mechanism of Sarnak's letter [Sa], written out with explicit coefficients for the
  sign function. We have not compared constants with [Sa] line by line.
* Mazur [Ma] discusses such races and their dependence on the rank. Fiorilli [Fi] studies them
  (conditionally) when the rank is large compared with the conductor.

### 4.4 The discreteness term from rational torsion [heuristic, new here]

**The setup.** If `E(ℚ)` has a point of order `m ≥ 3`, then `a_p ≡ p + 1 (mod m)` for good
`p ∤ m`. For fixed `p` the possible values of `a_p` lie on the lattice `r + mℤ`, with
`r ≡ p + 1 (mod m)`. Off `r ≡ 0, m/2`, this lattice is **not symmetric** under `a ↦ −a`.
For 11a1 at `p ≡ 3 (mod 5)`, `a_p ∈ {…, −6, −1, 4, 9, …}`. Below `10^6`, `a_p = 1` occurs only
at `p = 5` and at the bad prime `11`, while `a_p = −1` occurs 39 times.

**The local-density model.** Take a Lang–Trotter model [LT]: density `m·(1/(π√p))√(1 − a²/4p)` on
the allowed class, smooth otherwise. Summing `sgn a` over `r + mℤ` against a slowly varying even
weight gives

    E[sgn a_p | p] ≈ μ(r)/(π√p),    μ(r) = m − 2r (0 < r < m),   μ(0) = 0,

and so

    Δ_E = μ̄/π,   μ̄ = mean over units c mod m of μ((c+1) mod m).

**Values.**

* 11a1 (`m = 5`): `μ = 1, −1, −3, 0` for `p ≡ 1, 2, 3, 4 (mod 5)`, so `Δ = −3/(4π) = −0.239`.
* 14a1 (`m = 6`): `μ = 2, 0`, so `Δ = 1/π = +0.318`.
* `m = 1, 2, 4`: `Δ = 0`.

A model using the empirical distribution of `a_p mod M` in each class of `p mod M` gives:

* `−0.259` for 11a1 (`M = 5`);
* `+0.313` for 14a1 (`M = 12`);
* `|Δ| ≤ 0.03` for the torsion-free curves.

(The script prints `M = 5` and `M = 12`; in a scratch run, `M = 25` and `36` changed these by at
most `0.03`.)

So only the torsion congruence matters.

The term is invisible to every fixed mode `j`. In `cos θ_p` the lattice has spacing
`m/(2√p)`, so only the modes `j ≳ √p/m` resolve it, and that is where the mode heuristic of §4.3
is not uniform. The effect is not confined to small `|a_p|`: it is the offset of the whole lattice,
weighted by the slope of the Sato–Tate density.

**Test [numerical].** Compute the remainder `S − Σ_{j≤101} c_j M_j` (log-mean), which is the part
of the race not carried by the modes `j ≤ 101`:

| curve | remainder | `Δ_E` |
|---|---|---|
| 14a1 | +0.30 | +0.32 |
| 11a1 | −0.15 | −0.24 |
| 37a1 | −0.07 | 0 |
| 389a1 | −0.05 | 0 |
| 5077a1 | −0.17 | 0 |
| twists of 11a1 (all have `Δ = 0`) | +0.006, std 0.062 | 0 |
| twists of 37a1 | +0.019, std 0.072 | 0 |

The 14a1 value is a clear detection. 11a1 lies in the predicted direction, but within the spread
of the torsion-free curves.

### 4.5 Non-CM data against the prediction [numerical]

| curve | `B_E` | `Δ_E` | observed log-mean `S/π(√x)` | race `Σ a_p/√p` (pred `½ − r`) | `S − c_1·race` | pred `½ΣW_jc_j + Δ` |
|---|---|---|---|---|---|---|
| 11a1 | +0.234 | −0.239 | +0.429 | +0.485 | +0.02 | −0.43 |
| 14a1 | +0.234 | +0.318 | +0.279 | +0.474 | −0.12 | +0.13 |
| 37a1 | −0.234 | 0 | −0.113 | −0.666 | +0.45 | +0.19 |
| 389a1 | −1.464 | 0 | −1.048 | −1.798 | +0.48 | −0.19 |
| 5077a1 | −1.931 | 0 | −2.071 | −3.046 | +0.52 | +0.19 |

**Twist families [numerical].** Take all fundamental `d` with `|d| ≤ 150` and `(d, 5N) = 1`: 67
twists of 11a1 and 72 of 37a1. For each, `W(E_d) = χ_d(−N) W(E)`, and the analytic rank comes
from `L(1)` or `L'(1)` (eleven twists have rank `≥ 2`, e.g. 11a1 ⊗ `χ_{−47}`, `N = 24 299`).

| family | rank | #twists | mean `B` | mean observed | mean race (pred `½ − r`) |
|---|---|---|---|---|---|
| 11a1 | 0 | 29 | +0.34 | +1.01 | +1.12 |
| 11a1 | 1 | 35 | −0.36 | −0.38 | −0.56 |
| 11a1 | 2 | 3 | −1.22 | −1.08 | −1.56 |
| 37a1 | 0 | 28 | +0.35 | +0.76 | +0.91 |
| 37a1 | 1 | 36 | −0.37 | −0.61 | −0.55 |
| 37a1 | 2 | 8 | −1.37 | −1.34 | −1.64 |

The per-twist standard deviation is `0.5–0.9`.

**What the data show at `10^6`.**

1. **The direction follows the rank.**
   * Over all 139 twists, the correlation between `B` and the observed bias is `+0.67`.
   * The pair 11a1 (rank 0, `S/π(√x) = +1.32` at `10^6`) and 11a1 ⊗ `χ_{−7}` (`N = 539`, rank 1,
     `−0.96`) flips sign.
   * 389a1 and 5077a1 are negative at `99.4%` and `100%` of all `x ≤ 10^6`.
2. **The sign race is `c_1` times the classical race.** The least-squares fit over the twists is
   `S = 0.832 · race + 0.007`, with correlation `0.83`, against `c_1 = 8/(3π) = 0.849`. The
   `j = 1` mode, that is, the rank and the zeros of `L(s, E)`, carries the race.
3. **The modes `j ≥ 3` are not detected.** The residual `S − c_1·race` has correlation `−0.01`
   with the predicted `½Σ_{j≥3} c_jW_j = ±0.19, ±0.05` across the twists. Its group means are
   `0 ± 0.15`. Individual mode sums `M_j`, `j ≥ 5`, scatter by `±1` around `±½`. The conductor of
   `Sym^j` is `N^j`, so `x = 10^6` is far from asymptotic for `j ≥ 5`.
4. **Rank-0 twists of large conductor overshoot both races** by about `+0.5`: `+1.18` versus
   `+0.90` for `N ≥ 2·10^4` versus `N < 2·10^4` in the 11a1 race. This is a finite-range,
   large-conductor effect shared by `Σ a_p/√p`, so it is not specific to the sign.
5. **Rank `≥ 1` overshoots in the classical race**: observed `−0.67, −1.80, −3.05` against
   `−½, −3/2, −5/2`. This is the familiar slow convergence (low-lying zeros).

### 4.6 CM curves: three explicit `√x` constants

**64a and 32a.** These are `gaussian-primes.md` §§1–2:

* `sgn a_p(64a) = χ₄(a)` and `sgn a_p(32a) = sgn Re π₀`;
* `S_{64a} ~ √x/(2π)`, from Bateman–Horn on the lines `a = const` (constant `HK = 4/π`) and from the
  Hecke modes `λ^jχ₈`, all of which have `(−1)^{(j−1)/2} W = +1`;
* 32a: `W(λ^j) = (−2/j)`, so the mode sum converges, to `(1/π) L(1, χ₈) = 0.198` in units of
  `π(√x)`.

**36a and 27a: the lines [heuristic, new].** Both curves have line-constant signs.

* 36a: `a_p = 2t` with `p = t² + 3s²`, `t ≡ 1 (mod 3)`, so `sgn a_p = χ₋₃(|t|)`.
* 27a: `a_p = L` with `4p = L² + 27M²`, `L ≡ 2 (mod 3)`, so `sgn a_p = −χ₋₃(|L|)`.

The form is exactly that of the digit `[a ≡ 3 (mod 4)]` of 64a.

*Bateman–Horn on a line.* Write `χ = χ₋₃`. The line constant is
`C = (3/2) H₃ c₂ w(ℓ)`, where:

* `H₃ = Π_{q≥5}(1 − χ(q)/(q−1)) = 1.120733`;
* `w(ℓ) = Π_{q|ℓ, q≥5} (q−1)/(q−1−χ(q))`;
* `c₂ = 1` for 36a; for 27a, `c₂ = 2` for odd `L` (then `M` is odd and `(L² + 27M²)/4` is always
  odd) and `1` for even `L`.

*Summing over lines.* `χw = Σ_{d|ℓ} u(d) χ(ℓ/d)` with `u(q) = 1/(q−1−χ(q))`. The mean of
`Σ_{m≤y} χ(m)` is `1/3`; the mean of `Σ_{m≤y} c₂(m)χ(m)` is `1`. Summing the lines with
`√(x − t²)/√3` (36a) or `½√((4x − L²)/27)` (27a) points each gives

    S_{36a}(x) ~ +(1/4) H₃ K'' √x/√3,    S_{27a}(x) ~ −(1/4) H₃ K'' √x/√3,
    K'' = (1/3) Π_{q≥5} (1 + u(q))(1 − 1/q).

*The constant is exactly `1/(6π)` [proved, algebra].* At each `q ≥ 5` the local factors of `H₃`
and `3K''` multiply to `1 − χ(q)/q`:

* `χ(q) = 1`: `((q−2)/(q−1))·((q−1)/(q−2))·((q−1)/q)`;
* `χ(q) = −1`: `(q/(q−1))·((q+1)/q)·((q−1)/q)`.

So

    H₃ · 3K'' = Π_{q≥5}(1 − χ(q)/q) = (2/3)/L(1, χ₋₃) = 2√3/π,

hence `(1/4) H₃K''/√3 = 1/(6π)`. This gives

    S_{36a}(x) ~ +√x/(6π),    S_{27a}(x) ~ −√x/(6π)    (= ±0.053052 √x).

**The Hecke modes [numerical + heuristic].**

* *Setup.* `ψ(α) = α` for `α ≡ 1 (mod 3)` (27a, conductor `(3)`, level 27), and `ψ(β) = β` for
  `β ≡ 1 (mod 2√−3)` (36a, level 36). Inert primes give `ψ^j((p)) = −1` for odd `j`, so every mode
  gets `+¼` (as for 64a). For `3 | j` the two characters coincide: `ψ^j` then has conductor
  `(√−3)` and level 9.
* *Root numbers.* The Fricke test of the CM forms `Σ ψ(α)^j q^{Nα}` (50 digits, `j ≤ 41`) gives
  `W(ψ^j)` periodic in `j` with period 12. The alignment `(−1)^{(j−1)/2} W(ψ^j)`, for
  `j ≡ 1, 3, 5, 7, 9, 11 (mod 12)`, is:

  | curve | j ≡ 1 | j ≡ 3 | j ≡ 5 | j ≡ 7 | j ≡ 9 | j ≡ 11 | mean |
  |---|---|---|---|---|---|---|---|
  | 27a | + | − | − | − | − | + | `−1/3` |
  | 36a | + | − | + | + | − | + | `+1/3` |

  The modes `j ≡ 3 (mod 6)` are shared and anti-aligned. Every `W = +1` case has a nonzero
  central value.
* *Mode sum.* The mode heuristic `S ≈ π(√x)(1/π)Σ_{j≤√x}(−1)^{(j−1)/2}W_j/j` gives
  `±(1/3)·√x/(2π) = ±√x/(6π)`. This is **the same constant as the lattice model**. The alignment
  `±1/3` that Bateman–Horn requires is exactly what the root numbers deliver.
* *Mode biases.* To `10^9`, the log-means of `Σ_p cos(jθ_p)/π(√x)`, `j ≤ 23`, match `W/4` to
  within `±0.04`, except `j = 13` (`+0.17`) and `j = 19` (`+0.36`) for 27a. The truncated sums
  `J ≤ 41` match their predictions to within `0.035`.

**Numerics to `10^9` [numerical].** `P` is the Bateman–Horn line model and `Q` the mode model,
both in units of `π(√x)`:

| curve | x | `S` | `S/√x` | `S/π(√x)` | `P/π(√x)` | `Q/π(√x)` | frac `S<0` | sign changes |
|---|---|---|---|---|---|---|---|---|
| 64a | 1e6 | +245 | 0.245 | 1.46 | 1.49 | 1.30 | 0 | 0 |
| 64a | 1e8 | +2420 | 0.242 | 1.97 | 1.81 | 1.67 | 0 | 0 |
| 64a | 1e9 | +8003 | 0.253 | 2.35 | 1.99 | 1.85 | 0 | 0 |
| 36a | 1e6 | +145 | 0.145 | 0.86 | 0.54 | 0.55 | 0.005 | 33 |
| 36a | 1e8 | +1207 | 0.121 | 0.98 | 0.63 | 0.67 | 0.005 | 235 |
| 36a | 1e9 | +2961 | 0.094 | 0.87 | 0.69 | 0.73 | 0.0006 | 235 |
| 27a | 1e6 | +7 | 0.007 | 0.04 | −0.55 | −0.13 | 0.61 | 377 |
| 27a | 1e8 | −147 | −0.015 | −0.12 | −0.66 | −0.26 | 0.80 | 3066 |
| 27a | 1e9 | −1349 | −0.043 | −0.40 | −0.72 | −0.32 | 0.88 | 6008 |
| 32a | 1e9 | +793 | 0.025 | 0.23 | — | — | 0.049 | 4737 |

* **64a**: `S ≥ 1` for every `x ≥ 17`; the last `x` with `S ≤ 0` is `p = 13`.
* **36a**: `S > 0` for every `x > 1.92·10^7`.
* **27a**: negative on `88%` of `x ≤ 10^9`, but `S` was still positive at `p = 958 613 347`.
* **32a**: the log-mean of `S/π(√x)` is `+0.29`, against the mode prediction `0.198`
  (`gaussian-primes.md` found `+0.31` to `10^8`): a Chebyshev-size bias, with 4737 sign changes.
* **The leading constants are far away.** The line models reach `P/√x = 0.199, 0.0685, −0.0704`
  at `10^12`, with `(P/√x − const)·log x ≈ 1.1, 0.43, −0.48`, so the approach is only
  `O(1/log x)`.
* **Second order is unresolved.** `S` sits above both `P` and `Q` for 64a and 36a, and between
  them for 27a. The two heuristics disagree with each other at order `√x/log x`, by up to
  `0.4 π(√x)`.

## 5. Blocks and consecutive digits [numerical]

| sequence | n | density | `p(L) = 2^L` for `L ≤` | `χ²/dof` (z), `L = 2, 4, 6, 8, 10` | `P(d_{k+1} = d_k)` | independent | z |
|---|---|---|---|---|---|---|---|
| 11a1 (all p) | 78498 | 0.4980 | 12 | 0.20, 0.39 (−2.0), 0.69, 0.91, 0.99 | 0.5002 | 0.5000 | +0.1 |
| 37a1 | 78498 | 0.5005 | 12 | 0.27, 1.04, 1.12, 1.05, 0.96 | 0.5022 | 0.5000 | +1.3 |
| 5077a1 | 78498 | 0.5015 | 12 | 1.29, 1.00, 0.83, 1.04, 1.02 | 0.4982 | 0.5000 | −1.0 |
| 64a (split p) | 39175 | 0.4969 | 12 | 1.89, 0.95, 1.72 (+3.4), 0.97, 1.04 | 0.4966 | 0.5000 | −1.4 |
| 36a (split p) | 39231 | 0.4982 | 12 | 0.42, 0.76, 0.97, 1.02, 1.02 | 0.4988 | 0.5000 | −0.5 |
| 27a (split p) | 39231 | 0.4999 | 12 | 0.08, 0.77, 1.14, 0.86, 0.96 | 0.4991 | 0.5000 | −0.3 |
| 64a (all p) | 78498 | 0.2480 | 6 | 61, 14, 4.3, 1.6, 0.99 | 0.6069 | 0.6270 | **−11.6** |
| 27a (all p) | 78498 | 0.2498 | 7 | 53, 13, 3.9, 1.7, 0.99 | 0.6068 | 0.6252 | **−10.6** |

(14a1, 389a1 and 32a behave like their neighbours; the script prints them.) The tests use
non-overlapping blocks against an i.i.d. Bernoulli model with the empirical density, with the
Wilson–Hilferty `z`.

* **Non-CM digits, and CM digits along the split primes, look like fair coins.** Every block of
  length `≤ 12` occurs. No consecutive-digit correlation is visible (`|z| ≤ 1.4`). One block test
  of 45 has `|z| > 3`.
* **CM digits along all primes are not fair coins, and the reason is known.** The inert primes
  carry `0`, so the sequence inherits the consecutive-prime residue correlations of
  Lemke Oliver–Soundararajan [LOS]. Consecutive primes avoid repeating `p mod 4` (resp. `mod 3`),
  so the repeat probability is `0.607` against `0.627`, at `z = −11`.
* **There is no new correlation of the angles.** This is the analogue of
  `gaussian-primes.md` §4.

## 6. Irrationality

### 6.1 `ρ_E` [open]

Suppose `ρ_E` is rational. Then `d_k` is eventually periodic. By Sato–Tate the period has mean
`½`, so `S_E(x) + #{p ≤ x : a_p = 0} = O(1)`.

* **Non-CM.** `#{a_p = 0}` is `o(π(x))` and conjecturally `≍ √x/log x` (Lang–Trotter). One would
  have to show that `S_E + Z_E` is unbounded. Through §4.2 this means controlling
  `Σ_j c_j P_j(σ)` as `σ → ½⁺`. Each `P_j` is fine, by [NT] and §4.3. But the `O_j(1)` terms are
  not uniform in `j` (the conductor is `N^j`), the series is only conditionally convergent, and
  the discreteness term of §4.4 lives at `j ≈ √p`. No current technique handles infinitely many
  `L`-functions with this uniformity; effective Sato–Tate is far too weak at scale `√x`.
* **CM.** The same obstruction arises, with infinitely many Grössencharacters
  (`gaussian-primes.md` §3). The lattice route needs primes on the line `t = 1` (36a: `1 + 3s²`
  prime) or `L = ±1` (27a), which is a Landau-type problem.

### 6.2 Congruence digits: the method transfers [proved, modulo classical inputs]

Let `G = Gal(ℚ(E[ℓ])/ℚ)`, `C ⊂ G` a union of conjugacy classes, and `d_k = [Frob_{p_k} ∈ C]`.
Expand `1_C − |C|/|G| = |G|^{−1} Σ_{ρ≠1} c_ρ χ_ρ`, with `c_ρ = Σ_{g∈C} \overline{χ_ρ(g)}` an
algebraic integer. The proof of `unions.md` §2 goes through with Artin `L`-functions in place of
Dirichlet `L`-functions:

* **Step 1 (density of the period).** If `d` is eventually periodic, its period has mean
  `|C|/|G|` by Chebotarev.
* **Step 2.** `Σ_p (d(p) − |C|/|G|) p^{−s}` stays bounded as `s → ½⁺`.
* **Step 3 (prime squares).** `Σ_p χ_ρ(Frob_p²) p^{−2s} = FS(ρ) log 1/(2s−1) + O(1)`. This needs
  `L(s, Sym²ρ)` and `L(s, Λ²ρ)` regular and nonzero at `1` apart from their trivial constituents,
  which follows from Brauer induction and Hecke. Then
  `Σ_ρ c_ρ FS(ρ) = Σ_{g∈C} #{h : h² = g} − |C| = ν(C) − |C|`, with `ν(C) = #{h ∈ G : h² ∈ C}`.
* **Step 4 (central orders).** `L(s, ρ)` is meromorphic (Brauer), so `m_ρ = ord_{s=½} L(s, ρ) ∈ ℤ`.
  Poles are allowed, since the Artin conjecture is not needed.
* **Conclusion.**

      d eventually periodic  ⇒  Σ_{ρ≠1} c_ρ m_ρ = (|C| − ν(C))/2.                       (R_G)

  The left side is an algebraic integer. So if the **defect `|C| − ν(C)` is odd**, the digit is
  not eventually periodic, and `Σ_k d_k b^{−(k+1)}` is irrational for every base `b`. This is the
  `T1` of `unions.md`, with one Artin `L`-function per irreducible character of `G` (finitely
  many).

None of this is in Mathlib: Artin `L`-functions, Brauer induction and Chebotarev are all absent.

**The defect table [proved, finite computation].** Take `G = GL₂(𝔽_ℓ)` (surjective mod-`ℓ`
image), with `G = S₃` for `ℓ = 2`:

| `ℓ` | `C` | `#C` | `ν(C)` | defect `#C − ν(C)` | parity method | bias (no central zeros) |
|---|---|---|---|---|---|---|
| 2 | `tr = 0`, i.e. `[a_p even]` = `[2 ∣ #E(𝔽_p)]` | 4 | 4 | 0 | no conclusion | 0 |
| 2 | `g = 1`, i.e. `[E(𝔽_p)[2] ≅ (ℤ/2)²]` | 1 | 4 | −3 | **irrational** | `−0.250` |
| 3 | `tr = 0` | 18 | 12 | 6 | no conclusion | `+0.063` |
| 3 | `tr = 1` / `tr = 2` | 15 | 6 / 30 | 9 / −15 | **irrational** | `+0.094` / `−0.156` |
| 3 | `[3 ∣ #E(𝔽_p)]` | 21 | 30 | −9 | **irrational** | `−0.094` |
| 5 | `tr = 0` | 100 | 120 | −20 | no conclusion | `−0.021` |
| 5 | `tr = ±1` / `tr = ±2` | 95 | 60 / 120 | 35 / −25 | **irrational** | `+0.036` / `−0.026` |
| 5 | `[5 ∣ #E(𝔽_p)]` | 115 | 200 | −85 | **irrational** | `−0.089` |
| 7 | `tr = 0` | 294 | 252 | 42 | no conclusion | `+0.010` |
| 7 | `tr = t ≠ 0` | 287 | 238 or 350 | 49 or −63 | **irrational** | |
| 7 | `[7 ∣ #E(𝔽_p)]` | 329 | 602 | −273 | **irrational** | `−0.068` |
| `ℓ ≤ 7` | `g = 1` (`p` splits completely in `ℚ(E[ℓ])`) | 1 | `1 + #inv` = 4, 14, 32, 58 | `−#inv`, odd | **irrational** | `−0.25, −0.135, −0.032, −0.014` |

So the digits `[a_p ≡ t (mod ℓ)]` with `t ≢ 0`, `[ℓ | #E(𝔽_p)]` for `ℓ = 3, 5, 7`, and the
complete-splitting digits are **not eventually periodic for 37a1, 389a1 and 5077a1**. This assumes,
as the LMFDB records, that their mod-`ℓ` images are all of `GL₂(𝔽_ℓ)`; the densities for
`ℓ = 2, 3, 5` agree below. No hypothesis on zeros is needed, only the classical theory of Artin
`L`-functions.

**`[a_p ≡ 0 (mod 2)]` has defect 0.** On `C = {1, transpositions}`, `c_ε = −2` and
`c_{ρ₂} = 2`, so (R_G) reads `ord_{½} L(s, χ_D) = ord_{½} L(s, ρ₂)`. Here `χ_D` is the quadratic
character of `ℚ(√Δ_E)`, and `L(s, ρ₂) = ζ_K/ζ` for the cubic field `K` of the 2-division points.
Periodicity is excluded only if exactly one of these vanishes at `½`. With nonvanishing central
values (Chowla-type) nothing follows. This is the `ν(A) = |A|` situation of `unions.md`.

The densities are worth correcting: `[a_p even]` has density `2/3` (`G = S₃`), `1/3`
(`G = C₃`), or `1` (a rational 2-torsion point: 14a1, 64a, 32a, 36a). The value `1/2` does not
occur.

**[numerical]** For `p > 7` of good reduction, `x ≤ 10^6`:

| curve | digit | density obs. | `#C/#G` | log-mean bias | predicted |
|---|---|---|---|---|---|
| 11a1 | `[a_p even]` | 0.6671 | 0.6667 | −0.015 | 0 |
| 11a1 | `[E(𝔽_p)[2] full]` | 0.1664 | 0.1667 | −0.280 | −0.250 |
| 37a1 | `[a_p even]` | 0.6665 | 0.6667 | +0.013 | 0 |
| 37a1 | `[E(𝔽_p)[2] full]` | 0.1661 | 0.1667 | −0.304 | −0.250 |
| 389a1 | `[E(𝔽_p)[2] full]` | 0.1660 | 0.1667 | −0.297 | −0.250 |
| 5077a1 | `[E(𝔽_p)[2] full]` | 0.1655 | 0.1667 | −0.275 | −0.250 |
| 27a | `[a_p even]` | 0.6662 | 0.6667 | −0.022 | 0 |
| 37a1 | `[a_p ≡ 0 (3)]`, `[3 ∣ #E]` | 0.3768, 0.4377 | 0.3750, 0.4375 | +0.11, −0.21 | +0.06, −0.09 |
| 37a1 | `[a_p ≡ 0 (5)]`, `[5 ∣ #E]` | 0.2094, 0.2388 | 0.2083, 0.2396 | +0.33, −0.47 | −0.02, −0.09 |

* **`ℓ = 2` matches.** The prime-square bias `−¼π(√x)` of the complete-splitting digit appears on
  all four non-CM curves, and `[a_p even]` is unbiased.
* **`ℓ = 3, 5` is only consistent with noise.** The densities agree, but the biases are swamped:
  `GL₂(𝔽_ℓ)` has characters of large conductor, and 389a1 and 5077a1 scatter by `±0.4`.

## 7. Conjectures

**Conjecture A (64a; `gaussian-primes.md`).** `S_{64a}(x) ~ √x/(2π)`, and `S_{64a}(x) > 0` for
all `x ≥ 17`. Checked to `10^9`.

**Conjecture B (the Eisenstein curves).** For primes `p ≡ 1 (mod 3)`, write `p = t² + 3s²` with
`t ≡ 1 (mod 3)`, and `4p = L² + 27M²` with `L ≡ 2 (mod 3)`. Then

    Σ_{p ≤ x} sgn t_p ~ +√x/(6π),        Σ_{p ≤ x} sgn L_p ~ −√x/(6π).

That is, `S_{36a}(x) ~ √x/(6π)` and `S_{27a}(x) ~ −√x/(6π)`. Moreover
`(log x/√x)(S − (±√x/(6π)))` has a limiting logarithmic distribution. Consequently `S_{36a} > 0`
and `S_{27a} < 0` for all large `x`.

* *Evidence:* the lattice model with the exact identity `H₃·3K'' = 2√3/π`; the mode model with the
  computed root numbers (mean alignment exactly `±1/3`); mode biases to `10^9`.
* *Against, at this range:* `S_{27a}` still changes sign near `10^9`, at only `0.4π(√x)` below
  zero.

**Conjecture C (non-CM, semistable).** Assume:

* GRH and linear independence for the zeros of all `L(s, Sym^j E)`;
* minimal vanishing `r_j = (1 − W_j)/2` for `j ≥ 3`;
* enough uniformity in `j` to sum the modes.

Then `(log x/√x) S_E(x)` has a limiting logarithmic distribution with mean `2(B_E + Δ_E)`, where:

* `B_E = (8/(3π))(½ − r_E) + ½W(E)R`, with `R = −0.381582`;
* `Δ_E = μ̄/π`, the torsion term of §4.4, which is heuristic even granting the rest.

In particular, for semistable `E` without rational torsion of order `≥ 3`, the race favours
`a_p > 0` (`B > 0`) iff the rank is `0`, and the mean decreases by `16/(3π) = 1.70` per unit of
rank in units of `√x/log x`.

**Status of each statement.**

* **Proved here** (elementary, or given the cited theorems): the expansion §4.2 and its
  coefficients; the prime-square sign `−1` per odd mode (given [NT]); the identities
  `HK = 4/π` and `H₃·3K'' = 2√3/π`; the defect table and the criterion (R_G) (modulo the
  classical theory of Artin `L`-functions); that `[a_p < 0]` is not a function of `p mod N`; the
  values of `ρ_E` (exact enclosures).
* **Literature:** Sato–Tate [CHT, HSBT, T, BGHT]; automorphy of `Sym^j` [NT]; Hecke, Deuring; the
  classical CM formulas [IR]; Chebotarev; Brauer.
* **Heuristic:** every bias constant (`B_E`, `Δ_E`, `±1/(6π)`, `1/(2π)`), the root-number formula
  for `Sym^j` beyond `j = 3` (a derivation from standard local factors, not checked numerically),
  the summation over modes, and Conjectures A–C.
* **Limits of the numerics.**
  * For non-CM curves the biases are `O(π(√x))`, with `π(10^3) = 168`. That is the same order as
    the zero-driven fluctuations and conductor effects: per-curve scatter about `±0.5 π(√x)`, and
    rank-0 twists overshoot by `+0.5`. Only the rank dependence and the `j = 1` coefficient are
    clearly confirmed at `10^6`.
  * For CM curves even `10^9` is far from the leading constants: the corrections are
    `O(√x/log x)`, about `40%` at `10^9`.

## References

* [BGHT] T. Barnet-Lamb, D. Geraghty, M. Harris, R. Taylor, *A family of Calabi–Yau varieties and
  potential automorphy II*, Publ. RIMS 47 (2011).
* [CHT] L. Clozel, M. Harris, R. Taylor, *Automorphy for some l-adic lifts of automorphic mod l
  Galois representations*, Publ. IHÉS 108 (2008).
* [HSBT] M. Harris, N. Shepherd-Barron, R. Taylor, *A family of Calabi–Yau varieties and potential
  automorphy*, Ann. of Math. 171 (2010).
* [T] R. Taylor, *Automorphy for some l-adic lifts of automorphic mod l Galois representations
  II*, Publ. IHÉS 108 (2008).
* [De] L. Devin, *Discrepancies in the distribution of Gaussian primes*, Math. Z. 312 (2026).
* [Se] J.-P. Serre, *Quelques applications du théorème de densité de Chebotarev*, Publ. IHÉS 54
  (1981).
* [El] N. Elkies, *The existence of infinitely many supersingular primes for every elliptic curve
  over ℚ*, Invent. Math. 89 (1987).
* [Fi] D. Fiorilli, *Elliptic curves of unbounded rank and Chebyshev's bias*, IMRN 2014.
* [IR] K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, ch. 18.
* [LOS] R. Lemke Oliver, K. Soundararajan, *Unexpected biases in the distribution of consecutive
  primes*, PNAS 113 (2016).
* [LT] S. Lang, H. Trotter, *Frobenius distributions in GL₂-extensions*, LNM 504 (1976).
* [Ma] B. Mazur, *Finding meaning in error terms*, Bull. AMS 45 (2008).
* [NT] J. Newton, J. Thorne, *Symmetric power functoriality for holomorphic modular forms* I, II,
  Publ. IHÉS 134 (2021).
* [RS] M. Rubinstein, P. Sarnak, *Chebyshev's bias*, Experiment. Math. 3 (1994).
* [Sa] P. Sarnak, letter to B. Mazur on Chebyshev's bias (2007).
