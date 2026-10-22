# The Gaussian Rokicki digit: identification, bias of order `√x`, what a proof would need

**Status.** This note is research, with no Lean. It belongs to Direction 4 of `PROGRAM.md`
(sequences.md, row 5). Each claim carries one of three labels:

* **[proved]**: a complete argument is given here, or it is a classical theorem;
* **[numerical]**: checked by `python3 scripts/gaussian_primes.py` (all primes below `10^8`,
  about 30 s);
* **[heuristic]**: a conjecture, with its derivation.

The note corrects the explanation of the bias in `sequences.md` §2.2 and §3.3; see §5.

**Notation.**

* Every prime `p ≡ 1 (mod 4)` is uniquely `p = a² + b²` with `a` odd, `b` even, `a, b > 0`.
* The digit is `d_p = [a ≡ 3 (mod 4)]`, so `1 − 2d_p = χ₄(a_p)`.
* The primary generator is `π₀ = ε(a + bi) ≡ 1 (mod 2+2i)`, where `ε = ±1` is fixed by
  `ε(a + b) ≡ 1 (mod 4)`. Its angle is `θ_p = arg π₀`.
* `λ(𝔭) = π₀/|π₀|` is the basic Grössencharacter, of conductor `(1+i)³`.
* `χ₈(p) = (2/p)`; for `p ≡ 1 mod 4`, `χ₈(p) = +1` iff `p ≡ 1 (mod 8)`.
* The sums are
  * `S(x) = Σ_{p≤x, p≡1(4)} χ₄(a_p)`;
  * `C(x) = Σ χ₈(p)` (the control);
  * `U(x) = Σ sgn Re π₀`.

## 1. What the digit is

**Proposition 1 [proved].** For every prime `p ≡ 1 (mod 4)`,

    χ₄(a_p) = χ₈(p) · sgn(Re π₀) = χ₈(p) · sgn(cos θ_p).

*Proof.* Write `Re π₀ = εa`. From `ε(a + b) ≡ 1 (mod 4)` and `b` even, `εa ≡ 1 − b (mod 4)`. So
`χ₄(εa) = +1` iff `4 | b`, iff `p ≡ 1 (mod 8)`: here `a² ≡ 1 (mod 8)`, and `b² ≡ 0` or `4 (mod 16)`
according as `4 | b` or not. Hence `χ₄(Re π₀) = χ₈(p)`, and

    χ₄(a) = χ₄(ε) χ₄(εa) = sgn(Re π₀) χ₈(p),

since `a > 0`. ∎ (Checked for all `2 880 504` primes below `10^8`.)

**What is finite-order and what is not.**

* On generators, the function `α ↦ χ₄(Re α)` (with `Re α` odd) is a function of `α mod 4`.
* It is odd under `α ↦ −α`, so it is not a function of the ideal `(α)`.
* The two normalizations that make it one do different things:
  * The congruence normalization `π₀ ≡ 1 mod (2+2i)` turns `χ₄(Re π₀)` into the ray class
    character `χ₈∘N` modulo `4 = (1+i)⁴`. This is the unique nontrivial character of the ray class
    group mod `4`, which has order `8/4 = 2`, so it is a Dirichlet character in disguise.
  * The archimedean normalization `a > 0` picks one of `±π₀` by a half-plane condition.

The digit is the product of the two. All of its non-Dirichlet content sits in the half-plane
sign `sgn Re π₀`.

**Proposition 2 [proved].** No function of a ray class agrees with `χ₄(a_p)`. Precisely: there is
no modulus `𝔪` of `ℤ[i]`, no finite set of ray class characters `ψ` mod `𝔪`, and no constants `c_ψ`
with

    d_p = ½(1 − Σ c_ψ ψ(𝔭))

on a set of split primes of relative density `1`. In particular `d_p` is not a function of
`p mod N` for any `N`.

*Proof.* Enlarge `𝔪` to `(m)` with `m ∈ ℤ` and `4 | m`.

* The four units are distinct mod `(2+2i)`, so the ray class of `𝔭` mod `m` determines `π₀ mod m`,
  and with it `χ₈(p)`. Conversely, `π₀ mod m` determines the class.
* Suppose the identity held. Then `sgn Re π₀` would be a function of `π₀ mod m` off a density-zero
  set.
* By Hecke [He1, He2], the characters `ψλ^j` (`ψ` mod `m`, `j ≠ 0`) are nontrivial
  Grössencharacters. Their `L`-functions do not vanish on `Re s = 1`.
* So within each residue class `π₀ ≡ r (mod m)` the angles `θ_p` are equidistributed (Weyl's
  criterion), and each half-plane gets relative density `½`. Contradiction.
* Since `p mod N` is a function of the ray class mod `N` (through the norm), the last claim
  follows. ∎

Numerically the fraction of `a ≡ 3 (mod 4)` lies in `[0.497, 0.502]` in every class
`p mod N`, `N = 8, 16, 32, 64, 128` [numerical].

**The signed residue is Dirichlet, the sign is not [proved].** The supplementary law of quartic
reciprocity gives `(i/π₀)₄ = i^{−(Re π₀ − 1)/2}`. Since `(i/π₀)₄ = i^{(p−1)/4}`, this means

    Re π₀ ≡ (3 − p)/2 (mod 8).

So `p mod 16` fixes the *signed* `Re π₀ mod 8`: `1, 7, 5, 3` for `p ≡ 1, 5, 9, 13 (mod 16)`
(checked for all `p < 10^8`). But `a = |Re π₀|` loses exactly the sign. Gauss's criterion is of a
different kind: `2` is a quartic residue mod `p` iff `p = x² + 64y²`, i.e. iff `8 | b` [Ga]
(checked for the `19 552` primes `p ≡ 1 mod 8` below `10^6`). That is the finite-order Hecke digit
of `sequences.md` row 4, not this one.

**Fourier expansion [proved].** `cos θ_p ≠ 0` always, and the Fourier series of `sgn cos` converges
pointwise off `±π/2`. Hence

    d_p = ½ − (2/π) Σ_{j odd ≥ 1} ((−1)^{(j−1)/2}/j) · Re (λ^j χ₈)(𝔭),

with `𝔭` either prime above `p`. The two give complex-conjugate values, so the digit is a function
of `p`. This is an infinite combination of infinite-order Grössencharacters `λ^j χ₈`, `j` odd.

**Elliptic curves [proved / numerical].** For `E_D : y² = x³ + Dx`, `|a_p(E_D)| = 2a`
([IR] Ch. 18 §4; checked for `p < 4000`), and:

* `sgn a_p(y² = x³ + x) = sgn a_p(y² = x³ − 4x) = χ₄(a_p)`;
* `sgn a_p(y² = x³ − x) = sgn a_p(y² = x³ + 4x) = sgn Re π₀`.

So the Gaussian Rokicki digit is `d_p = [a_p(E) < 0]` for the conductor-`64` CM curve
`E : y² = x³ + x`, read along the primes `p ≡ 1 (mod 4)` (for `p ≡ 3 (mod 4)`, `a_p = 0`). Its
`L`-function is `L(s, λχ₈)`; the Fricke test in §3 finds level `64`. The digit `sgn Re π₀` is the
same thing for the conductor-`32` curve `y² = x³ − x`. This is the "sign of `a_p`" race of Mazur
and Sarnak [Ma, Sa] for a CM curve. In the form `p = a² + 4b²` it is exactly the race `D₂` of
Devin [De].

## 2. The bias: two heuristics, one constant

### 2.1 Hecke modes: inert primes and root numbers [heuristic, standard]

Take `ψ_j = λ^j χ₈`, `j` odd. Near `s = ½`, for real `s > ½`, write

    log L(s, ψ_j) = P_j(s) + c · log 1/(2s−1) + hol,     P_j(s) = Σ_{𝔭 split} ψ_j(𝔭) N𝔭^{−s}.

* **The `m = 2` terms of split primes** carry `ψ_j(𝔭)² = λ^{2j}(𝔭)`, a nontrivial
  Grössencharacter. They give `½ log L(2s, λ^{2j}) + hol`, which is holomorphic and nonzero near
  `s = ½`, so they contribute nothing to `c`.
* **The inert primes** `p ≡ 3 (mod 4)` have norm `p²` and primary generator `−p`, so
  `ψ_j((p)) = (−1)^j χ₈(p²) = −1`. Their `m = 1` terms give `−Σ_{p≡3(4)} p^{−2s}`, so
  `c = −½`. This is `sequences.md` §3.4.
* **The ramified prime** `(1+i)` divides the conductor and does not occur.

This is the "prime-square" term of the project. For a quadratic Dirichlet character `c = +½`
(`χ(p)² = 1`), which gives a negative bias. Here the norm-`p²` term has the value `−1`, so the sign
flips.

If `L(s, ψ_j)` vanishes to order `r_j` at `½`, then `P_j(s) ~ (½ − r_j) log 1/(2s−1)`. By the
explicit formula (Rubinstein–Sarnak [RS]), the mean bias of the mode is

    Σ_{p≤x} χ₈(p) cos(jθ_p)  ≈  (1 − 2r_j) · π(√x)/4.

(The two ideals above `p` each contribute half.)

**Root numbers [numerical].** `scripts/gaussian_primes.py` builds the CM forms
`f_j = Σ_{α primary} ψ(α) α^j q^{Nα}` (weight `j+1`). It finds their level and the sign `W` of the
functional equation from the Fricke relation `φ(1/(Ny)) = W N^{w/2} y^w φ(y)`, tested at two
points to 80 digits. For `j ≤ 41` the results are:

* `L(s, λ^j)` has level `32` and `W(λ^j) = (−2/j)`.
* `L(s, λ^j χ₈)` has level `64` and `W(λ^j χ₈) = χ₄(j)`.
* Every case with `W = +1` has a nonzero central value.

So `r_j = (1 − χ₄(j))/2`, presumably a simple zero when `W = −1`, and the mode bias is
`χ₄(j) π(√x)/4`. The log-means over `x ∈ [10^5, 10^8]` match:

| j | 1 | 3 | 5 | 7 | 9 | 11 | 13 | 15 |
|---|---|---|---|---|---|---|---|---|
| observed `⟨M_j/π(√x)⟩` | +0.26 | −0.28 | +0.28 | −0.26 | +0.16 | −0.26 | +0.20 | −0.32 |
| predicted `χ₄(j)/4` | +0.25 | −0.25 | +0.25 | −0.25 | +0.25 | −0.25 | +0.25 | −0.25 |

The untwisted modes `N_j = Σ cos(jθ_p)` match `(−2/j)/4` in the same way.

**Summing the modes.** The Fourier coefficient of mode `j` is `(4/π)χ₄(j)/j`, and its bias is
`χ₄(j)/4`. The product is `+1/(πj)` for **every** odd `j`, so the root numbers line the biases up
with the coefficients. The formal series `(1/π) Σ 1/j` diverges, which matches the "infinite mean"
of Devin [De]. The angular resolution of primes up to `x` is about `1/√x`, so cut the series at
`j ≈ √x`:

    S(x) ≈ π(√x) · (1/π) Σ_{j odd ≤ √x} 1/j ≈ (2√x/log x) · (1/π) · (log x)/4 = √x/(2π).

The truncated Fourier sums confirm the root-number-corrected prediction. The table shows the
log-mean of `Σ_p χ₈(p) f_J(θ_p)/π(√x)`, with `f_J` the partial Fourier sum of `sgn cos`:

| J | 1 | 3 | 9 | 31 | 101 | 301 | 1001 |
|---|---|---|---|---|---|---|---|
| observed | 0.331 | 0.451 | 0.592 | 0.801 | 0.933 | 1.122 | 1.292 |
| `(1/π)Σ_{j≤J} 1/j` (with `W`) | 0.318 | 0.424 | 0.569 | 0.754 | 0.938 | 1.111 | 1.302 |
| without central zeros | 0.318 | 0.212 | 0.266 | 0.245 | 0.252 | 0.251 | 0.250 |

The inert-prime term alone (no central zeros) predicts `+π(√x)/4`: `112` at `10^7`, against the
observed `704`. With the root numbers the prediction is `Q(x)`, given in the table of §2.3.

### 2.2 The lattice: Bateman–Horn on every line `a = const` [heuristic]

Fix odd `a` and count the primes `a² + 4c²`, `c ≥ 1`. Bateman–Horn [BH] predicts the density
`H·w(a)/log(a² + 4c²)`, where:

* `H = 2 Π_{q odd}(1 − χ₄(q)/(q−1)) = 2.745627…`, twice the Hardy–Littlewood constant
  `1.3728135…` of `n² + 1`;
* `w(a) = Π_{q | a} (q−1)/(q−1−χ₄(q))`, which is `> 1` for `q ≡ 1 (mod 4)` and `< 1` for
  `q ≡ 3 (mod 4)`.

The correction `w(a)` arises because `a² + 4c² ≡ 4c² (mod q)` has one root when `q | a`, against
`1 + χ₄(q)` roots otherwise.

So `g(a) = χ₄(a) w(a)` is biased. Write `g = Σ_{d | a} u(d) χ₄(a/d)` with `u(q) = χ₄(q)(w(q) − 1)`,
so that `u(q) = 1/(q−2)` or `1/q`. Since `Σ_{m ≤ M, m odd} χ₄(m) ∈ {0, 1}` has mean `½`,

    Σ_{a ≤ A, a odd} g(a) ~ (K/2) log A,     K = ½ Π_{q odd} (1 + u(q))(1 − 1/q) = 0.463734… .

Summing the lines up to `a ≤ √x`, with `√(x − a²)/2` values of `c` on each line:

    P(x) := Σ_a χ₄(a) H w(a) Σ_c 1/log(a²+4c²) ~ (H/(2 log x)) · √x · (K/2) log √x = (HK/8) √x.

**The constant is exactly `1/(2π)` [proved, algebra].** At every odd prime `q`, the local factors
of `H/(4/π)` and of `2K` multiply to `1`:

* `q ≡ 1`: `[q(q−2)/(q−1)²] · [(q−1)²/(q(q−2))] = 1`;
* `q ≡ 3`: `[q²/(q²−1)] · [(q²−1)/q²] = 1`.

Here `Π(1 − χ₄(q)/q) = 1/L(1, χ₄) = 4/π`. Hence `HK = 4/π` and `HK/8 = 1/(2π)`.

The two heuristics are independent, one through the zeros and root numbers of infinitely many Hecke
`L`-functions and one through local densities of primes on lines. They give the same leading
constant:

    S(x) ~ √x/(2π).                                        (Conjecture)

The bias is therefore **of order `√x`**, a factor `log x` larger than any Chebyshev bias
(`≍ √x/log x`). This is why `S(x)/π(√x)` keeps growing.

### 2.3 Numerics (all primes `p ≡ 1 mod 4` below `10^8`)

Here `P(x)` is the exact Bateman–Horn line sum, and `Q(x) = π(√x)(1/π)Σ_{j odd ≤ √x} 1/j` is the
mode sum.

| x | #p | S(x) | π(√x) | S/π(√x) | S/√x | P(x) | S − P | Q(x) |
|---|---|---|---|---|---|---|---|---|
| 10^5 | 4 783 | +83 | 65 | 1.28 | 0.263 | 85.3 | −2.3 | 73 |
| 10^6 | 39 175 | +245 | 168 | 1.46 | 0.245 | 250.0 | −5.0 | 219 |
| 10^7 | 332 180 | +704 | 446 | 1.58 | 0.223 | 741.3 | −37.3 | 662 |
| 1.5·10^7 | 485 274 | +920 | 536 | 1.72 | 0.238 | 892.9 | +27.1 | 813 |
| 10^8 | 2 880 504 | +2420 | 1229 | 1.97 | 0.242 | 2217.8 | +202.2 | 2050 |

* **No sign change.** `S(n) ≥ 0` for every prefix up to `10^8`; the minimum is `0`, at `p = 13`.
  This agrees with Devin's data to `5·10^9` [De].
* **The residual.** `|S − P| ≤ 0.17 π(√x)`, the size of the expected zero-driven fluctuation. The
  data cannot tell whether an additional `+π(√x)/4`-type term exists beyond `P`. Both heuristics
  are uncertain at order `√x/log x`.
* **Approach to the constant.** Beyond the sieve range, the Bateman–Horn sum (integral form) gives
  `P(x)/√x = 0.2218, 0.2082, 0.1992, 0.1931` at `x = 10^8, 10^10, 10^12, 10^14`. Moreover
  `(P/√x − 1/(2π)) log x ≈ 1.15, 1.13, 1.11, 1.09`, so `P(x) = √x/(2π) + (1.1 + o(1)) √x/log x`.
  The observed `S/√x ≈ 0.24` is the start of this slow approach.
* **Single lines.** Bateman–Horn works line by line: for `a = 1, 3, 5, 7, 9` at `10^8`, there are
  `840, 544, 1123, 752, 568` primes, against the predictions `855, 570, 1139, 732, 569`.

**Removing the small-`a` lines (test (c)).** The table shows `S_{a>A₀}(x)`, with the
Bateman–Horn prediction in parentheses:

| A₀ | 10^6 | 10^7 | 1.5·10^7 | 10^8 |
|---|---|---|---|---|
| 1 | +134 (128) | +389 (423) | +547 (515) | +1580 (1362) |
| 3 | +214 (209) | +599 (635) | +794 (766) | +2124 (1932) |
| 9 | +81 (71) | +261 (273) | +389 (336) | +1185 (956) |
| 25 | +43 (29) | +176 (160) | +295 (202) | +838 (650) |
| 99 | +99 (89) | +399 (321) | +562 (394) | +1335 (1088) |

The bias persists and grows for every `A₀`. Removing lines only shifts it by the partial sum
`Σ_{a ≤ A₀}`, which alternates with `A₀ mod 4`, as Bateman–Horn predicts. Sign changes: `99` with
`a = 1` removed (last negative at `p = 459 841`), and `481` with `a ≤ 9` removed (last at
`5.33·10^6`); none for the full sum.

**The partial sums over lines `T(A) = Σ_{p ≤ 10^8, a ≤ A} χ₄(a_p)`** oscillate with `A` and drift
upward:

| A | 1 | 3 | 5 | 31 | 255 | 1023 | 4095 | all |
|---|---|---|---|---|---|---|---|---|
| T(A) | 840 | 296 | 1419 | 1046 | 948 | 2153 | 1895 | 2420 |

The bias is spread over all scales of `a`, not concentrated at `a = 1`.

### 2.4 Control and untwisted digit

| x | C(x) = Σ χ₈(p) | C/π(√x) | U(x) = Σ sgn Re π₀ | U/π(√x) |
|---|---|---|---|---|
| 10^5 | −15 | −0.23 | +37 | +0.57 |
| 10^6 | −71 | −0.42 | +51 | +0.30 |
| 10^7 | −228 | −0.51 | −72 | −0.16 |
| 1.5·10^7 | −308 | −0.57 | +282 | +0.53 |
| 10^8 | −564 | −0.46 | +284 | +0.23 |

**Control `[b ≡ 2 mod 4] = [p ≡ 5 mod 8]` [numerical; RS].**
`C = ½Σ_p ((2/p) + (−2/p))`, so the prediction is `−π(√x)/2`. The log-mean is `−0.52`. `C < 0`
at every prefix below `10^8`, with no sign change. This is the ordinary Chebyshev sign, consistent
with the known first crossing of the `8;1` versus `8;5` race near `5.9·10^8` (Bays–Hudson).

**Untwisted `sgn Re π₀` (the curve `y² = x³ − x`).**

* Lattice model: along each line the sign `(−1)^{b/2}` alternates, so there is no `√x` term.
* Mode model: the coefficients times the biases give
  `(1/π) Σ (2/j)/j = (1/π) L(1, (2/·)) = (1/π) · log(1+√2)/√2 = 0.198`, a finite sum. This is a
  Chebyshev-size positive bias.
* Observed: log-mean `+0.31`, `2099` sign changes, negative `10%` of the time.

So it is weakly biased, not unbiased. The single value `−72` at `10^7` quoted in `sequences.md` is
a downward excursion.

## 3. Irrationality of the Gaussian Rokicki constant `Σ_k d_{p_k} 2^{−k}`

**The method, mode by mode [proved, modulo the analytic input].** The project's argument
transfers to one Grössencharacter `ψ_j = λ^j χ₈`:

1. Suppose `Σ_{N𝔭 ≤ x} ψ_j(𝔭)` stays bounded.
2. Then `P_j(σ)` stays bounded as `σ → ½⁺`.
3. But `log L(σ, ψ_j) − P_j(σ) = −½ log 1/(2σ−1) + O(1)`, from the inert primes, and
   `log L(σ, ψ_j) = r_j log(2σ−1) + O(1)` for the (finite) order `r_j`.
4. So `P_j(σ) = (½ − r_j) log 1/(2σ−1) + O(1)`, which is unbounded because `½ − r_j ≠ 0` for every
   integer `r_j`.

Steps 2–4 need:

* the Euler product of `L(s, ψ_j)` over the prime ideals of `ℤ[i]`;
* analytic continuation to a neighborhood of `[½, 1]` (Hecke: `L(s, ψ_j)` is entire);
* the inert/split decomposition of rational primes in `ℤ[i]`.

Nonvanishing on `(½, 1]` follows automatically, as in the Dirichlet case.

**The digit [open].** The digit is not a finite combination (Prop. 2) and not a Dirichlet digit.
So the theorems already proved here (single class, quadratic, residue constants) do not apply. An
eventually periodic digit sequence would make `S(n)` bounded, hence
`D(σ) = Σ χ₄(a_p) p^{−σ}` bounded as `σ → ½⁺`. Heuristically `D` even has a pole: from
`S ~ √x/(2π)`, `D(σ) ~ 1/(4π(σ − ½))`. Proving that `D` is unbounded needs one of two routes:

* **Through the modes:**
  * `L(½, λ^j χ₈) ≠ 0` for all `j ≡ 1 (mod 4)`, and simple zeros for `j ≡ 3 (mod 4)`. Both are
    open in general; the cases `j ≤ 41` are checked here.
  * Uniform control in `j` of the `O(1)` terms. The series over `j` is only conditionally
    convergent (indeed log-divergent). This is beyond current technology: Devin [De] needs GRH and
    summability hypotheses, and even then gets an infinite mean, not a theorem.
* **Through the lattice:** primes on the line `a = 1`, i.e. `1 + 4c²` prime infinitely often. That
  is Landau's fourth problem.

We know no proof that the Gaussian Rokicki constant is irrational. Gaussian primes with **this**
digit are not a case of verbatim transfer. The verbatim Hecke case remains `sequences.md` row 4
(the quartic character of `2`, finite order, `L = ζ_{K(2^{1/4})}/ζ_K`).

**Mathlib today** (grep of `.lake/packages/mathlib`).

*Present:*

* `NumberField.dedekindZeta`, defined as an `LSeries` of ideal counts by `Ideal.absNorm`, with
  `dedekindZeta_residue`, `dedekindZeta_residue_pos` and `tendsto_sub_one_mul_dedekindZeta_nhdsGT`
  (the residue at `1`). There is no Euler product and no continuation.
* `ClassGroup`, `NumberField.AdeleRing` (restricted products).
* `GaussianInt` (`ℤ[i]`, `toComplex`, `sq_add_sq_of_nat_prime_of_not_irreducible`) and
  `Nat.Prime.sq_add_sq`.
* `ZMod.χ₄`, `ZMod.χ₈`.
* Dirichlet `L`-functions with continuation and nonvanishing on `Re s ≥ 1` (`LSeries/`).
* `ModularForm.L` / `ModularForm.Λ`, with `differentiable_L` for cusp forms: the `L`-function of a
  cusp form is entire.

*Absent:*

* Ray class groups and ray class characters, Grössencharacters, Hecke `L`-functions (Euler product,
  continuation, functional equation, root numbers), Hecke's equidistribution of angles.
* The factorization `ζ_{ℚ(i)} = ζ · L(·, χ₄)`.
* Theta series with harmonic polynomials as modular forms of level `Γ₁(32)`/`Γ₁(64)`.
* Hecke operators and Euler products of eigenform `L`-series.

The cheapest formal route to a single mode is to build `f_j` as a cusp form and use
`ModularForm.differentiable_L` for the continuation. That leaves modularity of the theta series and
the Euler product to be proved: several thousand lines, and it still gives only one mode.

## 4. Equidistribution and normality

* **Density [proved].** By Hecke's theorem the digit has density `½`: the angles `θ_p` are
  equidistributed jointly with ray classes, and the half-plane `Re π₀ > 0` has measure `½` in each
  class mod `8`.
* **Narrow sectors [literature].** Kubilius [Ku] and later work count Gaussian primes in shrinking
  sectors; Rudnick–Waxman [RW] study the variance.
* **Consecutive digits [literature].** Nothing is known about consecutive-prime patterns of the
  digit. There is no analogue of the Lemke Oliver–Soundararajan theory for angles of consecutive
  Gaussian primes, and normality of the constant is open.
* **Consecutive digits [numerical].** Pairs `(d_k, d_{k+1})` below `10^8` deviate from
  independence by `z = ±0.16`. Blocks of length 3 and 4 give `χ² = 8.0` (7 d.o.f.) and `17.8`
  (15 d.o.f.). No local correlation is visible.
* **Primes with prime real part.** Fouvry–Iwaniec [FI] prove infinitely many primes `a² + b²` with
  `a` prime. This is a thin-set result of the same lattice type, but it gives no information on
  `a mod 4` biases.

## 5. Verdict on `sequences.md`

That note says, in §2.2 and §3.3, that the positive bias of row 5 is "a lattice-point effect from
small `a`, not an `L`-function effect", and that `sgn Re π` is unbiased. Corrections:

1. **Not from small `a`.** Removing the lines `a ≤ A₀` for any `A₀ ≤ 99` leaves the bias positive
   and growing. At `10^8`, `+1335` remains with `a ≤ 99` removed. The `a = 1` line (`+315` at
   `10^7`) is only the first term of a series `Σ χ₄(a) w(a)` whose partial sums grow like
   `(K/2) log A`.
2. **It is also an `L`-function effect, of a new kind.** In Hecke language the bias is the
   inert-prime (norm `p²`) term of every mode, with sign `+`, opposite to the Dirichlet
   prime-square term. The root numbers `W(λ^jχ₈) = χ₄(j)` flip half the modes so that every mode
   pushes in the same direction. The sum over modes then diverges logarithmically.
3. **The lattice and Hecke pictures are one phenomenon.** Both give `S(x) ~ √x/(2π)`, and the
   constants agree exactly (`HK = 4/π`). The bias is of order `√x`, not `√x/log x`.
4. **`sgn Re π₀` is weakly biased.** It has a Chebyshev-size positive bias of about
   `0.2 π(√x)` (log-mean `0.31`), with `2099` sign changes below `10^8`.

**Prior work.** The positive bias itself is Devin's Conjecture 1.2 [De]: a "complete bias" of `D₂`
with infinite mean in the `log x/√x` normalization, supported by data to `5·10^9`. What is new
here, all heuristic and numerical:

* the explicit rate `√x/(2π)`;
* its derivation by Bateman–Horn on lines, with the exact identity `HK = 4/π`;
* the cut-off mode sum `(1/π)Σ_{j≤√x} 1/j`;
* the root-number tables;
* the removal and control tests.

## References

* [BH] P. Bateman, R. Horn, *A heuristic asymptotic formula concerning the distribution of prime
  numbers*, Math. Comp. 16 (1962).
* [De] L. Devin, *Discrepancies in the distribution of Gaussian primes*, Math. Z. 312 (2026),
  arXiv:2105.02492.
* [FI] É. Fouvry, H. Iwaniec, *Gaussian primes*, Acta Arith. 79 (1997).
* [Ga] C. F. Gauss, *Theoria residuorum biquadraticorum I* (1828).
* [He1, He2] E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der
  Primzahlen*, Math. Z. 1 (1918), 6 (1920).
* [IR] K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 18.
* [Ku] J. Kubilius, *On some problems of the geometry of prime numbers*, Mat. Sb. 31 (1952).
* [Ma] B. Mazur, *Finding meaning in error terms*, Bull. AMS 45 (2008).
* [RS] M. Rubinstein, P. Sarnak, *Chebyshev's bias*, Experiment. Math. 3 (1994).
* [RW] Z. Rudnick, E. Waxman, *Angles of Gaussian primes*, Israel J. Math. 232 (2019).
* [Sa] P. Sarnak, letter to B. Mazur on Chebyshev's bias for `a_p` (2007).
