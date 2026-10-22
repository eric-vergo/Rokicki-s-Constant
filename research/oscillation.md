# Quantitative oscillation: `Σ χ(p)` is `Ω(x^{1/2-ε})`

**Status.** Proved and formalized (`RokickiConstant/General/Oscillation.lean`, no `sorry`). This
is Direction 2 of `PROGRAM.md`. The numerical table in §6 is reproduced by
`python3 scripts/oscillation.py`.

Notation: `χ` is a nonprincipal quadratic Dirichlet character modulo `q` (values in `{0, ±1}`),
`p_0 = 2 < p_1 = 3 < …` are the primes (`Nat.nth Nat.Prime k`), and

    S(n) = Σ_{k<n} χ(p_k),        S*(x) = Σ_{p<x} χ(p)    (so S*(x) = S(π'(x))).

For Rokicki's constant `ρ = 0.d_0 d_1 d_2 …` (binary) with `d_k = [p_{k+1} ≡ 3 (mod 4)]` and
`χ = χ₄`, we have `χ₄(p_{k+1}) = 1 - 2 d_k` and `χ₄(2) = 0`, hence

    S(n + 1) = Σ_{k<n} (1 - 2 d_k) = #{k < n : d_k = 0} - #{k < n : d_k = 1}.

## 1. The theorem

**Theorem.** For every `θ < 1/2` there is no constant `C` with `|S(n)| ≤ C n^θ` for all `n`.
Equivalently, `S(n) ≠ O(n^{1/2-ε})` for every `ε > 0`; likewise `S*(x) ≠ O(x^{1/2-ε})`.

The `x`-form is the stronger one: since `π'(x) ≤ x`, a bound `S*(x) = O(π'(x)^θ)` implies
`S*(x) = O(x^θ)`. Both forms are proved, without the prime number theorem and without
Dirichlet's theorem.

| Lean name | Statement |
|---|---|
| `DirichletCharacter.IsQuadratic.not_exists_norm_sum_le_rpow` | `¬ ∃ C, ∀ n, ‖Σ_{k<n} χ(p_k)‖ ≤ C n^θ` (`θ < 1/2`) |
| `DirichletCharacter.IsQuadratic.not_isBigO_rpow` | `¬ (n ↦ Σ_{k<n} χ(p_k)) =O[atTop] (n ↦ n^θ)` |
| `DirichletCharacter.IsQuadratic.not_isBigO_rpow_one_half_sub` | the same with `θ = 1/2 - ε`, `ε > 0` |
| `DirichletCharacter.IsQuadratic.not_exists_norm_sum_primesBelow_le_rpow` | `¬ ∃ C, ∀ x, ‖Σ_{p<x} χ(p)‖ ≤ C x^θ` |
| `DirichletCharacter.IsQuadratic.not_isBigO_primesBelow_rpow` | `¬ (x ↦ Σ_{p<x} χ(p)) =O[atTop] (x ↦ x^θ)` |
| `DirichletCharacter.IsQuadratic.not_exists_norm_sum_primesBelow_le_primeCounting'_rpow` | `¬ ∃ C, ∀ x, ‖Σ_{p<x} χ(p)‖ ≤ C π'(x)^θ` |
| `DirichletCharacter.IsQuadratic.not_exists_norm_sum_succ_le_nthPrime_rpow` | core form: `¬ ∃ C, ∀ k, ‖Σ_{j≤k} χ(p_j)‖ ≤ C p_k^θ` |
| `RokickiConstant.not_exists_abs_sum_rokickiDigit_le_rpow` | `¬ ∃ C, ∀ n, |Σ_{k<n} (1 - 2 d_k)| ≤ C n^θ` |
| `RokickiConstant.not_isBigO_card_rokickiDigit_rpow` | `#{k<n : d_k = 0} - #{k<n : d_k = 1} ≠ O(n^θ)` |

Supporting lemmas (general Abel series, generalizing `PartialSums.lean`):
`rpow_mul_rpow_neg_sub_rpow_neg_le`, `norm_abelSeries_term_le_of_le_rpow`,
`summable_abelSeries_of_le_rpow`, `differentiableOn_abelSeries_of_le_rpow`,
`abelSeries_eq_tsum_of_le_rpow`, `DirichletCharacter.IsQuadratic.exp_abelSeries_add_primePowerPart_of_le_rpow`;
and two bookkeeping lemmas, `mul_rpow_le_abs_mul_rpow_max` (reduce `θ < 0` to `θ = 0`) and
`exists_forall_norm_le_rpow_of_isBigO` (turn an eventual `O`-bound into a bound for all `n`).

## 2. The proof

It is the proof of unboundedness (`General/CharacterSums.lean`) with one quantitative input.

1. **Abel series.** For `a_k = χ(p_k)` and `A_k = Σ_{j≤k} a_j`, set
   `A(s) = Σ_k A_k (p_k^{-s} - p_{k+1}^{-s})`. If `|A_k| ≤ C p_k^θ` with `θ ≥ 0`, then for
   `θ < δ ≤ re s`

       |A_k| · |p_k^{-s} - p_{k+1}^{-s}| ≤ C (|s|/δ) p_k^θ (p_k^{-δ} - p_{k+1}^{-δ})
                                        ≤ C |s|/(δ-θ) · (p_k^{θ-δ} - p_{k+1}^{θ-δ}),

   and the right side telescopes. So `A(s)` converges absolutely and locally uniformly on
   `re s > θ`, and is holomorphic there. The second inequality is the one new piece of real
   analysis: for `0 < x ≤ y`, `0 ≤ θ < δ`,

       x^θ (x^{-δ} - y^{-δ}) ≤ δ/(δ-θ) · (x^{θ-δ} - y^{θ-δ}).

   With `u = x/y ∈ (0,1]`, `z = u^δ` and `r = (δ-θ)/δ ∈ (0,1]`, it reads `r(1 - z) ≤ 1 - z^r`,
   which is the weighted AM-GM inequality `z^r · 1^{1-r} ≤ r z + (1 - r)`
   (`Real.geom_mean_le_arith_mean2_weighted`). No integrals are needed.
2. **Continuation.** For `re s > 1` summation by parts gives `A(s) = Σ_k χ(p_k) p_k^{-s}`
   (the boundary term `A_n p_n^{-s}` is `O(p_n^{θ - re s}) → 0`), so
   `exp(A(s) + primePowerPart χ s) = L(s, χ)` there by the Euler product, and on all of
   `re s > 1/2` by the identity theorem, provided `θ ≤ 1/2`.
3. **Blow-up.** As `σ → 1/2⁺`, `re primePowerPart χ σ ≥ ½ Σ_{p∤q} p^{-2σ} - O(1) → +∞`, while
   `A(σ)` stays bounded because `A` is continuous at `1/2` — *this is where `θ < 1/2` is used*.
   So `|L(σ, χ)| → ∞`, contradicting continuity of the entire function `L(·, χ)` at `1/2`.

The `n`-form follows from the core form since `n = k + 1 ≤ p_k`; the `x`-form since
`Σ_{j≤k} χ(p_j) = S*(p_k + 1)` and `(p_k + 1)^θ ≤ 2^θ p_k^θ`.

## 3. Why exactly `1/2`

The method sees one singularity: the pole-free but logarithmic singularity of `log L(s, χ)`
coming from the prime squares. Formally,

    log L(s, χ) = Σ_p χ(p) p^{-s} + ½ Σ_p χ(p)² p^{-2s} + (holomorphic on re s > 1/3),

and since `χ² = 1` off the primes dividing `q`, the second sum is `½ log ζ(2s) + O(1)`, which
blows up at `s = 1/2`: `1/2` is the abscissa of absolute convergence of `Σ χ(p)² p^{-2s}`. The
Abel series is holomorphic to the right of `θ`, so the identity
`Σ χ(p) p^{-s} = log L(s, χ) - ½ log ζ(2s) + …` forces `θ ≥ 1/2`. Nothing to the left of `1/2` is
visible: the argument never uses the location of the zeros of `L(s, χ)` (it only uses that `L`
is entire), and any exponent `θ ≥ 1/2` is consistent with everything it uses. The result is thus
"one zero-free singularity's worth" of information: the prime squares force `S` to be as large
as `x^{1/2-ε}`, whatever the zeros do.

This is a Phragmén–Landau style Ω-theorem (singularity of the Mellin transform ⇒ oscillation),
in its most elementary form.

## 4. Comparison with what is known and conjectured

**Upper bounds and GRH.** The theorem is sharp up to `x^ε` *if and only if GRH holds for `χ`*:

    S*(x) = O(x^{1/2+ε}) for every ε > 0   ⟺   L(s, χ) ≠ 0 for re s > 1/2.

(⇒) If `S*(x) = O(x^{1/2+ε})`, partial summation makes `P(s) = Σ_p χ(p) p^{-s}` holomorphic on
`re s > 1/2`; then `log L(s, χ) = P(s) + ½ Σ_{p∤q} p^{-2s} + (holomorphic on re s > 1/3)` is
holomorphic on `re s > 1/2`, so `L` has no zeros there. This is exactly the argument of §2 run
with `θ > 1/2`: the Abel series continues `P` to `re s > θ`. (⇐) Under GRH the explicit formula
gives `ψ(x, χ) = O(√x log² x)`; subtracting the prime squares (`O(√x)`) and partial summation
give `S*(x) = O(√x log x)`. Unconditionally the best upper bound is the classical
`S*(x) = O(x exp(-c √log x))` from the de la Vallée Poussin zero-free region — so
unconditionally the truth is pinned between `x^{1/2-ε}` (this theorem) and `x^{1-o(1)}`, and
closing the gap from above is GRH for `χ`. A zero `β + iγ` of `L(s, χ)` with `β > 1/2` would
give `S*(x) = Ω(x^{β-ε})`, by the same singularity argument applied to `log L`.

**Littlewood (1914).** The explicit formula, with an analysis of the zeros near the critical line
(Dirichlet's approximation theorem on the ordinates `γ`), gives the classical two-sided result

    Σ_{p≤x} χ(p) = Ω_±(√x · log log log x / log x)

(Littlewood 1914 for `π(x) - li(x)`; the same method for `π(x; 4, 3) - π(x; 4, 1)`; see Ingham,
*The distribution of prime numbers*, Ch. V, and Knapowski–Turán's comparative prime number
theory). Compared with this, our theorem

* loses a factor `x^ε` (not merely logarithms): it sees only the singularity at `1/2`, not the
  zeros;
* is two-sided only in absolute value (`Ω`, not `Ω_+` and `Ω_-` separately), so it does *not*
  give infinitely many sign changes;
* in exchange it is completely elementary given the analytic continuation of `L(s, χ)`: no
  explicit formula, no zero-counting, no GRH case split, no prime number theorem.

**Rubinstein–Sarnak (1994).** Under GRH and the linear independence hypothesis LI for the
ordinates of zeros, `E(x) = (log x / √x) · Σ_{p≤x} χ₄(p)` has a limiting logarithmic
distribution with mean `-1` (the prime-square term, the same `½ log ζ(2s)` that drives our
proof) and unbounded support; the logarithmic density of `{x : π(x; 4, 3) > π(x; 4, 1)}` is
`≈ 0.9959`. Unbounded support is the probabilistic counterpart of Littlewood's `Ω_±`. In
the `n`-scale, `√x/log x ≈ √(n / log n)`, so `|S(n)|/√n` should typically decay like
`(log n)^{-1/2}` while having `limsup = +∞` along a very sparse set. The table in §6 shows the
decay; the `limsup` is invisible at this range.

## 5. The digits of `ρ`

For `χ = χ₄`, `-S(n + 1) = #{1s} - #{0s}` among the first `n` binary digits of `ρ`. Hence
(`RokickiConstant.not_isBigO_card_rokickiDigit_rpow`):

> **the imbalance between the `1`s and `0`s among the first `n` digits of `ρ` is not
> `O(n^{1/2-ε})`**, for any `ε > 0`.

For a sequence of independent fair bits the imbalance is of order `√n` (and `√(2 n log log n)`
infinitely often, by the law of the iterated logarithm), so this says that the digits of `ρ` are
at least as unbalanced as random bits, up to `n^ε`, infinitely often. Under GRH they are also at
most that unbalanced (`O(√n log n)`), and the digit frequency is `1/2` unconditionally
(prime number theorem in arithmetic progressions; not formalized here). The Chebyshev bias says
the imbalance is mostly in favor of `1`s (primes `≡ 3 mod 4`): in the table, `S(n) < 0` for
`99.98 %` of `n ≤ 10^7`; the first `n` with `S(n) > 0` is `n = 2946` (`p = 26861`, Leech 1957).

## 6. Numerics (`scripts/oscillation.py`)

`S(n) = Σ_{k<n} χ₄(p_k)`. Column 2 is `max_{n≤N} |S(n)|/√n`, which is attained at `n = 5`
(`S(5) = -2`, primes `2, 3, 5, 7, 11`) for every `N`, so column 3 restricts to the last decade
`N/10 < n ≤ N`. Column 6 is the Rubinstein–Sarnak normalization
`max_{x ≤ p_N} |S*(x)| log x/√x` (attained at `x = 126227`, `S = -73`). The last column is the
proportion of `n ≤ N` with `S(n) < 0`.

|          N | max_{n≤N} | max_{N/10<n≤N} |    at n |  S(n) | max \|S*\| log x/√x | P(S<0) |
|-----------:|----------:|---------------:|--------:|------:|--------------------:|-------:|
|     10^4   |    0.8944 |         0.7232 |    1394 |   -27 |              2.4071 | 0.9988 |
|     10^5   |    0.8944 |         0.6709 |   11840 |   -73 |              2.4134 | 0.9965 |
|     10^6   |    0.8944 |         0.5550 |  219457 |  -260 |              2.4134 | 0.9978 |
|     10^7   |    0.8944 |         0.5214 | 3767167 | -1012 |              2.4134 | 0.9998 |

`S(10^k)` for `k = 4, …, 7`: `-31, -101, -403, -1095`, i.e. `S(N)/√N ≈ -0.31, -0.32, -0.40,
-0.35` and `S(N) √(log N)/√N ≈ -0.94, -1.08, -1.50, -1.39`: consistent with the
`√(n/log n)` scale and the negative mean of §4. The windowed maximum of `|S(n)|/√n` decreases
slowly, as `(log n)^{-1/2}` predicts; no finite computation can see the `Ω` of the theorem,
which is an asymptotic statement about a sparse set of `n`.

## 7. What is not done, and next steps

* **One-sided version (`Ω_-`, the Chebyshev-bias direction).** Claim: for `θ < 1/2` there is
  no `C` with `S*(x) ≥ -C x^θ` for all `x`. Proof sketch: if `S*(x) + C x^θ ≥ 0`, the Abel
  series of `S* + C x^θ` has nonnegative terms for real `σ`, so by **Landau's theorem** on
  Dirichlet series (integrals) with nonnegative coefficients it converges up to its first real
  singularity; its continuation is `P(σ) + C · (holomorphic on σ > θ)`, and
  `P(σ) = log L(σ, χ) - ½ log ζ(2σ) + O(1) → -∞` as `σ → max(1/2, β)⁺`, where `β` is the
  largest real zero of `L(·, χ)` in `(1/2, 1)` if any — contradicting nonnegativity. So
  `S*(x) = Ω_-(x^{1/2-ε})`, which implies the present theorem. Not formalized: Mathlib has no
  Landau (Pringsheim-type) theorem for Dirichlet series with nonnegative coefficients; that
  theorem is the missing ingredient. The `Ω_+` direction is genuinely harder (it needs the
  zeros, as in Littlewood).
* **Sign changes.** Infinitely many sign changes of `S` need either Littlewood's method (explicit
  formula + Dirichlet approximation on the `γ`) or Landau's theorem combined with a zero of
  `L(s, χ)` off the real axis on or near `re s = 1/2`. Both are well beyond the current Mathlib
  infrastructure (no explicit formula for `ψ(x, χ)`).
* **Other residue constants.** The digit corollary is stated for `χ₄` only; the analogous
  statements for the constants of `General/Expansion.lean` and `General/ResidueConstant.lean`
  should follow from the general theorem in the same way (not stated here).
