# Landau's theorem and the one-sided bias: `Σ χ(p)` is `Ω₋(√x/(log x)^A)`

**Status.** Proved and formalized (`RokickiConstant/General/Landau.lean`, no `sorry`): Landau's
theorem for Laplace transforms of positive measures (hence for Dirichlet series with nonnegative
coefficients and for Mellin transforms of nonnegative functions), and the one-sided (`Ω₋`)
theorem announced in `oscillation.md` §6.4 and §8. The numerical table in §6 is the third table
printed by `python3 scripts/oscillation.py`.

Notation as in `oscillation.md`: `χ` is a nonprincipal quadratic character modulo `q`,
`p_0 = 2 < p_1 < …` the primes, `S(n) = Σ_{k<n} χ(p_k)`, `S*(x) = Σ_{p<x} χ(p)`, and for `ρ`
(`χ = χ₄`) `S(n + 1) = #{k < n : d_k = 0} - #{k < n : d_k = 1}`.

## 1. The theorems

**Theorem A (Landau).** Let `μ` be a measure on `[0, ∞)` and `F(s) = ∫ e^{-su} dμ(u)` its
Laplace transform. Suppose `∫ e^{-σu} dμ < ∞` for every real `σ > σ₀`, and that `F` continues
holomorphically to a neighbourhood of the real point `σ₀`. Then `∫ e^{-σu} dμ < ∞` for some real
`σ < σ₀`. Equivalently: the (real) abscissa of convergence of `F` is a singularity of `F`.

The Dirichlet series `Σ_k c_k λ_k^{-s}` with `c_k ≥ 0`, `λ_k ≥ 1` are the case
`μ = Σ_k c_k δ_{log λ_k}`, and the Mellin transform `∫_1^∞ h(x) x^{-s-1} dx` of a nonnegative
function is the case `dμ(u) = h(e^u) du`.

**Theorem B (one-sided bias).** For every `A > 1` and every `C`,

    S*(x) < -C √x / (log x)^A   for infinitely many x,

that is, `S*(x) = Ω₋(√x/(log x)^A)`. In the index scale, `S(n) = Ω₋(√n/(log n)^A)` for every
`A > 1/2`. For `ρ`: for every `A > 1/2` and every `C`, among the first `n` binary digits of `ρ`
the ones outnumber the zeros by more than `C √n/(log n)^A` for infinitely many `n`.

The sign: `S < 0` means more primes with `χ(p) = -1`; for `χ₄` these are the primes `≡ 3 (mod 4)`,
recorded by the digit `1`. So the digits of `ρ` lean towards `1`, which is the direction of
Chebyshev's bias. Since `x^θ = o(√x/(log x)^A)`, the theorem contains `S*(x) = Ω₋(x^θ)` for all
`θ < 1/2`.

| Lean name | Statement |
|---|---|
| `integrable_exp_neg_mul_of_differentiableOn_ball` | Pringsheim form: if `F` converges at `s₁ - δ` and agrees near `s₁` with a function holomorphic on `B(s₁, r)`, then `∫ e^{-σu} dμ < ∞` for all real `σ > s₁ - r` |
| `exists_lt_integrable_exp_neg_mul` | Theorem A (abscissa form) |
| `exists_lt_summable_mul_rpow_neg` | Theorem A for `Σ c_k λ_k^{-s}`, `c_k ≥ 0`, `λ_k ≥ 1` |
| `DirichletCharacter.IsQuadratic.not_exists_le_re_sum_succ_nthPrime_rpow_div_log_rpow` | core, `A > 1`: `¬ ∃ C, ∀ k, -C p_k^{1/2}/(log p_k)^A ≤ Σ_{j≤k} χ(p_j)` |
| `DirichletCharacter.IsQuadratic.frequently_re_sum_succ_lt_nthPrime_rpow_div_log_rpow` | `∀ C, ∃ᶠ k, Σ_{j≤k} χ(p_j) < -C p_k^{1/2}/(log p_k)^A` (`A > 1`) |
| `DirichletCharacter.IsQuadratic.frequently_re_sum_primesBelow_lt_rpow_div_log_rpow` | `∀ C, ∃ᶠ x, S*(x) < -C x^{1/2}/(log x)^A` (`A > 1`) |
| `DirichletCharacter.IsQuadratic.not_exists_le_sum_primesBelow_rpow_div_log_rpow` | `¬ ∃ C, ∀ x ≥ 2, -C x^{1/2}/(log x)^A ≤ S*(x)` (`A > 1`) |
| `DirichletCharacter.IsQuadratic.frequently_re_sum_succ_lt_rpow_div_log_rpow` | `∀ C, ∃ᶠ k, Σ_{j≤k} χ(p_j) < -C k^{1/2}/(log k)^A` (`A > 1/2`) |
| `DirichletCharacter.IsQuadratic.frequently_re_sum_lt_rpow_div_log_rpow` | `∀ C, ∃ᶠ n, S(n) < -C n^{1/2}/(log n)^A` (`A > 1/2`) |
| `DirichletCharacter.IsQuadratic.not_exists_le_re_sum_rpow_div_log_rpow` | `¬ ∃ C, ∀ n ≥ 2, -C n^{1/2}/(log n)^A ≤ S(n)` (`A > 1/2`) |
| `RokickiConstant.frequently_card_rokickiDigit_one_sub_card_zero_gt` | `∀ C, ∃ᶠ n, C n^{1/2}/(log n)^A < #{d_k = 1} - #{d_k = 0}` (`k < n`, `A > 1/2`) |
| `RokickiConstant.not_exists_card_rokickiDigit_one_sub_card_zero_le` | `¬ ∃ C, ∀ n ≥ 2, #{d_k = 1} - #{d_k = 0} ≤ C n^{1/2}/(log n)^A` |

(`.re` appears in the Lean statements because `χ` is `ℂ`-valued; the sums are real.)

Supporting definitions and lemmas: `stepMeasure H q` (the measure `Σ_k H_k 1_{(log q_k, log
q_{k+1}]}(u) du`, whose Laplace transform is the Mellin transform of the step function equal to
`H_k` on `[q_k, q_{k+1})`), `mul_complexMGF_stepMeasure` (`s F(s) = Σ_k H_k (q_k^{-s} -
q_{k+1}^{-s})`), `integrable_stepMeasure`, `diracMeasure`, `complexMGF_diracMeasure`,
`integrable_diracMeasure_iff`, `differentiableOn_complexMGF_neg`,
`mem_ball_of_mem_ball_of_re_le` (the geometry of the gluing), `exists_forall_neg_mul_le_of_eventually`,
`rpow_div_log_rpow_le_nthPrime` (Chebyshev, as in `Oscillation.lean`).

## 2. Landau's theorem: the proof

The Laplace transform is Mathlib's `ProbabilityTheory.complexMGF (fun u ↦ -u) μ`, and
`iteratedDeriv_complexMGF` gives its derivatives at an interior point of convergence:

    F^{(n)}(s₁) = ∫ (-u)^n e^{-s₁u} dμ(u).

Let `Ψ` be holomorphic on the disc `B(s₁, r)` with `Ψ = F` near the real point `s₁`. Then
`F^{(n)}(s₁) = Ψ^{(n)}(s₁)` and the Cauchy–Taylor expansion (`Complex.hasSum_taylorSeries_on_ball`)
at `σ = s₁ - t`, `0 < t < r`, reads

    Ψ(s₁ - t) = Σ_n (-t)^n/n! · F^{(n)}(s₁) = Σ_n ∫ (tu)^n/n! · e^{-s₁u} dμ(u).

Every term is a nonnegative real number, because the measure lives on `u ≥ 0` and the signs
`(-t)^n (-u)^n` cancel. Tonelli (`lintegral_tsum`) then sums in the other order:

    ∫ e^{-(s₁-t)u} dμ = ∫ Σ_n (tu)^n/n! e^{-s₁u} dμ = Σ_n ∫ (tu)^n/n! e^{-s₁u} dμ < ∞.

This is the Pringsheim form. For the abscissa form one glues `F` (holomorphic on `re s > σ₀`,
`differentiableOn_complexMGF`) and the given continuation `G` on `B(σ₀, ε)` into one function on
the disc `B(σ₀ + 1, 1 + ε²/3)`, which lies in `{re s > σ₀} ∪ B(σ₀, ε)`; its real part reaches
`σ₀ - ε²/3`.

**Why the integral (Mellin) form and not a series over the primes.** The natural series-level
object, the Abel series `Σ_k H_k (p_k^{-s} - p_{k+1}^{-s})` with `H_k ≥ 0`, does not have
Taylor coefficients of fixed sign: `(-d/ds)^m (p^{-s} - p'^{-s}) = (log p)^m p^{-s} - (log
p')^m p'^{-s}` changes sign as `m` grows. Regrouping it as a Dirichlet series `Σ_k (H_k -
H_{k-1}) p_k^{-s}` destroys positivity. Dividing by `s` repairs this:

    (p^{-s} - p'^{-s}) / s = ∫_{log p}^{log p'} e^{-su} du

is completely monotone in `s`. This is exactly the Mellin transform of the step function, and it
is why Landau's theorem is formalized for Laplace transforms of measures. The step-function
measure `stepMeasure` is a countable sum of weighted restrictions of Lebesgue measure, so all
measure theory reduces to `lintegral_sum_measure`/`integral_sum_measure` and the elementary
integral `∫_a^b e^{-su} du`.

## 3. The one-sided theorem: the proof

Suppose `S(k+1) = Σ_{j≤k} χ(p_j) ≥ -C g_k` for all `k`, with `g_k = p_k^{1/2}/(log p_k)^A`,
`C ≥ 0`. Put `H_k = S(k+1) + C g_k ≥ 0`, the value on `[p_k, p_{k+1})` of the nonnegative function
`h = S* + C g`, and let `μ = stepMeasure H` and `F` its Laplace transform (the Mellin transform
of `h`). Then:

1. `F(σ)` converges for `σ > 1` (`H_k ≤ B p_k`), and for `re s > 1`, by Abel summation,
   `s F(s) = primePart χ s + Γ(s)`, where `Γ(s) = Σ_k C g_k (p_k^{-s} - p_{k+1}^{-s})` is the
   transform of `C g`. `Γ` is holomorphic on `re s > 1/2` and, because `A > 1`, continuous on
   `[1/2, 2]` up to the line (`continuousOn_abelSeries_of_le_rpow_div_log_rpow`, §6 of
   `oscillation.md`).
2. Let `σ_c ∈ [1/2, 3/2]` be the abscissa of convergence of `F` on `(1/2, ∞)`. On `re s > σ_c`
   the function `E(s) = s F(s) - Γ(s) + primePowerPart χ s` is holomorphic and `exp E = L(·, χ)`
   (identity theorem from `re s > 1`, where it is the Euler product). In particular `L(s, χ) ≠ 0`
   on `re s > σ_c`, and for real `σ > σ_c`
   `0 ≤ σ F(σ) = log |L(σ, χ)| + Γ(σ) - re primePowerPart χ σ`.
3. Three cases at `σ_c`:
   * `σ_c = 1/2`: `log |L|` is bounded above near `1/2`, `Γ` has a limit, and
     `re primePowerPart χ σ → +∞` (the prime squares, `tendsto_re_primePowerPart`): the right
     side tends to `-∞`.
   * `σ_c > 1/2` and `L(σ_c, χ) = 0` (a real zero): `log |L(σ, χ)| → -∞` and the other terms
     converge: the right side tends to `-∞`.
   * `σ_c > 1/2` and `L(σ_c, χ) ≠ 0`: on a small disc about `σ_c`, `ℓ(s) = log(L(s)/L(σ_c))` is a
     holomorphic logarithm of `L` up to a constant, `E - ℓ` is constant on the right half of the
     disc (its derivative vanishes because `exp(E - ℓ)` is constant), and
     `G = (ℓ + c + Γ - primePowerPart χ)/s` continues `F` across `σ_c`. Theorem A gives
     convergence at some `σ < σ_c`, contradicting the definition of `σ_c`.

   In the first two cases the nonnegative quantity `σ F(σ)` tends to `-∞`: contradiction.

The `x`-scale and index-scale forms, and the digit form, follow as in `oscillation.md` §6.1
(`p_{k+1} ≤ 2p_k`, `p_k ≤ k²`, `k log p_k ≤ 5 p_k`), now applied to one-sided bounds; an
eventual lower bound is turned into a global one by enlarging `C`
(`exists_forall_neg_mul_le_of_eventually`).

## 4. Why positivity and the prime squares give the direction, with no zeros

Writing `log L = primePart + primePowerPart`, the Mellin transform of `S*` is
`(log L(s, χ) - primePowerPart χ s)/s`. On the real axis, `primePowerPart χ σ = ½ Σ_p χ(p)²
p^{-2σ} + O(1) → +∞` as `σ → 1/2⁺`, because `χ(p)² = 1` for all `p ∤ q`. This is the analytic
shadow of the prime squares: `Σ_{p²<x} χ(p²) = π(√x) + O(1)` enters `log L` with the coefficient
`½`, and on the primes themselves it appears with the opposite sign, as the term
`-½ π(√x) ≈ -√x/log x`. So the Mellin transform of `S*` tends to `-∞` on the real axis, and the
transform of `S* + C g` is pulled to `-∞` too unless `C g` compensates, which it cannot when
`g = o(√x/log x)` in the Mellin sense (`A > 1`).

Positivity enters only through Landau's theorem: a nonnegative `h` has a transform that is
holomorphic up to its real abscissa and is `≥ 0` there. No information on the zeros of `L(s, χ)`
is used. Real zeros (Siegel zeros included) only help: at a real zero `log |L| → -∞` pushes the
transform further down (case 2 of §3). Nonreal zeros play no role at all: they never meet the real
axis.

## 5. Why `Ω₊` is different

Under `S*(x) ≤ C g(x)` the nonnegative function is `k = C g - S*`, with transform
`(C Γ(σ) - log L(σ, χ) + primePowerPart χ σ)/σ → +∞` as `σ → 1/2⁺`. A transform of a
nonnegative function may well tend to `+∞` at its abscissa, so the real axis gives no
contradiction. One needs a singularity off the real axis that the positivity of `k` forbids:

* Landau's inequality `|K(σ + it)| ≤ K(σ)` for the transform `K` of `k ≥ 0` (or, equivalently,
  positivity of `k(x)(1 + cos(γ log x - φ))`) compares the size of `K` at `σ + iγ` with its size on
  the real axis. At a zero `ρ₀ = 1/2 + iγ₀` of multiplicity `m`, `|K(σ + iγ₀)| ≈ (m/|ρ₀|) log
  1/(σ - 1/2)`, while `K(σ) ≈ log 1/(σ - 1/2)` from the prime squares. So a single zero gives a
  contradiction only if `m > |ρ₀|`, which fails for every known L-function (for `χ₄` the lowest
  zero has `γ₀ ≈ 6.02`). This is the difference with `ψ(x) - x`, where there is no prime-square
  term on the real axis and one zero suffices for `Ω₊(√x)`.
* With a product kernel `Π_j (1 + cos(γ_j log x - φ_j)) ≥ 0` over finitely many zeros one gets a
  contradiction once `Σ_j m_j/|ρ_j| > 1`, provided no nontrivial combination `Σ ε_j γ_j`
  (`ε_j ∈ {-1, 0, 1}`) vanishes or hits another ordinate (Ingham-style). Since `Σ 1/|ρ|` diverges
  this needs a few dozen certified zeros of `L(s, χ₄)` and a finite non-resonance check: zero
  locations that Mathlib does not have. If some nonreal zero had real part `β > 1/2` exceeding
  every real zero, a much simpler argument (the transform of `C x^{β-ε} - S*` would have to be
  holomorphic at that zero) would give `Ω₊(x^{β - ε})`.

So `Ω₊` needs nonreal zeros and a twisted kernel; the present framework, which uses no zeros,
gives exactly `Ω₋`. Infinitely many sign changes of `S*` (which would follow from `Ω₋` and `Ω₊`
together) remain out of reach for the same reason.

## 6. Comparison with Rubinstein–Sarnak, and numerics

Under GRH and the linear independence hypothesis, `S*(x) log x/√x` has a limiting logarithmic
distribution with mean `-1` (for `χ₄`: `π(x; 4, 3) - π(x; 4, 1) ≈ √x/log x` on average), and the
sign of the mean is the sign of the prime-square coefficient `-χ(p)²/2`: this is the bias. The
theorem here is the unconditional shadow of this: the same prime-square term forces `S*` to be
very negative infinitely often (`Ω₋`), on the scale `√x/(log x)^{1+ε}`, while the opposite
deviation (`Ω₊`), which in Rubinstein–Sarnak comes from the oscillation of the zeros, is not
seen.

Third table of `scripts/oscillation.py` (`χ = χ₄`, `S*(x) = Σ_{p≤x} χ₄(p)`, evaluated at the
primes `x ≤ p_N`, where the extremes of either sign are attained since `(log x)^A/√x` decreases
for `x ≥ e^{2A}`):

|        N | min S* log^1.5 x/√x | min S* log² x/√x |   at x   | max S* log^1.5 x/√x | max S* log² x/√x |   at x   |
|---------:|--------------------:|-----------------:|---------:|--------------------:|-----------------:|---------:|
|   10^4   |             -7.4419 |         -24.4954 |    50723 |              0.1987 |           0.6346 |    26861 |
|   10^5   |             -8.2713 |         -30.0783 |   775091 |              0.4938 |           1.8036 |   623681 |
|   10^6   |             -8.6004 |         -34.0433 | 11169643 |              0.4938 |           1.8201 | 12366589 |
|   10^7   |             -9.6601 |         -40.9493 | 63679459 |              0.4938 |           1.8201 | 12366589 |

The running minimum decreases steadily and slowly (for `A = 2` roughly like `-log x`), as the
theorem (it tends to `-∞` for every `A > 1`) predicts. The running maximum is two orders of
magnitude smaller and is attained in the classical regions where `S*` is positive (`x = 26861`,
the first sign change, then near `623681` and `12366589`). This asymmetry is the bias, and it
matches §5: positive excursions exist (Littlewood) but are not visible to an argument without
zeros. As in `oscillation.md` §7, no finite computation can see the `Ω`-statements themselves.

## 7. What is not done, and next steps

* **`Ω₊`.** See §5: it needs certified nonreal zeros of `L(s, χ)` and a positive trigonometric
  kernel, or Littlewood's method. Not formalized.
* **`Ω₋` at the Rubinstein–Sarnak scale, with the sharp constant.** The argument of §3 should
  also work at `A = 1` with a constant. For `g(x) = √x/log x` the transform of `g` is
  `σ ∫ x^{-σ-1/2} dx/log x = ½ log 1/(σ - 1/2) + O(1)` as `σ → 1/2⁺` (an exponential integral; the
  step version is a Riemann sum of it, so no prime number theorem is needed), while
  `primePowerPart χ σ = ½ log 1/(σ - 1/2) + O(1)` (Mertens-type, from
  `exists_norm_primePart_one_add_log_le` in `SingleClass.lean` at `2σ`). Then
  `0 ≤ σF(σ) ≤ ((c - 1)/2) log 1/(σ - 1/2) + O(1)`, a contradiction for `c < 1`. Expected
  statement: **for every `c < 1`, `S*(x) < -c √x/log x` for infinitely many `x`**, i.e.
  `liminf S*(x) log x/√x ≤ -1`, matching the Rubinstein–Sarnak mean `-1`. Not formalized; it
  needs the two-sided asymptotics of both transforms with constant `½`, where the present proof
  only needs boundedness of `Γ`.
* **Other residue constants.** The digit corollary is stated for `ρ` (`χ₄`) only; the constants
  of `General/Expansion.lean` and `General/ResidueConstant.lean` built from a quadratic character
  should satisfy the same one-sided statement (the class of non-residues wins).
