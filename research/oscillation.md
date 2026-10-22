# Quantitative oscillation: `Σ χ(p)` is `Ω(x^{1/2-ε})`

**Status.** Proved and formalized (`RokickiConstant/General/Oscillation.lean`, no `sorry`). This
is Direction 2 of `PROGRAM.md`. The `x^{1/2-ε}` theorem is §§1–5; the log-power refinement
`S*(x) ≠ O(√x/(log x)^A)`, `A > 1`, is §6. The numerical table in §7 is reproduced by
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
`(log n)^{-1/2}` while having `limsup = +∞` along a very sparse set. The table in §7 shows the
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

## 6. Log-power refinement

The argument of §2 does not need a power saving below `1/2`: a power of the logarithm suffices.

**Theorem.** Let `A > 1`. Then

    S*(x) = Σ_{p<x} χ(p)  is not  O(√x / (log x)^A),

and, in the index scale, `S(n) = Σ_{k<n} χ(p_k)` is not `O(√n / (log n)^{A'})` for every
`A' > 1/2`. For `ρ`: the imbalance `#{k < n : d_k = 0} - #{k < n : d_k = 1}` is not
`O(√n / (log n)^{A'})` for `A' > 1/2`.

The index exponent is `A' > 1/2` rather than `A' > 1` because `p_n ≍ n log n`: a bound
`S(n) = O(√n/(log n)^{A'})` gives `S(k+1) = O(√p_k/(log p_k)^{A'+1/2})`, and `A' + 1/2 > 1`. The
`x`-scale statement is the primary one and implies the index one; the converse loses `(log)^{1/2}`.

| Lean name (`DirichletCharacter.IsQuadratic.` unless stated) | Statement |
|---|---|
| `not_exists_norm_sum_primesBelow_le_rpow_div_log_rpow` | `A > 1`: `¬ ∃ C, ∀ x ≥ 2, ‖Σ_{p<x} χ(p)‖ ≤ C x^{1/2} / (log x)^A` |
| `not_isBigO_primesBelow_rpow_div_log_rpow` | `A > 1`: `¬ (x ↦ Σ_{p<x} χ(p)) =O[atTop] (x ↦ x^{1/2} / (log x)^A)` |
| `not_exists_norm_sum_le_rpow_div_log_rpow` | `A > 1/2`: `¬ ∃ C, ∀ n ≥ 2, ‖Σ_{k<n} χ(p_k)‖ ≤ C n^{1/2} / (log n)^A` |
| `not_isBigO_rpow_div_log_rpow` | `A > 1/2`: `¬ (n ↦ Σ_{k<n} χ(p_k)) =O[atTop] (n ↦ n^{1/2} / (log n)^A)` |
| `not_exists_norm_sum_succ_le_nthPrime_rpow_div_log_rpow` | core, `A > 1`: `¬ ∃ C, ∀ k, ‖Σ_{j≤k} χ(p_j)‖ ≤ C p_k^{1/2} / (log p_k)^A` |
| `not_isBigO_sum_succ_nthPrime_rpow_div_log_rpow` | the same, Landau form |
| `not_isBigO_sum_succ_rpow_div_log_rpow` | `A > 1/2`: `Σ_{j≤k} χ(p_j)` is not `O(k^{1/2} / (log k)^A)` |
| `RokickiConstant.not_exists_abs_sum_rokickiDigit_le_rpow_div_log_rpow` | `A > 1/2`: `¬ ∃ C, ∀ n ≥ 2, \|Σ_{k<n} (1 - 2 d_k)\| ≤ C n^{1/2} / (log n)^A` |
| `RokickiConstant.not_isBigO_card_rokickiDigit_rpow_div_log_rpow` | `A > 1/2`: `#{d_k = 0} - #{d_k = 1}` (over `k < n`) is not `O(n^{1/2} / (log n)^A)` |

Supporting lemmas: `rpow_mul_rpow_neg_sub_rpow_neg_le_mul_log`, `mul_sub_div_mul_rpow_neg_le`,
`rpow_mul_rpow_neg_sub_div_log_rpow_le` (real inequalities), `norm_abelSeries_term_le_of_le_rpow_div_log_rpow`,
`continuousOn_abelSeries_of_le_rpow_div_log_rpow` (the Abel series is continuous on `σ ∈ [1/2, 2]`),
`exists_forall_norm_le_mul_of_isBigO` (eventual to global bounds), `Nat.nth_prime_succ_le_two_mul`
(Bertrand: `p_{k+1} ≤ 2 p_k`), `Nat.log_nth_prime_le_two_mul_log` (`p_k ≤ k²` for `k ≥ 4096`, from
`Chebyshev.pi_ge`) and `Nat.succ_mul_log_nth_prime_le` (`(k+1) log p_k ≤ 5 p_k`, from
`Chebyshev.pi_le_log4_mul_div`).

### 6.1 Proof idea: uniform convergence up to the line `re s = 1/2`

In §2 the hypothesis `θ < 1/2` was used only once: to make the Abel series `A(s)` continuous at
`s = 1/2`. Holomorphy on `re s > 1/2`, the identity `L = exp(A + primePowerPart)` there, and the
blow-up of `primePowerPart` at `1/2⁺` all hold with `θ = 1/2`. So it suffices that `A(σ)` stays
bounded as `σ → 1/2⁺`, and for that it suffices that the series converges uniformly on
`σ ∈ [1/2, 2]`, *including the line itself*.

Suppose `|A_k| ≤ C √p_k / (log p_k)^A`. For `re s ≥ 1/2` (with `δ = 1/2` in
`norm_ofReal_cpow_neg_sub_cpow_neg_le`),

    |A_k| |p_k^{-s} - p_{k+1}^{-s}| ≤ 2 |s| C · √p_k (p_k^{-1/2} - p_{k+1}^{-1/2}) / (log p_k)^A.

Write `a = log p_k ≤ b = log p_{k+1}`. Then:

1. `√p_k (p_k^{-1/2} - p_{k+1}^{-1/2}) = 1 - w^{-1} ≤ log w ≤ b - a` for `w = (p_{k+1}/p_k)^{1/2}`;
2. Bertrand's postulate `p_{k+1} ≤ 2 p_k ≤ p_k²` gives `b ≤ 2a`, so `a^{-A} ≤ 2^A b^{-A}`;
3. the tangent-line inequality for the convex decreasing function `t ↦ t^{1-A}`,
   `(A - 1)(b - a) b^{-A} ≤ a^{1-A} - b^{1-A}` (proved from `e^y ≥ 1 + y` and `log w ≥ 1 - 1/w`).

Hence the `k`-th term is at most `2|s| C · 2^A/(A - 1) · ((log p_k)^{1-A} - (log p_{k+1})^{1-A})`,
which telescopes. With `|s| ≤ 2` this is a summable majorant independent of `σ ∈ [1/2, 2]`, so
the Weierstrass M-test (`continuousOn_tsum`) makes `σ ↦ A(σ)` continuous on `[1/2, 2]`. No
integrals, and no prime number theorem: the only prime-distribution input is Bertrand.

In integral language the whole condition is

    Σ_k (p_{k+1} - p_k) / (p_k (log p_k)^A)  ≍  ∫_2^∞ dt / (t (log t)^A)  <  ∞,

which holds exactly for `A > 1`.

The `x`-scale form follows since `Σ_{j≤k} χ(p_j) = S*(p_k + 1)`, `(p_k + 1)^{1/2} ≤ √2 p_k^{1/2}`
and `log(p_k + 1) ≥ log p_k`. The index form uses `p_k ≤ k²` (`k ≥ 4096`; Chebyshev's
`π(n) ≥ (n log 2 - log(n+1))/log n` gives `π(n) ≥ √n + 1` for `n ≥ 8⁴`) and `k log p_k ≤ 5 p_k`
(Chebyshev's `π(x) ≤ 2 log 4 · x/log x + √x`).

### 6.2 Comparison with Littlewood

Littlewood's theorem (§4) is `S*(x) = Ω_±(√x · log log log x / log x)`. The refinement gives
`S*(x) = Ω(√x / (log x)^{1+ε})`, i.e. we are within a factor `(log x)^ε · log log log x` of
Littlewood (in the index scale: `Ω(√n/(log n)^{1/2+ε})` against Littlewood's
`Ω(√n · log log log n / (log n)^{1/2})`). This is obtained without the explicit formula, without
any information on the zeros of `L(s, χ)`, without the prime number theorem (Bertrand and
Chebyshev suffice), but only for `|S*|`, not for each sign.

### 6.3 Why the method stops exactly at `A = 1`

At `A = 1` the majorant becomes `Σ_k (log p_{k+1} - log p_k)/log p_k ≍ ∫ dt/(t log t) = ∞`, and
this is not an artifact of the estimates: `S*(x) = O(√x / log x)` is **not** ruled out by this
argument. The only thing the method sees is the singularity of `-½ log ζ(2s) ≈ ½ log(s - 1/2)` at
`s = 1/2` (§3), and this singularity is exactly the Mellin transform of a function of size
`√x / log x`: indeed `-½ π(√x) ≈ -√x/log x` (the prime squares) has

    s ∫_2^∞ (√x / log x) x^{-s-1} dx  ≈  ∫ e^{-(s-1/2)u} du/u  ≈  log(1/(s - 1/2))   (s → 1/2⁺).

So a hypothetical `S*` of size `√x/log x` with the right sign would reproduce the singularity
without contradiction. Going below `√x/log x` (Littlewood's extra `log log log x`) requires
infinitely many zeros of `L(s, χ)` and Diophantine approximation of their ordinates: information
this framework never uses. In this sense the refinement is optimal for the method up to `(log x)^ε`.

### 6.4 The one-sided question

The theorem is two-sided only in absolute value. The two signs behave very differently.

* **`Ω₋` (the Chebyshev-bias direction, `S*` very negative).** Suppose `S*(x) ≥ -C g(x)` with
  `g(x) = √x/(log x)^A`, `A > 1` (or `g(x) = x^θ`, `θ < 1/2`). Then `f = S* + C g ≥ 0`, and by
  **Landau's theorem** on Mellin (Laplace) integrals of nonnegative functions, `∫ f x^{-s-1} dx`
  converges up to its first real singularity. On the real axis it continues as
  `P(σ)/σ + C G(σ)` with `G(σ) = ∫ g x^{-σ-1} dx` bounded on `σ > 1/2` (here `A > 1` is used), and
  `P(σ) = log L(σ, χ) - ½ log ζ(2σ) + O(1) → -∞` as `σ` decreases to `max(1/2, β)`, where `β` is
  the largest real zero of `L(·, χ)` in `(1/2, 1)` if any. This contradicts `f ≥ 0`. So
  `S*(x) = Ω₋(√x/(log x)^A)` *follows from Landau's theorem alone*; real zeros of `L` only help (they
  make `P` more negative). For `χ₄`, `L(σ, χ₄) > 0` for `σ > 0` (alternating series), so the
  relevant singularity is exactly the prime-square one at `1/2`. The missing ingredient is
  Landau's theorem itself (a Pringsheim-type theorem for Mellin integrals), which Mathlib does
  not have; with it, this would be a short addition to the present file.
* **`Ω₊` (against the bias, `S*` very positive).** Here the real axis gives nothing: under
  `S*(x) ≤ C g(x)` the function `C g - S* ≥ 0` has Mellin transform `C G(σ) - P(σ)/σ → +∞`, which
  is consistent. One needs a *nonreal* singularity on or to the right of the critical line, i.e.
  a zero `ρ₀ = β₀ + iγ₀` of `L(s, χ)` with `β₀ ≥ 1/2`, `γ₀ ≠ 0` (for instance a zero on the
  critical line, which exist but are not in Mathlib), and Landau's argument with the twisted
  kernel `1 + cos(γ₀ log x - φ)` applied to `C g - S*` (Ingham, *The distribution of prime
  numbers*, Ch. V; this is also how `Ω_±` results are obtained there). The real-zero-freeness
  of `L(σ, χ₄)` does not help in this direction: it removes real singularities, which only ever
  feed `Ω₋`. So `Ω₊` is out of reach of the present framework, which uses no zeros at all.

## 7. Numerics (`scripts/oscillation.py`)

`S(n) = Σ_{k<n} χ₄(p_k)`. Column 2 is `max_{n≤N} |S(n)|/√n`, which is attained at `n = 5`
(`S(5) = -2`, primes `2, 3, 5, 7, 11`) for every `N`, so column 3 restricts to the last decade
`N/10 < n ≤ N`. Column 6 is the Rubinstein–Sarnak normalization
`max_{x ≤ p_N} |S*(x)| log x/√x` (attained at `x = 126227`, `S = -73`), and column 7 is the
log-power normalization `max_{x ≤ p_N} |S*(x)| (log x)²/√x` of §6 (here `S*(x) = Σ_{p≤x} χ₄(p)`,
evaluated at the primes; `(log x)^A/√x` is decreasing for `x ≥ e^{2A}`). The last column is the
proportion of `n ≤ N` with `S(n) < 0`.

|          N | max_{n≤N} | max_{N/10<n≤N} |    at n |  S(n) | max \|S*\| log x/√x | max \|S*\| log² x/√x | P(S<0) |
|-----------:|----------:|---------------:|--------:|------:|--------------------:|---------------------:|-------:|
|     10^4   |    0.8944 |         0.7232 |    1394 |   -27 |              2.4071 |              24.4954 | 0.9988 |
|     10^5   |    0.8944 |         0.6709 |   11840 |   -73 |              2.4134 |              30.0783 | 0.9965 |
|     10^6   |    0.8944 |         0.5550 |  219457 |  -260 |              2.4134 |              34.0433 | 0.9978 |
|     10^7   |    0.8944 |         0.5214 | 3767167 | -1012 |              2.4134 |              40.9493 | 0.9998 |

The `(log x)²` column is attained at `x = 50723, 775091, 11169643, 63679459` (`S* = -47, -144,
-432, -1012`) and grows steadily, roughly like `log x`, consistent with the theorem of §6, which
says that it is unbounded (as is the analogous column for every `A > 1`; for `A = 1.5` the maxima are `7.44, 8.27,
8.60, 9.66`), while the `log x` column (`A = 1`) is flat at `2.41` on this range, consistent with
the `√x/log x` scale of Rubinstein–Sarnak and with §6.3 (`A = 1` is not covered). In the index
scale, `max_{n≤N} |S(n)| √(log n)/√n` is `1.95, 2.05, 2.05, 2.05` (flat) while
`max_{n≤N} |S(n)| log n/√n` is `5.58, 6.38, 6.83, 7.90` (growing), matching the index threshold
`A' = 1/2`. (These extra figures are the second table printed by the script.)

`S(10^k)` for `k = 4, …, 7`: `-31, -101, -403, -1095`, i.e. `S(N)/√N ≈ -0.31, -0.32, -0.40,
-0.35` and `S(N) √(log N)/√N ≈ -0.94, -1.08, -1.50, -1.39`: consistent with the
`√(n/log n)` scale and the negative mean of §4. The windowed maximum of `|S(n)|/√n` decreases
slowly, as `(log n)^{-1/2}` predicts; no finite computation can see the `Ω` of the theorem,
which is an asymptotic statement about a sparse set of `n`.

## 8. What is not done, and next steps

* **One-sided version (`Ω_-`, the Chebyshev-bias direction).** Claim: for `θ < 1/2`, and also in
  the log-power scale `√x/(log x)^A`, `A > 1`, there is no `C` with `S*(x) ≥ -C x^θ` (resp.
  `≥ -C √x/(log x)^A`) for all `x`. The proof via **Landau's theorem** on Mellin integrals of
  nonnegative functions is in §6.4; it needs no zeros of `L(s, χ)` (real zeros only help). Not
  formalized: Mathlib has no Landau (Pringsheim-type) theorem for Dirichlet series or Mellin
  integrals with nonnegative coefficients; that theorem is the missing ingredient. The `Ω_+`
  direction is genuinely harder: it needs a nonreal zero of `L(s, χ)` with real part `≥ 1/2` and
  Landau's twisted-kernel argument (§6.4), as in Littlewood/Ingham.
* **Below `√x/(log x)^{1+ε}`.** `S*(x) ≠ O(√x/log x)` (and Littlewood's `log log log x`) is out of
  reach of any argument that sees only the singularity at `1/2` (§6.3).
* **Sign changes.** Infinitely many sign changes of `S` need either Littlewood's method (explicit
  formula + Dirichlet approximation on the `γ`) or Landau's theorem combined with a zero of
  `L(s, χ)` off the real axis on or near `re s = 1/2`. Both are well beyond the current Mathlib
  infrastructure (no explicit formula for `ψ(x, χ)`).
* **Other residue constants.** The digit corollary is stated for `χ₄` only; the analogous
  statements for the constants of `General/Expansion.lean` and `General/ResidueConstant.lean`
  should follow from the general theorem in the same way (not stated here).


> **Update.** Landau's theorem is now formalized (`RokickiConstant/General/Landau.lean`), and with it the one-sided `Ω₋` result of §6.4: see `research/landau.md`.
