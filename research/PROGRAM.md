# Research program: four orthogonal directions

Where things stand. Rokicki's constant `ρ` is irrational (formalized), because the partial
sums `S(n) = Σ_{k<n} χ₄(p_k)` are neither bounded nor `c·n + O(1)`; the same holds for every
nonprincipal quadratic character (formalized); the digits read in any base, the Legendre
constants and the residue constants of every modulus `q ≥ 3` are irrational (formalized); `ρ` is
normal in base `2` if consecutive-prime residue patterns are equidistributed (formalized
implication); transcendence is open and no known method applies (`transcendence.md`).

The question "is `ρ` transcendental" has four independent axes along which the framework can
still be pushed. Each is a separate line of work with its own deliverable.

## Direction 1: the character. Characters of higher order

The two contradictions used `χ(p)² = 1`. For a character `χ` of order `m`, the logarithm of the
Euler product is `Σ_{j≥1} G_{χ^j}(js)/j` with `G_ψ(s) = Σ_p ψ(p) p^{-s}`. If `S_χ` is bounded then
`G_χ` and `G_{χ̄}` continue to `re s > 0`, and the `j = m` term `G_{χ^m}(ms) = Σ_{p∤q} p^{-ms}/m`
blows up as `s → 1/m⁺`. For `m = 3` the only other term, `j = 2`, is `G_{χ̄}(2s)/2`, also
continued; the identity theorem then applies on `re s > 1/3` and the blow-up at `1/3`
contradicts the entire `L(·, χ)`. So **the partial sums of a character of order 3 are
unbounded**, and for every order the linear case `S = c·n + O(1)`, `c ≠ 0` (now complex `c`), is
ruled out at `s → 1⁺` through both `|L|` and `arg L`. For `m ≥ 4` the method needs the
continuation of `G_{χ^j}` for `j` coprime to `m` other than `±1`, which bounded `S_χ` alone does
not give: a "simultaneous" statement remains. Deliverables: Lean formalization of the order-3
theorem and of the all-orders linear case; a note on `m ≥ 4`; corollary: the "cubic residue
constants" (digits recording the cubic character of `p_k` modulo a prime `≡ 1 (mod 3)`) are
irrational.

## Direction 2: the rate. Quantitative oscillation

The bounded case only used that the Abel series converges on `re s > 0`. If `|S(n)| ≤ C n^θ`
with `θ < 1/2`, the Abel series converges on `re s > θ`, the identity theorem still applies on
`re s > 1/2`, and the blow-up at `1/2` gives the same contradiction. So
**`S(n) ≠ O(n^{1/2-ε})` for every `ε > 0`**, i.e. `Σ_{p≤x} χ(p) = Ω(x^{1/2-ε})` for every
nonprincipal quadratic `χ`, without the prime number theorem. For `ρ` this says the imbalance
`#{1s} − #{0s}` among the first `n` digits is not `O(n^{1/2-ε})`. Deliverables: Lean
formalization (generalize `abelSeries` to polynomially bounded partial sums); a note placing
this against the classical `Ω(x^{1/2} log log log x / log x)` of Littlewood and the Chebyshev-bias
picture of Rubinstein–Sarnak; what a *lower* bound `S(n) = O(n^{1/2+ε})` would need (zeros of
`L(s, χ)`, i.e. GRH).

## Direction 3: the Diophantine side. Approximation exponent

Good rational approximations to `ρ` are periodic stretches in the binary digits, i.e. periodic
residue patterns over stretches of consecutive primes. The dyadic case is runs of congruent
primes: Breusch's Bertrand postulate for `4k+3` gives runs of length `O(position)` and hence
`|ρ − a/2^m| ≥ 2^{-Cm}` (no dyadic Liouville behaviour); short-interval results give
`m^{7/12+ε}`. For general denominators nothing is proved. Deliverables: certified statistics of
periodic stretches (all periods `P ≤ 64`) in `10^7` digits versus the random model, as evidence
for `μ(ρ) = 2`; a precise formulation of the run-length theorem with its exact inputs; an
assessment of what it would take to formalize Breusch (Mathlib has Bertrand's postulate but not
its arithmetic-progression version) and of Chebyshev bounds available in Mathlib; if feasible,
a Lean theorem *conditional on Breusch* giving the dyadic bound.

## Direction 4: the sequence. What replaces the primes

The method needs an `L`-function behind the sequence. Which other sequences `a_k` give
irrational, or transcendental, constants `Σ [a_k ≡ 3 (mod 4)] 2^{-k}`? Candidates: primes in an
arithmetic progression, prime ideals of a number field (Hecke characters), sums of two squares
(governed by `χ₄` through Landau), squarefree numbers (Möbius), Beatty sequences `⌊kα⌋` (Sturmian
digits: transcendental by Adamczewski–Bugeaud, but via the Subspace theorem), lacunary
placements. Mathlib's Liouville theory gives the one transcendental case within formal reach:
placing Rokicki's digits at factorial positions, `Σ b_k 2^{-k!}`, yields a Liouville number
(`Liouville.transcendental`), which shows that what blocks transcendence for `ρ` is the dense
placement, not the digits. Deliverables: a classification note; Lean formalization of the
Liouville variant; identification of the next sequence for which the character-sum method
transfers verbatim (primes in a progression, or Gaussian primes).

## How the four fit together

| Direction | Axis varied | Changes `ρ`? | Changes the method? | Formal target |
|---|---|---|---|---|
| 1 | the character | no (new constants) | yes: higher-order Euler product terms | order-3 theorem |
| 2 | the rate | no | yes: polynomial growth in the Abel series | `Ω(n^{1/2-ε})` |
| 3 | approximation | no | no: new input (Bertrand in APs) | conditional dyadic bound |
| 4 | the sequence | yes (new constants) | no: same method, new `L`-functions | Liouville variant |

Directions 1 and 2 are run first (both are extensions of the formal development and touch the
same analytic core); directions 3 and 4 second (both open outward, to Diophantine approximation
and to other sequences). Each produces a note in `research/` and, where marked, Lean under
`RokickiConstant/General/`.

## Outcomes (first round)

| Direction | Formalized (Lean, no sorry, standard axioms) | Note |
|---|---|---|
| 1 | `DirichletCharacter.not_exists_norm_sum_sub_mul_le` (linear case, every nonprincipal `χ`, complex slope); `not_exists_norm_sum_le_of_pow_three` (order 3: unbounded, even the real parts); `Real.irrational_cubicResidueConstant`; simultaneous theorem `not_forall_exists_norm_sum_pow_le` for order `m` | `higher-order.md`: why `m ≥ 4` needs zeros of `L(·, χ^j)`; conditional theorem for squarefree `m`; cancellation for `m = 4, 8, 9` |
| 2 | `IsQuadratic.not_isBigO_rpow_one_half_sub` and the `x`-scale `not_isBigO_primesBelow_rpow`; `RokickiConstant.not_isBigO_card_rokickiDigit_rpow` | `oscillation.md`: exponent `1/2` is the edge of absolute convergence of `χ²`; upper bounds are GRH; one-sided `Ω₋` would need Landau's theorem |
| 3 | `Nat.primeCounting_two_mul_le` (`π(2x) ≤ 28 π(x)`, unconditional); `one_div_two_pow_le_abs_tsum_sub_div_two_pow` (digits vs dyadic approximation); conditional on `BreuschFour`: `|ρ − a/2^m| ≥ 2^{-(28m+55)}` | `diophantine.md`: exact reduction approximations ⇔ periodic stretches; evidence for `μ(ρ) = 2` along `2^n(2^P − 1)`; Breusch formalization estimated at 2000–4000 lines |
| 4 | `liouville_tsum_div_pow_factorial`; `Real.transcendental_rokickiLacunary` (Rokicki's digits at factorial positions) | `sequences.md`: classification of fifteen Rokicki-type constants; the method transfers exactly to progressions cut out by quadratic characters (the prime-square term) and fails where no prime square lies in the class |

Second-round candidates, by direction: (1) formalize the conditional `m ≥ 4` theorem, and
`S_χ ≠ O(n^{1/3-ε})` for cubic `χ`; (2) the one-sided `Ω₋` via Landau's theorem on Dirichlet
series with nonnegative coefficients (not in Mathlib); (3) prove `BreuschFour` in Lean, or `P`
consecutive congruent primes in every `(x, 2x]`; (4) primes in a quadratic progression with the
existing Euler-product file, and Hecke characters once Mathlib has them.

## Outcomes (second round, Direction 2)

| Result | Lean |
|---|---|
| `Σ_{p<x} χ(p) ≠ O(√x/(log x)^A)` for `A > 1` (quadratic `χ`); index scale `A > 1/2`; digit imbalance of `ρ` likewise | `IsQuadratic.not_isBigO_primesBelow_rpow_div_log_rpow`, `not_isBigO_rpow_div_log_rpow`, `RokickiConstant.not_isBigO_card_rokickiDigit_rpow_div_log_rpow` |
| `S_χ ≠ O(n^{1/3-ε})` for `χ` of order 3, both scales; the bounded case is now the `θ = 0` instance of a `θ`-parametrized engine | `not_isBigO_rpow_one_third_sub_of_pow_three`, `not_isBigO_primesBelow_rpow_of_pow_three` |

Where Direction 2 stops: the dominating series diverges at `A = 1`, and `O(√x/log x)` cannot be
excluded by this method (the prime-square singularity is the Mellin transform of
`−½π(√x) ≈ −√x/log x`). The next step is sign-sensitive: `Ω₋(√x/(log x)^A)`, the Chebyshev-bias
direction, follows from Landau's theorem on Mellin transforms of nonnegative functions (not in
Mathlib; a self-contained formalization is the natural next task), while `Ω₊` needs a nonreal
zero of `L(s, χ)` with real part `≥ 1/2` and a twisted kernel (Ingham, Ch. V).

## Outcomes (third round, Direction 4)

| Result | Lean / note |
|---|---|
| **Single-class theorem**: for every `q ≥ 3` and every unit `a`, `[p_k ≡ a (mod q)]` is not eventually periodic, so `Σ [p_k ≡ a]/b^(k+1)` is irrational in every base; a third proof for `ρ` (`classConstant 4 3 2 = ρ/2`). New mechanism: zeros of `L(·,χ)` at `1/2` contribute an algebraic integer `Σ χ̄(a) m_χ` to the `log(σ − 1/2)` coefficient, while the prime squares demand `(1 − ν(a))/2` with `ν(a)` even. | `Nat.not_eventuallyPeriodic_nthPrime_modEq`, `Real.irrational_classConstant`; `single-class.md` |
| Beatty sequences: `[⌊kα⌋ ≡ a (mod m)]` non-periodic for irrational `α`, rational for rational `α`; the constants are irrational (and transcendental by Adamczewski–Bugeaud, not formalizable) | `Int.not_eventuallyPeriodic_floor_mul_emod`, `Real.irrational_beattyConstant`; `beatty.md` |
| Squarefree numbers: every residue word mod 4 occurs among consecutive squarefree numbers (CRT + union bound); every squarefree residue constant is irrational | `Nat.exists_squarefreeNth_mod_four_eq`, `Real.irrational_squarefreeConstant`; `two-squares-squarefree.md` |
| Sums of two squares: the square and prime digits give irrational constants unconditionally; the parity digit conditionally on Landau's `B(x) ~ Kx/√log x` | `Real.irrational_sumTwoSq{Square,Prime}Constant`, `..._sumTwoSqParityConstant_of_landau` |
| Gaussian primes: the sector digit `[a ≡ 3 (mod 4)]` for `p = a² + b²` is `χ₈(p)·sgn(Re π₀)`, not a Dirichlet digit; its partial sums are biased positive with `S(x) ~ √x/(2π)` (two derivations), the race of Devin's Conjecture 1.2; irrationality open (needs infinitely many Hecke modes) | `gaussian-primes.md`, `scripts/gaussian_primes.py` |

Where the method transfers (now a theorem, not a heuristic): to any digit cut out by a *single
residue class* of the primes, by the integrality mechanism; to quadratic and cubic digits by the
prime-square and prime-cube terms; to rotation codings by Diophantine approximation; to
squarefree residues by sieve constructions. Where it does not: digits that are infinite
combinations of Hecke modes (the Gaussian sector digit), and unions of residue classes with
`ν(A) = |A|`.

## Round 4 (Claude's choice): sign, parity, rates, elliptic curves

The engine behind every result on this branch is the singularity that the prime squares create
at `s = 1/2`, together with integrality of the contribution of zeros at `1/2`. Four things it
has not yet been asked to do:

1. **Sign** (`General/Landau.lean`, `research/landau.md`). Landau's theorem: a Dirichlet series
   or Mellin transform with nonnegative coefficients has a singularity at its abscissa of
   convergence. With it, positivity plus the prime-square term gives the one-sided
   `Σ_{p<x} χ(p) = Ω₋(√x/(log x)^A)` for quadratic `χ`: the Chebyshev bias *direction*, with no
   zeros and no prime number theorem.
2. **Parity** (`General/Unions.lean`, `research/unions.md`). For a union `A` of unit classes
   modulo `q`, the single-class mechanism gives `x = (|A| − ν(A))/2` with `ν(A)` even. So
   `[p_k mod q ∈ A]` is non-periodic unconditionally when `|A|` is odd, and when `|A|` is even
   and `ν(A) ≠ |A|` the statement is equivalent to a constraint on central zeros: it holds if
   `L(1/2, χ) ≠ 0` for all `χ` mod `q` (Chowla's conjecture).
3. **Rates for a single class** (`General/SingleClassRate.lean`): `π(x; q, a) − π(x)/φ(q)` is
   not `O(√x/(log x)^A)`, `A > 1`, by crossing the flagship with the log-power Abel series.
4. **Elliptic curves** (`research/elliptic.md`, `scripts/elliptic.py`): the digit
   `[a_p(E) < 0]` for CM and non-CM curves, the biases of its partial sums (`√x/(2π)`-type for
   `y² = x³ + x`; Chebyshev-type expected otherwise), irrationality status, and a precise
   conjecture.

## Outcomes (round 4)

| Result | Lean / note |
|---|---|
| **Landau's theorem** (Laplace/Mellin and Dirichlet-series forms) and the **direction of the Chebyshev bias**: `Σ_{p<x} χ(p) < −C√x/(log x)^A` infinitely often for every `C`, `A > 1`, quadratic `χ`; no zeros used, Siegel zeros covered; for `ρ`, ones outnumber zeros by more than `C√n/(log n)^A` infinitely often | `exists_lt_integrable_exp_neg_mul`, `IsQuadratic.frequently_re_sum_primesBelow_lt_rpow_div_log_rpow`; `landau.md` |
| **Parity dichotomy** for unions `A`: the multiplicity relation `Σ c_χ m_χ = (|A| − ν(A))/2`; unconditional for odd `|A|` and by positivity for pairs `{1, a}`, `a` a square; under Chowla for even `|A|` with `ν(A) ≠ |A|`; silent iff `ν(A) = |A|` | `Nat.not_eventuallyPeriodic_nthPrime_mem_of_odd`, `…_of_chowla`; `unions.md` |
| **Rates**: `π(x; q, a) − π(x)/φ(q) ≠ O(√x/(log x)^β)` for `β > 1`, every class and every odd union; one-sided version only conditional (real zeros have mixed-sign weights for a single class) | `Nat.not_isBigO_card_primesBelow_modEq_sub_rpow_div_log_rpow`; `single-class-rate.md` |
| **Elliptic curves**: see `elliptic.md` | numerics and conjectures |
