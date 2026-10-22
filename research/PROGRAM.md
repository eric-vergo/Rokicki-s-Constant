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
