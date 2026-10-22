/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint
import RokickiConstant.General.HigherOrder
import RokickiConstant.General.Oscillation
import RokickiConstant.General.Diophantine
import RokickiConstant.General.Lacunary
import RokickiConstant.General.SingleClass
import RokickiConstant.General.Beatty
import RokickiConstant.General.TwoSquares

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Research directions" =>

%%%
tag := "chapter-research"
%%%

This chapter records the headline theorems of the research program (`research/PROGRAM.md`), one
section per direction. Only the main statements are listed; the supporting lemmas are in the
Lean files.

# The character: higher order

:::theorem "linear_any_order" (lean := "DirichletCharacter.not_exists_norm_sum_sub_mul_le")
For every nonprincipal Dirichlet character $`\chi` and every complex $`c \neq 0`, the partial
sums $`S(n) = \sum_{k<n} \chi(p_k)` are not of the form $`c\,n + O(1)`.
:::

:::proof "linear_any_order" (uses := "general_euler_product, general_prime_power_part_analytic")
As $`\sigma \to 1^+`, $`G_\chi(\sigma) = c \sum_k p_k^{-\sigma} + O(1)` while $`\|G_\chi(\sigma)\|`
stays bounded because $`\log L(\cdot, \chi)` has the continuous derivative $`L'/L` on
$`[1, 2]` ($`L` is entire with no zeros on $`\operatorname{Re} s \geq 1`).
:::

:::theorem "order_three" (lean := "DirichletCharacter.not_exists_norm_sum_le_of_pow_three")
For every nonprincipal Dirichlet character $`\chi` with $`\chi^3 = 1`, the partial sums $`S(n)`
are unbounded.
:::

:::proof "order_three" (uses := "general_euler_product, general_not_bounded, abel_series_holomorphic")
With $`S_\chi` bounded, $`G_\chi` and $`G_{\bar\chi} = G_{\chi^2}` continue to
$`\operatorname{Re} s > 0`, so $`\log L(s, \chi) = G_\chi(s) + \tfrac12 G_{\chi^2}(2s) + \tfrac13 \sum_{p \nmid q} p^{-3s} + (\text{tail})`
holds on $`\operatorname{Re} s > 1/3` by the identity theorem; the third term tends to $`+\infty` as
$`s \to 1/3^+`, contradicting continuity of $`L(\cdot, \chi)` at $`1/3`.
:::

:::theorem "cubic_residue_constant" (lean := "Real.irrational_cubicResidueConstant") (uses := "general_irrational_of_not_periodic")
For a prime $`\ell \equiv 1 \pmod 3` and a base $`b \geq 2`, the number whose $`k`-th digit
records whether $`p_k` is a nonzero cube modulo $`\ell` is irrational.
:::

:::proof "cubic_residue_constant" (uses := "linear_any_order, order_three")
Apply the two theorems to a cubic character modulo $`\ell`, which exists since
$`(\mathbb{Z}/\ell)^\times` is cyclic of order divisible by $`3`.
:::

# The rate: quantitative oscillation

:::theorem "oscillation" (lean := "DirichletCharacter.IsQuadratic.not_isBigO_rpow_one_half_sub, DirichletCharacter.IsQuadratic.not_isBigO_primesBelow_rpow")
For every nonprincipal quadratic $`\chi` and every $`\varepsilon > 0`,
$`S(n) \neq O(n^{1/2 - \varepsilon})`; equivalently $`\sum_{p < x} \chi(p) \neq O(x^{1/2-\varepsilon})`.
:::

:::proof "oscillation" (uses := "general_not_bounded, abel_series_holomorphic, general_blowup")
If $`|S(n)| \leq C n^\theta` with $`\theta < 1/2`, the Abel series converges on
$`\operatorname{Re} s > \theta` (the term bounds telescope after the elementary inequality
$`x^\theta (x^{-\delta} - y^{-\delta}) \leq \tfrac{\delta}{\delta - \theta}(x^{\theta-\delta} - y^{\theta - \delta})`),
so the identity theorem and the blow-up at $`1/2` apply exactly as in the bounded case.
:::

:::theorem "digit_imbalance" (lean := "RokickiConstant.not_isBigO_card_rokickiDigit_rpow") (uses := "digit")
For every $`\theta < 1/2`, the imbalance between the numbers of zeros and ones among the first
$`n` binary digits of $`\rho` is not $`O(n^\theta)`.
:::

:::proof "digit_imbalance" (uses := "oscillation, chi4_odd_prime_int")
The imbalance is $`-S(n)` for $`\chi_4` up to the index shift.
:::

:::theorem "oscillation_log" (lean := "DirichletCharacter.IsQuadratic.not_isBigO_primesBelow_rpow_div_log_rpow, DirichletCharacter.IsQuadratic.not_isBigO_rpow_div_log_rpow")
For every nonprincipal quadratic $`\chi`: $`\sum_{p<x} \chi(p) \neq O(\sqrt{x}/(\log x)^A)` for every
$`A > 1`, and $`S(n) \neq O(\sqrt{n}/(\log n)^A)` for every $`A > 1/2`. This is within a factor
$`(\log x)^{\varepsilon}` of Littlewood's $`\Omega_\pm(\sqrt{x} \log\log\log x / \log x)`, with no
explicit formula and no prime number theorem.
:::

:::proof "oscillation_log" (uses := "oscillation, chebyshev_doubling")
On the closed half-plane $`\operatorname{Re} s \geq 1/2` the Abel series is dominated by
$`\sum_k (p_{k+1} - p_k)/(p_k (\log p_k)^A)`, which converges for $`A > 1` (Bertrand's postulate
and the antitone function $`(\log t)^{1-A}`), so the series is continuous up to the line and
the contradiction at $`1/2` goes through. Chebyshev's bounds convert between the two scales.
:::

:::theorem "cubic_rate" (lean := "DirichletCharacter.not_isBigO_rpow_one_third_sub_of_pow_three, DirichletCharacter.not_isBigO_primesBelow_rpow_of_pow_three")
For every nonprincipal $`\chi` with $`\chi^3 = 1` and every $`\varepsilon > 0`,
$`S(n) \neq O(n^{1/3 - \varepsilon})`.
:::

:::proof "cubic_rate" (uses := "order_three, oscillation")
The order-3 argument with the polynomial-growth Abel series: a bound $`|S(n)| \leq C n^\theta`
with $`\theta < 1/3` continues $`G_\chi` and $`G_{\bar\chi}` to $`\operatorname{Re} s > \theta`, and the
blow-up of $`\tfrac13 \sum_{p \nmid q} p^{-3s}` at $`1/3` gives the contradiction.
:::

# The Diophantine side

:::theorem "chebyshev_doubling" (lean := "Nat.primeCounting_two_mul_le")
$`\pi(2x) \leq 28\,\pi(x)` for all $`x \geq 6`.
:::

:::proof "chebyshev_doubling"
Mathlib's explicit Chebyshev bounds $`\pi(x) \leq (\log 4)\, x / \log x` and
$`\pi(x) \geq (\log 2 / 2)\, x / \log x`-type estimates.
:::

:::theorem "dyadic_bound" (lean := "RokickiConstant.one_div_two_pow_le_abs_rokickiConstant_sub_of_breuschFour") (uses := "rokicki_constant")
Assume Breusch's Bertrand postulate for the classes $`1` and $`3` modulo $`4`: for $`x \geq 7`
each class contains a prime in $`(x, 2x]`. Then $`|\rho - a/2^m| \geq 2^{-(28m+55)}` for all
integers $`a` and $`m`; in particular $`\rho` admits no Liouville-type dyadic approximations.
:::

:::proof "dyadic_bound" (uses := "chebyshev_doubling, binary_tail_basic")
A run of equal digits starting at index $`n` ends within $`\pi(2p_{n+2}) - \pi(p_{n+2}) \leq 27(n+2)`
digits by Breusch and the doubling bound; a non-constant block in positions $`m, \ldots, m+L`
separates $`\rho` from every $`a/2^m` by at least $`2^{-(m+L+1)}`.
:::

# The sequence: lacunary placement

:::theorem "liouville_lacunary" (lean := "liouville_tsum_div_pow_factorial")
For a base $`m \geq 2` and binary digits $`d_k` with infinitely many ones,
$`\sum_k d_k / m^{k!}` is a Liouville number.
:::

:::proof "liouville_lacunary"
The partial sums are rationals with denominator $`m^{N!}` and the tail is at most
$`2 m^{-(N+1)!}`, positive infinitely often; this is Mathlib's argument for the Liouville
constant with $`0/1` coefficients.
:::

:::theorem "rokicki_lacunary" (lean := "Real.transcendental_rokickiLacunary") (uses := "digit")
Rokicki's digits placed at the factorial positions, $`\sum_k d_k / 2^{(k+1)!}`, give a
transcendental number.
:::

:::proof "rokicki_lacunary" (uses := "liouville_lacunary")
Infinitely many primes are $`3` modulo $`4`, so infinitely many digits are $`1`; Liouville
numbers are transcendental. What blocks transcendence for $`\rho` itself is the dense placement
of the same digits, not the digits.
:::

# The sequence: a single residue class

:::theorem "single_class" (lean := "Nat.not_eventuallyPeriodic_nthPrime_modEq, Real.irrational_classConstant")
For every modulus $`q \geq 3` and every $`a` coprime to $`q`, the indicator sequence
$`[p_k \equiv a \pmod q]` of a single residue class is not eventually periodic; hence the number
whose $`k`-th base-$`b` digit is this indicator is irrational, for every $`b \geq 2`.
:::

:::proof "single_class" (uses := "general_euler_product, general_prime_power_part_analytic, abel_series_holomorphic, general_irrational_of_not_periodic, periodic_partial_sums")
Periodicity forces $`\#\{k<n : p_k \equiv a\} = c\,n + O(1)`; the nonvanishing of every
$`L(1,\chi)` forces $`c = 1/\varphi(q)` (Dirichlet density, without the prime number theorem).
Then $`\Phi = \sum_{\chi \neq 1} \bar\chi(a)(G_\chi + H_\chi)` continues to
$`\operatorname{Re} s > 1/2`, with $`(\prod_\chi L_\chi)\,\Phi' = \sum_\chi \bar\chi(a) L_\chi' \prod_{\psi \neq \chi} L_\psi`
there by the identity theorem. Near $`1/2` on the real axis,
$`\Phi(\sigma) = x \log(\sigma - 1/2) + O(1)` with $`x = \sum_\chi \bar\chi(a)\, m_\chi`, where $`m_\chi`
is the order of vanishing of $`L(\cdot,\chi)` at $`1/2`; the prime squares give instead
$`\Phi(\sigma) = \tfrac{1-\nu}{2} \log(\sigma - 1/2) + O(1)` with $`\nu` the number of square roots
of $`a` modulo $`q`. So $`x = (1-\nu)/2`. But $`x` is an algebraic integer and $`\nu` is even for
$`q \geq 3`: no configuration of zeros at $`1/2` can rescue periodicity.
:::

:::theorem "rokicki_third_proof" (lean := "Real.classConstant_four_three_two, Real.irrational_rokickiConstant''") (uses := "rokicki_constant")
The single-class constant of $`q = 4`, $`a = 3` in base $`2` equals $`\rho/2`; this gives a
third proof that Rokicki's constant is irrational.
:::

:::proof "rokicki_third_proof" (uses := "single_class")
The term $`k = 0` vanishes ($`p_0 = 2`) and the remaining digits are Rokicki's digits shifted by
one position.
:::

# The sequence: Beatty sequences

:::theorem "beatty" (lean := "Int.not_eventuallyPeriodic_floor_mul_emod, Real.irrational_beattyConstant")
For irrational $`\alpha`, $`m \geq 2` and any residue $`a`, the digits $`[\lfloor k\alpha \rfloor \equiv a \pmod m]`
are not eventually periodic, and the Beatty–Rokicki constant $`\sum_k d_k / b^{k+1}` is irrational
for every $`b \geq 2`; for rational $`\alpha` it is rational.
:::

:::proof "beatty" (uses := "general_irrational_of_not_periodic")
The digit is the coding of the rotation by $`\alpha/m` on the circle by an arc of length $`1/m`.
Along a progression $`N + tP` the rotation by $`P\alpha/m` is still irrational, so its orbit meets
every arc (Dirichlet's approximation theorem); hence the digit cannot be constant along the
progression, which eventual periodicity would require. These constants are in fact
transcendental by Adamczewski–Bugeaud, since the coding has linear subword complexity.
:::

# The sequence: squarefree numbers and sums of two squares

:::theorem "squarefree_patterns" (lean := "Nat.exists_squarefreeNth_mod_four_eq")
Every finite word over the residues $`\{1, 2, 3\}` modulo $`4` occurs, arbitrarily late, as the
residues of consecutive squarefree numbers.
:::

:::proof "squarefree_patterns"
By the Chinese remainder theorem, place the prescribed residues in an arithmetic progression
whose step is a square of a factorial, kill every other integer of the window by the square of
its own large prime, and bound the candidates lost to larger prime squares by a union bound
with $`\sum_{n > K} n^{-2} \leq 2/(K+1)`; half of the progression survives. This is an
elementary stand-in for Mirsky's pattern counts.
:::

:::theorem "squarefree_constant" (lean := "Nat.not_eventuallyPeriodic_squarefreeNth_mod_four, Real.irrational_squarefreeConstant") (uses := "general_irrational_of_not_periodic")
The residues modulo $`4` of the consecutive squarefree numbers are not eventually periodic, so
every constant whose digits distinguish two of the residues $`1, 2, 3` is irrational.
:::

:::proof "squarefree_constant" (uses := "squarefree_patterns")
An eventually periodic sequence with period $`P` has at most $`P` factors of each length, while
all $`3^L` words occur.
:::

:::theorem "two_squares_constants" (lean := "Real.irrational_sumTwoSqSquareConstant, Real.irrational_sumTwoSqPrimeConstant, Real.irrational_sumTwoSqParityConstant_of_landau") (uses := "general_irrational_of_not_periodic")
Over the sums of two squares $`s_0 < s_1 < \cdots`, the digits $`[s_k \text{ is a square}]` and
$`[s_k \text{ is prime}]` give irrational constants unconditionally; the parity digit
$`[s_k \text{ odd}]` gives an irrational constant assuming Landau's asymptotic
$`B(x) \sim K x / \sqrt{\log x}` for the counting function of sums of two squares.
:::

:::proof "two_squares_constants"
Arbitrarily long runs of the digit $`0` exist for the first two digits (no square between
consecutive squares; windows $`t^2 + 2, \ldots, t^2 + R` with $`R! \mid t` contain no prime), and the
digit $`1` recurs infinitely often (Fermat). For the parity digit, the self-similarity
$`2n \in S \Leftrightarrow n \in S` gives $`B(2n) = \#\{\text{odd } s \leq 2n\} + B(n)`, so periodicity
would force $`B(n) = (1-c) B(2n) + O(1)`; Landau's asymptotic forces $`c = 1/2` and then
$`B(2^j n_0) \geq 2^j`, contradicting density zero.
:::
