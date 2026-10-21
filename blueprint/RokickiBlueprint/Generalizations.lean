/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint
import RokickiConstant.General.Irrational
import RokickiConstant.General.Normal
import RokickiConstant.General.ResidueConstant

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Generalizations" =>

%%%
tag := "chapter-generalizations"
%%%

Nothing in the proof used the modulus $`4` beyond the single identity $`\chi_4(p)^2 = 1`, and
nothing used the base $`2` beyond the fact that digits are read in some base. This chapter
records the general statements: for every *quadratic* Dirichlet character $`\chi` modulo $`q`,
that is, one with values in $`\{0, 1, -1\}`, and every base $`b \geq 2`. Throughout,
$`p_0 = 2 < p_1 = 3 < \cdots` are all the primes (in Lean, `Nat.nth Nat.Prime k`), and
$`S(n) = \sum_{k<n} \chi(p_k)`.

# Expansions in any base

:::theorem "general_eventually_periodic_of_rational" (lean := "eventuallyPeriodic_of_tsum_div_pow_mem_range_ratCast") (uses := "eventually_periodic")
Let $`b \geq 2` and let $`d : \mathbb{N} \to \{0, \ldots, b-1\}`. If $`\sum_k d_k / b^{k+1}` is
rational then $`d` is eventually periodic with some period $`p > 0`.
:::

:::proof "general_eventually_periodic_of_rational" (uses := "eventually_periodic_of_rational")
The tail argument of {ref "chapter-binary-expansion"}[Chapter 3] with $`2` replaced by $`b`:
the tails satisfy $`T(n+1) = b\,T(n) - d_n` and lie in $`[0, 1]`; two equal tails that continue
with different digits would have next tails differing by a nonzero integer, forcing one of them
to be $`1` (all later digits $`b-1`) and the other $`0` (all later digits $`0`), which is absurd.
:::

:::theorem "general_irrational_of_not_periodic" (lean := "irrational_tsum_div_pow") (uses := "eventually_periodic")
If $`d : \mathbb{N} \to \{0, \ldots, b-1\}` is not eventually periodic, then $`\sum_k d_k / b^{k+1}`
is irrational.
:::

:::proof "general_irrational_of_not_periodic" (uses := "general_eventually_periodic_of_rational")
Contrapositive.
:::

# The Euler product for an arbitrary character

:::definition "general_prime_term" (lean := "DirichletCharacter.primeTerm")
$`z_k(s) = \chi(p_k)\, p_k^{-s}`.
:::

:::definition "general_parts" (lean := "DirichletCharacter.primePart, DirichletCharacter.primePowerPart") (uses := "general_prime_term")
$`G_\chi(s) = \sum_k z_k(s)` and $`H_\chi(s) = \sum_k \big( -\log(1 - z_k(s)) - z_k(s) \big)`.
:::

:::theorem "general_euler_product" (lean := "DirichletCharacter.exp_primePart_add_primePowerPart") (uses := "general_parts")
For every Dirichlet character $`\chi` and $`\operatorname{Re} s > 1`,
$`\exp\big( G_\chi(s) + H_\chi(s) \big) = L(s, \chi)`.
:::

:::proof "general_euler_product" (uses := "euler_product, log_tail_bounds")
As in {ref "chapter-euler-product"}[Chapter 5], now over all primes: the Euler product of
Mathlib, reindexed along $`k \mapsto p_k`, and split termwise.
:::

:::theorem "general_prime_power_part_analytic" (lean := "DirichletCharacter.differentiableOn_primePowerPart, DirichletCharacter.exists_norm_primePowerPart_le") (uses := "general_parts")
For every Dirichlet character $`\chi`, $`H_\chi` is holomorphic on $`\operatorname{Re} s > 1/2` and
bounded on $`\operatorname{Re} s \geq 1`.
:::

:::proof "general_prime_power_part_analytic" (uses := "log_tail_bounds, prime_power_part_holomorphic, prime_power_part_bounded")
Since $`|z_k(s)| \leq p_k^{-\operatorname{Re} s} \leq 2^{-1/2} < 3/4` for $`\operatorname{Re} s > 1/2`, the
$`k`-th term of $`H_\chi` is bounded by $`2 p_k^{-2\sigma_0}` on $`\operatorname{Re} s \geq \sigma_0`,
and the argument of Chapter 5 applies verbatim.
:::

:::theorem "general_blowup" (lean := "DirichletCharacter.IsQuadratic.le_re_primePowerPart, DirichletCharacter.IsQuadratic.tendsto_re_primePowerPart") (uses := "general_parts")
If $`\chi` is quadratic, then $`\operatorname{Re} H_\chi(\sigma) \to +\infty` as real
$`\sigma \to 1/2^+`.
:::

:::proof "general_blowup" (uses := "prime_power_part_lower, prime_power_part_blowup, tendsto_prime_sum")
For $`p_k \nmid q` one has $`\chi(p_k)^2 = 1`, so the $`k`-th term of $`H_\chi(\sigma)` is at least
$`p_k^{-2\sigma}/2 - 2 p_k^{-3/2}`; for the finitely many $`p_k \mid q` the term vanishes and
$`p_k^{-2\sigma}/2 \leq 1/2`. Hence
$`\operatorname{Re} H_\chi(\sigma) \geq \tfrac12 \sum_k p_k^{-2\sigma} - \tfrac12 \omega(q) - 2 \sum_k p_k^{-3/2}`,
where $`\omega(q)` is the number of prime factors of $`q`, and $`\sum_k p_k^{-2\sigma} \to \infty`.
:::

# The general theorem

:::theorem "general_not_linear" (lean := "DirichletCharacter.IsQuadratic.not_exists_norm_sum_sub_mul_le, DirichletCharacter.IsQuadratic.not_exists_norm_sum_primesBelow_sub_mul_le")
Let $`\chi` be a nonprincipal quadratic Dirichlet character. Then $`S(n)` is not of the form
$`c\,n + O(1)` with $`c \neq 0`; equivalently, $`\sum_{p < x} \chi(p)` is not $`c\,\pi(x) + O(1)`
with $`c \neq 0`.
:::

:::proof "general_not_linear" (uses := "not_linear, general_euler_product, general_prime_power_part_analytic, by_parts_bound")
The proof of {ref "chapter-character-sums"}[Chapter 6] with $`\chi_4` replaced by $`\chi`: as
$`\sigma \to 1^+`, $`\operatorname{Re} G_\chi(\sigma) = c \sum_k p_k^{-\sigma} + O(1) \to \pm\infty` while
$`H_\chi` stays bounded, contradicting $`L(1, \chi) \neq 0`.
:::

:::theorem "general_not_bounded" (lean := "DirichletCharacter.IsQuadratic.not_exists_norm_sum_le, DirichletCharacter.IsQuadratic.not_exists_norm_sum_primesBelow_le")
Let $`\chi` be a nonprincipal quadratic Dirichlet character. Then $`S(n)` is unbounded;
equivalently, $`\sum_{p < x} \chi(p)` is unbounded.
:::

:::proof "general_not_bounded" (uses := "not_bounded, general_euler_product, general_prime_power_part_analytic, general_blowup, abel_series_holomorphic, abel_series_eq")
Bounded partial sums continue $`G_\chi` holomorphically to $`\operatorname{Re} s > 0` through the Abel
series; the identity theorem extends the Euler product to $`\operatorname{Re} s > 1/2`; and the
blow-up of $`\operatorname{Re} H_\chi` at $`1/2` contradicts the continuity of the entire function
$`L(\cdot, \chi)`.
:::

# Irrational numbers from quadratic characters

:::theorem "general_irrational" (lean := "DirichletCharacter.IsQuadratic.irrational_tsum") (uses := "eventually_periodic")
Let $`\chi` be a nonprincipal quadratic Dirichlet character, $`b \geq 2`, and let $`f` encode the
values of $`\chi` as digits $`f(z) < b` with $`f(1) \neq f(-1)`. Then
$$`\sum_{k \geq 0} \frac{f(\chi(p_k))}{b^{k+1}}`
is irrational.
:::

:::proof "general_irrational" (uses := "general_irrational_of_not_periodic, general_not_linear, general_not_bounded, periodic_partial_sums")
If the digits were eventually periodic, so would be $`k \mapsto \chi(p_k)`: the two sequences
determine each other once $`p_k \nmid q`, which holds for all large $`k`. Then $`S(n) = c\,n + O(1)`,
which contradicts the general theorem whether $`c = 0` or not.
:::

:::theorem "rokicki_any_base" (lean := "Real.irrational_rokickiConstantBase") (uses := "digit")
For every base $`b \geq 2`, the number $`\rho_b = \sum_k d_k / b^{k+1}` with Rokicki's digits
$`d_k = [p_{k+2} \equiv 3 \pmod 4]` is irrational. For $`b = 2` this is Rokicki's constant.
:::

:::proof "rokicki_any_base" (uses := "general_irrational_of_not_periodic, main")
The digit sequence is not eventually periodic (this is the content of
{ref "chapter-main-theorem"}[Chapter 7]), and the base plays no role.
:::

:::theorem "legendre_constant" (lean := "Real.irrational_legendreConstant")
Let $`\ell` be an odd prime and $`b \geq 2`. The number whose $`k`-th base-$`b` digit is $`1` if
$`p_k` is a quadratic non-residue modulo $`\ell` and $`0` otherwise is irrational.
:::

:::proof "legendre_constant" (uses := "general_irrational")
Apply the general theorem to the Legendre symbol modulo $`\ell`, which is a nonprincipal
quadratic character for $`\ell \neq 2`.
:::

:::theorem "exists_quadratic_character" (lean := "DirichletCharacter.exists_isQuadratic_ne_one")
Every modulus $`q \geq 3` carries a nonprincipal quadratic Dirichlet character.
:::

:::proof "exists_quadratic_character"
If $`q` has an odd prime factor $`\ell`, lift the Legendre symbol modulo $`\ell` to level $`q`;
otherwise $`q` is a power of $`2` with $`4 \mid q`, and lift $`\chi_4`. Lifting preserves both
properties.
:::

:::theorem "residue_constant" (lean := "Real.irrational_residueConstant")
For every $`q \geq 3` and base $`b > q`, the number whose $`k`-th base-$`b` digit is the residue
$`p_k \bmod q` is irrational.
:::

:::proof "residue_constant" (uses := "exists_quadratic_character, general_irrational_of_not_periodic, general_not_linear, general_not_bounded, periodic_partial_sums")
Eventually periodic digits would make the residues $`p_k \bmod q` eventually periodic, hence
the values $`\chi(p_k)` of the character of the previous theorem, which contradicts the general
theorem as before.
:::

# Conditional normality

:::definition "is_normal" (lean := "_root_.wordCount, IsNormalSeq, Real.IsNormal")
A digit sequence over $`\{0, \ldots, b-1\}` is *normal* if every word of length $`L` occurs with
limiting frequency $`b^{-L}` (overlapping count). A real number in $`[0, 1]` is normal in base
$`b` if it has a normal base-$`b` digit expansion; such an expansion is never eventually
constant, so it is the canonical one and this is Borel's definition.
:::

:::definition "consecutive_primes_equidistributed" (lean := "ConsecutivePrimesEquidistributed")
The *equidistribution conjecture* modulo $`q`: for every word $`a` of units modulo $`q`, the
proportion of $`m < n` with $`p_{m+i} \equiv a_i \pmod q` for all $`i < L` tends to
$`\varphi(q)^{-L}`. It follows from the Hardy–Littlewood prime tuples conjecture
(Lemke Oliver–Soundararajan, 2016) and is open for every $`q \geq 3`.
:::

:::theorem "conditional_normality" (lean := "Real.isNormal_rokickiConstant_of_consecutivePrimesEquidistributed") (uses := "is_normal, consecutive_primes_equidistributed, rokicki_constant")
If the residue patterns of consecutive primes modulo $`4` are equidistributed, then Rokicki's
constant is normal in base $`2`.
:::

:::proof "conditional_normality" (uses := "digit")
A word $`w` of digits occurs at position $`m` exactly when the odd primes $`p_{m+2}, \ldots, p_{m+L+1}`
have the residues prescribed by $`w`; the two counts differ by the shift of one index, which does
not affect frequencies, and $`\varphi(4) = 2`.
:::
