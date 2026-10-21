/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint
import RokickiConstant.CharacterSums

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The character sums are neither bounded nor linear" =>

%%%
tag := "chapter-character-sums"
%%%

Let $`S(n) = \sum_{k < n} \chi_4(q_k) \in \mathbb{Z}` be the partial sums of the character over
the odd primes. We show that $`S(n)` is not of the form $`c\,n + O(1)` with $`c \neq 0`, and that
$`S(n)` is not bounded. Both arguments start from the Euler product
$`\exp(G + H) = L(\cdot, \chi)` of {ref "chapter-euler-product"}[the previous chapter] and end
with the same observation: a function with a finite limit at a point cannot be bounded below by
a function tending to $`+\infty` there.

:::lemma_ "exp_re_limit" (lean := "RokickiConstant.tendsto_exp_re_of_exp_eq_LFunction") (uses := "chi4")
Let $`x \in \mathbb{R}` and let $`F` be a function with $`\exp(F(\sigma)) = L(\sigma, \chi)` for all
real $`\sigma > x`. Then $`\exp(\operatorname{Re} F(\sigma)) \to |L(x, \chi)|` as $`\sigma \to x^+`.
:::

:::proof "exp_re_limit" (uses := "chi4_basic")
$`|\exp w| = \exp(\operatorname{Re} w)`, and $`L(\cdot, \chi)` is continuous because it is entire,
$`\chi` being nontrivial.
:::

# The linear case

:::lemma_ "prime_part_linear" (lean := "RokickiConstant.abs_re_primePart_sub_mul_tsum_le") (uses := "prime_part, odd_prime")
If $`|S(n) - c\,n| \leq C` for all $`n`, then for real $`\sigma > 1`,
$$`\Big| \operatorname{Re} G(\sigma) - c \sum_k q_k^{-\sigma} \Big| \leq 2C.`
:::

:::proof "prime_part_linear" (uses := "by_parts_bound, chi4_odd_prime, prime_sums")
$`\operatorname{Re} G(\sigma) - c \sum_k q_k^{-\sigma} = \sum_k (\chi(q_k) - c)\, q_k^{-\sigma}`. The coefficients
$`\chi(q_k) - c` have partial sums bounded by $`C`, and $`q_k^{-\sigma}` is antitone and nonnegative
with first value $`3^{-\sigma} \leq 1`, so the summation by parts bound applies.
:::

:::theorem "not_linear" (lean := "RokickiConstant.not_exists_abs_sum_chi4_sub_mul_le") (uses := "chi4, odd_prime")
There are no real $`c \neq 0` and $`C` with $`|S(n) - c\,n| \leq C` for all $`n`.
:::

:::proof "not_linear" (uses := "prime_part_linear, euler_product, prime_power_part_bounded, tendsto_prime_sum, exp_re_limit")
Suppose there were. For real $`\sigma > 1` put $`F(\sigma) = G(\sigma) + H(\sigma)`, so that
$`\exp F(\sigma) = L(\sigma, \chi)` and $`\exp(\operatorname{Re} F(\sigma)) \to |L(1, \chi)|`, which is
positive because $`L(1, \chi) \neq 0`. Taking logarithms, $`\operatorname{Re} F(\sigma)` converges to a
finite limit as $`\sigma \to 1^+`. But
$`|\operatorname{Re} F(\sigma)| \geq |c| \sum_k q_k^{-\sigma} - 2C - M \to +\infty`.
:::

# The bounded case

:::lemma_ "bounded_sums_norm" (lean := "RokickiConstant.norm_sum_chi4_le") (uses := "chi4, odd_prime")
If $`|S(n)| \leq C` for all $`n`, then $`\big\| \sum_{j<n} \chi(q_j) \big\| \leq C` in $`\mathbb{C}`.
:::

:::proof "bounded_sums_norm" (uses := "chi4_basic")
The complex sum is the cast of the integer sum.
:::

:::lemma_ "abel_chi4_holomorphic" (lean := "RokickiConstant.differentiableOn_abelSeries_chi4") (uses := "abel_series, chi4, odd_prime")
If $`S` is bounded, the Abel series $`A(s)` of the coefficients $`a_k = \chi(q_k)` over the
sequence $`q` is holomorphic on $`\operatorname{Re} s > 0`.
:::

:::proof "abel_chi4_holomorphic" (uses := "bounded_sums_norm, abel_series_holomorphic, odd_prime_basic")
Apply the general theorem of {ref "chapter-partial-sums"}[Chapter 4].
:::

:::theorem "continuation" (lean := "RokickiConstant.exp_abelSeries_add_primePowerPart") (uses := "abel_series, prime_power_part, chi4")
If $`S` is bounded, then $`\exp\big( A(s) + H(s) \big) = L(s, \chi)` for all $`\operatorname{Re} s > 1/2`.
:::

:::proof "continuation" (uses := "abel_chi4_holomorphic, abel_series_eq, euler_product, prime_power_part_holomorphic, chi4_basic")
Both sides are holomorphic on the connected open half-plane $`\operatorname{Re} s > 1/2`, the right
side because $`L(\cdot, \chi)` is entire. They agree on $`\operatorname{Re} s > 1`, where $`A = G` and
the Euler product applies. The identity theorem gives equality on the whole half-plane.
:::

:::theorem "not_bounded" (lean := "RokickiConstant.not_exists_abs_sum_chi4_le") (uses := "chi4, odd_prime")
There is no $`C` with $`|S(n)| \leq C` for all $`n`.
:::

:::proof "not_bounded" (uses := "continuation, abel_chi4_holomorphic, prime_power_part_blowup, exp_re_limit")
Suppose there were. For real $`\sigma > 1/2`,
$`\exp\big( \operatorname{Re} A(\sigma) + \operatorname{Re} H(\sigma) \big) = |L(\sigma, \chi)| \to |L(1/2, \chi)| < \infty`
as $`\sigma \to 1/2^+`. But $`\operatorname{Re} A(\sigma) \to \operatorname{Re} A(1/2)` by continuity of the
holomorphic function $`A` at $`1/2`, while $`\operatorname{Re} H(\sigma) \to +\infty`; so the left side
tends to $`+\infty`.
:::
