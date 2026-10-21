/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint
import RokickiConstant.Chi4
import RokickiConstant.EulerProduct

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The character modulo four and the Euler product" =>

%%%
tag := "chapter-euler-product"
%%%

# The character

:::definition "chi4" (lean := "RokickiConstant.chi4")
$`\chi = \chi_4` is the nontrivial Dirichlet character modulo $`4` with complex values:
$`\chi(n) = 1` if $`n \equiv 1`, $`\chi(n) = -1` if $`n \equiv 3 \pmod 4`, and $`\chi(n) = 0` for
even $`n`. In Lean it is `ZMod.χ₄` composed with the cast from $`\mathbb{Z}` to $`\mathbb{C}`.
:::

:::lemma_ "chi4_basic" (lean := "RokickiConstant.chi4_natCast, RokickiConstant.chi4_ne_one, RokickiConstant.chi4_two") (uses := "chi4")
$`\chi(n)` is the cast of `ZMod.χ₄ n`; $`\chi` is not the trivial character; and $`\chi(2) = 0`.
:::

:::proof "chi4_basic"
$`\chi(3) = -1 \neq 1`.
:::

:::lemma_ "chi4_odd_prime" (lean := "RokickiConstant.chi4_oddPrime, RokickiConstant.chi4_oddPrime_sq, RokickiConstant.norm_chi4_oddPrime") (uses := "chi4, odd_prime, digit")
$`\chi(q_k) = 1 - 2 d_k \in \{1, -1\}`; consequently $`\chi(q_k)^2 = 1` and $`|\chi(q_k)| = 1`.
:::

:::proof "chi4_odd_prime" (uses := "chi4_basic, chi4_odd_prime_int")
Cast the integer identity $`\chi_4(q_k) = 1 - 2 d_k` to $`\mathbb{C}`.
:::

# Sums over the odd primes

:::lemma_ "tsum_primes_split" (lean := "RokickiConstant.tsum_primes_eq_add_tsum_oddPrime") (uses := "odd_prime")
For a summable function $`F` on the primes, $`\sum_p F(p) = F(2) + \sum_{k \geq 0} F(q_k)`.
:::

:::proof "tsum_primes_split" (uses := "odd_prime_basic")
$`k \mapsto p_{k+1}` is a bijection from $`\mathbb{N}` onto the primes, since `Nat.nth` is
injective with range the primes. Reindex the sum and split off $`k = 0`.
:::

:::lemma_ "prime_sums" (lean := "RokickiConstant.not_summable_oddPrime_inv, RokickiConstant.summable_oddPrime_rpow") (uses := "odd_prime")
$`\sum_k 1/q_k` diverges, and $`\sum_k q_k^{\,r}` converges for $`r < -1`.
:::

:::proof "prime_sums" (uses := "tsum_primes_split, dirichlet_summable, odd_prime_basic")
Mathlib proves that $`\sum_p 1/p` diverges; removing the term at $`p = 2` does not change that.
Convergence is the general lemma of {ref "chapter-partial-sums"}[the previous chapter].
:::

:::theorem "tendsto_prime_sum" (lean := "RokickiConstant.tendsto_tsum_oddPrime_rpow_neg") (uses := "odd_prime")
$`\sum_k q_k^{-\sigma} \to +\infty` as real $`\sigma \to 1^+`.
:::

:::proof "tendsto_prime_sum" (uses := "prime_sums")
Given $`M`, choose $`N` with $`\sum_{k<N} 1/q_k > M + 1`. The finite sum $`\sum_{k<N} q_k^{-\sigma}`
is continuous in $`\sigma`, so it exceeds $`M` for $`\sigma` close to $`1`, and it is at most the
full sum.
:::

# The Euler product

:::definition "prime_term" (lean := "RokickiConstant.primeTerm") (uses := "chi4, odd_prime")
$`z_k(s) = \chi(q_k)\, q_k^{-s}`.
:::

:::lemma_ "prime_term_norm" (lean := "RokickiConstant.norm_primeTerm, RokickiConstant.norm_primeTerm_le") (uses := "prime_term")
$`|z_k(s)| = q_k^{-\operatorname{Re} s}`, and $`|z_k(s)| \leq 3/4` whenever $`\operatorname{Re} s > 1/2`.
:::

:::proof "prime_term_norm" (uses := "chi4_odd_prime, odd_prime_basic")
$`|\chi(q_k)| = 1` and $`q_k \geq 3`, so $`q_k^{-\operatorname{Re} s} \leq 3^{-1/2} < 3/4`.
:::

:::lemma_ "log_tail_bounds" (lean := "RokickiConstant.one_sub_mem_slitPlane, RokickiConstant.norm_neg_log_one_sub_sub_le, RokickiConstant.norm_neg_log_one_sub_sub_sub_le")
For complex $`|z| \leq 3/4`: $`1 - z` lies in the slit plane, $`|{-\log(1-z)} - z| \leq 2|z|^2`, and
$`|{-\log(1-z)} - z - z^2/2| \leq 2|z|^3`.
:::

:::proof "log_tail_bounds"
Mathlib bounds the remainder of the Taylor series of $`\log(1-z)^{-1}`:
$`\big| \log(1-z)^{-1} - \sum_{j \leq n} z^j/j \big| \leq |z|^{n+1} (1-|z|)^{-1} / (n+1)`, and
$`(1 - |z|)^{-1} \leq 4`.
:::

:::definition "prime_part" (lean := "RokickiConstant.primePart") (uses := "prime_term")
The *prime part* $`G(s) = \sum_k z_k(s) = \sum_k \chi(q_k)\, q_k^{-s}`.
:::

:::definition "prime_power_part" (lean := "RokickiConstant.primePowerPart") (uses := "prime_term")
The *prime-power part* $`H(s) = \sum_k \big( -\log(1 - z_k(s)) - z_k(s) \big)`. For
$`\operatorname{Re} s > 0` the $`k`-th term equals $`\sum_{m \geq 2} \chi(q_k)^m q_k^{-ms} / m`, the
contribution of the powers of $`q_k` to the logarithm of the Euler product.
:::

:::lemma_ "prime_power_part_term" (lean := "RokickiConstant.norm_primePowerPart_term_le") (uses := "prime_power_part")
For $`1/2 < \sigma_0 \leq \operatorname{Re} s`, the $`k`-th term of $`H(s)` has norm at most
$`2 q_k^{-2\sigma_0}`.
:::

:::proof "prime_power_part_term" (uses := "log_tail_bounds, prime_term_norm")
Apply the bound $`|{-\log(1-z)} - z| \leq 2|z|^2` with $`z = z_k(s)`, and
$`|z_k(s)|^2 = q_k^{-2 \operatorname{Re} s} \leq q_k^{-2\sigma_0}`.
:::

:::lemma_ "parts_summable" (lean := "RokickiConstant.summable_primePart, RokickiConstant.summable_primePowerPart") (uses := "prime_part, prime_power_part")
$`G(s)` converges absolutely for $`\operatorname{Re} s > 1`, and $`H(s)` for $`\operatorname{Re} s > 1/2`.
:::

:::proof "parts_summable" (uses := "prime_power_part_term, prime_sums, dirichlet_summable")
For $`G`, the coefficients $`\chi(q_k)` are bounded. For $`H`, the terms are dominated by the
summable $`2 q_k^{-2 \operatorname{Re} s}`.
:::

:::theorem "euler_product" (lean := "RokickiConstant.exp_primePart_add_primePowerPart") (uses := "prime_part, prime_power_part, chi4")
For $`\operatorname{Re} s > 1`,
$$`\exp\big( G(s) + H(s) \big) = L(s, \chi).`
:::

:::proof "euler_product" (uses := "parts_summable, tsum_primes_split, chi4_basic")
Mathlib provides the Euler product in exponential form,
$`\exp\big( \sum_p -\log(1 - \chi(p) p^{-s}) \big) = L(s, \chi)`. The term at $`p = 2` vanishes since
$`\chi(2) = 0`, and the sum over the odd primes splits termwise as
$`z_k + \big( -\log(1 - z_k) - z_k \big)`.
:::

# Analytic properties of the prime-power part

:::theorem "prime_power_part_holomorphic" (lean := "RokickiConstant.differentiableOn_primePowerPart") (uses := "prime_power_part")
$`H` is holomorphic on $`\operatorname{Re} s > 1/2`.
:::

:::proof "prime_power_part_holomorphic" (uses := "prime_power_part_term, prime_sums, prime_term_norm, log_tail_bounds")
On each half-plane $`\operatorname{Re} s > \sigma_0 > 1/2` the terms are holomorphic, because the
logarithm is holomorphic on the slit plane, and they are dominated by the summable
$`2 q_k^{-2\sigma_0}`.
:::

:::lemma_ "prime_power_part_bounded" (lean := "RokickiConstant.exists_norm_primePowerPart_le") (uses := "prime_power_part")
There is a constant $`M` with $`|H(s)| \leq M` for all $`s` with $`\operatorname{Re} s \geq 1`.
:::

:::proof "prime_power_part_bounded" (uses := "prime_power_part_term, prime_sums")
Take $`M = 2 \sum_k q_k^{-2}`.
:::

:::lemma_ "prime_power_part_lower" (lean := "RokickiConstant.le_re_primePowerPart") (uses := "prime_power_part")
For real $`\sigma > 1/2`,
$$`\operatorname{Re} H(\sigma) \geq \tfrac{1}{2} \sum_k q_k^{-2\sigma} - 2 \sum_k q_k^{-3/2}.`
:::

:::proof "prime_power_part_lower" (uses := "log_tail_bounds, prime_term_norm, chi4_odd_prime, prime_sums")
For real $`\sigma`, $`z_k(\sigma)` is real with $`z_k(\sigma)^2 = q_k^{-2\sigma}` because
$`\chi(q_k)^2 = 1`. The $`k`-th term of $`H(\sigma)` differs from $`z_k^2 / 2` by at most
$`2|z_k|^3 = 2 q_k^{-3\sigma} \leq 2 q_k^{-3/2}`.
:::

:::theorem "prime_power_part_blowup" (lean := "RokickiConstant.tendsto_re_primePowerPart") (uses := "prime_power_part")
$`\operatorname{Re} H(\sigma) \to +\infty` as real $`\sigma \to 1/2^+`.
:::

:::proof "prime_power_part_blowup" (uses := "prime_power_part_lower, tendsto_prime_sum")
$`\sum_k q_k^{-2\sigma} \to +\infty` as $`2\sigma \to 1^+`, while $`\sum_k q_k^{-3/2}` is a constant.
:::
