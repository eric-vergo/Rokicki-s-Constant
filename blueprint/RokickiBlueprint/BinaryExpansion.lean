/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint
import RokickiConstant.BinaryExpansion

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Binary expansions of rational numbers" =>

%%%
tag := "chapter-binary-expansion"
%%%

This chapter is independent of primes. Fix a digit sequence $`d : \mathbb{N} \to \{0, 1\}` and let
$`x = \sum_{k \geq 0} d_k / 2^{k+1} \in [0, 1]`. We prove that if $`x` is rational then $`d` is
eventually periodic. The usual proof divides by the denominator and watches remainders, but has
to deal with the non-uniqueness of binary expansions ($`0.0111\ldots = 0.1000\ldots`). We avoid
that discussion by working with the tails of the series and a short argument showing that two
equal tails must begin with the same digit.

:::definition "eventually_periodic" (lean := "Function.EventuallyPeriodic")
A function $`f : \mathbb{N} \to \alpha` is *eventually periodic* with period $`p` if
$`f(n + p) = f(n)` for all sufficiently large $`n`.
:::

:::lemma_ "eventually_periodic_exists" (lean := "Function.EventuallyPeriodic.exists_forall_le") (uses := "eventually_periodic")
If $`f` is eventually periodic with period $`p`, there is $`N` with $`f(n + p) = f(n)` for all
$`n \geq N`.
:::

:::proof "eventually_periodic_exists"
This is the definition of "for all sufficiently large $`n`".
:::

:::definition "binary_tail" (lean := "binaryTail")
The *tail* of the expansion at position $`n` is
$$`T_d(n) = \sum_{k \geq 0} \frac{d_{n+k}}{2^{k+1}}.`
:::

:::lemma_ "binary_tail_basic" (lean := "summable_binaryTail, binaryTail_zero, binaryTail_succ, binaryTail_mem_Icc") (uses := "binary_tail")
For digits $`d_k \leq 1`: the tail series converges, $`T_d(0) = x`, $`T_d(n+1) = 2\,T_d(n) - d_n`,
and $`0 \leq T_d(n) \leq 1`.
:::

:::proof "binary_tail_basic"
Comparison with the geometric series $`\sum_k 2^{-(k+1)} = 1`; the recursion comes from splitting
off the first term of the tail.
:::

:::lemma_ "binary_tail_extreme" (lean := "binaryTail_eq_one_iff, binaryTail_eq_zero_iff") (uses := "binary_tail")
$`T_d(n) = 1` if and only if $`d_{n+k} = 1` for all $`k`, and $`T_d(n) = 0` if and only if
$`d_{n+k} = 0` for all $`k`.
:::

:::proof "binary_tail_extreme" (uses := "binary_tail_basic")
A convergent sum of nonnegative terms vanishes if and only if every term vanishes. If some
$`d_{n+k_0} = 0`, then comparing termwise with the all-ones series gives
$`T_d(n) \leq 1 - 2^{-(k_0+1)} < 1`.
:::

:::lemma_ "binary_tail_eq" (lean := "apply_eq_of_binaryTail_eq, binaryTail_succ_eq_of_binaryTail_eq") (uses := "binary_tail")
If $`i < j` and $`T_d(i) = T_d(j)`, then $`d_i = d_j` and $`T_d(i+1) = T_d(j+1)`.
:::

:::proof "binary_tail_eq" (uses := "binary_tail_basic, binary_tail_extreme")
Suppose $`d_i \neq d_j`; say $`d_i = 0` and $`d_j = 1`. Write $`T = T_d(i) = T_d(j)`. By the
recursion $`T_d(i+1) = 2T` and $`T_d(j+1) = 2T - 1`, and both lie in $`[0, 1]`, which forces
$`T = 1/2`, $`T_d(i+1) = 1` and $`T_d(j+1) = 0`. By the previous lemma all digits from index
$`i+1` on equal $`1`; since $`j + 1 > i + 1` this gives $`T_d(j+1) = 1`, a contradiction. In the
other case, $`d_i = 1` and $`d_j = 0`, the same computation gives $`T_d(i+1) = 0` and
$`T_d(j+1) = 1`: all digits from $`i+1` on are $`0` while all digits from $`j+1` on are $`1`,
which is absurd at index $`j+1`. Hence $`d_i = d_j`, and the recursion gives
$`T_d(i+1) = T_d(j+1)`.
:::

:::lemma_ "two_pow_mul_tsum" (lean := "two_pow_mul_tsum_sub_binaryTail") (uses := "binary_tail")
$`2^n x - T_d(n) = \sum_{k < n} d_k\, 2^{\,n-1-k}`, an integer.
:::

:::proof "two_pow_mul_tsum" (uses := "binary_tail_basic")
Induction on $`n` using the recursion $`T_d(n+1) = 2\,T_d(n) - d_n`.
:::

:::lemma_ "finite_range_tail" (lean := "finite_range_binaryTail") (uses := "binary_tail")
If $`x` is rational, the tails $`T_d(n)` take only finitely many values.
:::

:::proof "finite_range_tail" (uses := "two_pow_mul_tsum, binary_tail_basic")
Write $`x = a / b` with $`b \geq 1`. Then $`b\, T_d(n) = 2^n a - b \sum_{k<n} d_k 2^{n-1-k}` is an
integer in $`[0, b]`, so $`T_d(n) \in \{0, 1/b, \ldots, 1\}`.
:::

:::theorem "eventually_periodic_of_rational" (lean := "eventuallyPeriodic_of_tsum_div_two_pow_mem_range_ratCast") (uses := "eventually_periodic")
If $`x = \sum_k d_k / 2^{k+1}` is rational, then $`d` is eventually periodic with some period
$`p > 0`.
:::

:::proof "eventually_periodic_of_rational" (uses := "finite_range_tail, binary_tail_eq")
By the pigeonhole principle there are $`i < j` with $`T_d(i) = T_d(j)`. By induction on $`k`, using
the previous lemma at each step, $`T_d(i+k) = T_d(j+k)` and $`d_{i+k} = d_{j+k}` for all $`k`.
So $`d` has period $`p = j - i` from index $`i` on.
:::

:::theorem "irrational_of_not_periodic" (lean := "irrational_tsum_div_two_pow") (uses := "eventually_periodic")
If $`d` is not eventually periodic for any period $`p > 0`, then $`\sum_k d_k / 2^{k+1}` is
irrational.
:::

:::proof "irrational_of_not_periodic" (uses := "eventually_periodic_of_rational")
This is the contrapositive of the previous theorem.
:::
