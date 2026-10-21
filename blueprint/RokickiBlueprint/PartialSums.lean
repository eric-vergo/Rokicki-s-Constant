/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint
import RokickiConstant.PartialSums

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Partial sums and summation by parts" =>

%%%
tag := "chapter-partial-sums"
%%%

This chapter collects the elementary analysis used later: the partial sums of an eventually
periodic sequence, a summation-by-parts bound, and the *Abel series*, which continues a
Dirichlet series with bounded coefficient sums from $`\operatorname{Re} s > 1` to
$`\operatorname{Re} s > 0`.

# Eventually periodic sequences

:::lemma_ "eventually_periodic_bounded" (lean := "Function.EventuallyPeriodic.exists_forall_abs_le") (uses := "eventually_periodic")
An eventually periodic real sequence is bounded.
:::

:::proof "eventually_periodic_bounded" (uses := "eventually_periodic_exists")
Beyond the index $`N` the sequence takes only the values $`f(N), \ldots, f(N+p-1)`.
:::

:::theorem "periodic_partial_sums" (lean := "Function.EventuallyPeriodic.exists_abs_sum_sub_mul_le") (uses := "eventually_periodic")
If $`a : \mathbb{N} \to \mathbb{Z}` is eventually periodic with period $`p > 0`, there are a
rational number $`c` and a constant $`C` such that
$$`\Big| \sum_{k < n} a_k - c\, n \Big| \leq C \qquad \text{for all } n.`
:::

:::proof "periodic_partial_sums" (uses := "eventually_periodic_exists, eventually_periodic_bounded")
Let $`S(n) = \sum_{k<n} a_k` and choose $`N` with $`a_{n+p} = a_n` for $`n \geq N`. Put
$`c = (S(N+p) - S(N)) / p`. For $`n \geq N` we have $`S(n+p) - S(n) = S(N+p) - S(N) = c\,p`, so
$`n \mapsto S(n) - c\,n` is itself eventually periodic with period $`p`, hence bounded.
:::

# Summation by parts

:::lemma_ "by_parts_identity" (lean := "sum_range_succ_mul_eq_sum_mul_sub")
For sequences $`a` and $`w` in a commutative ring, with $`S(n) = \sum_{j<n} a_j`,
$$`\sum_{k \leq n} a_k w_k = S(n+1)\, w_n + \sum_{k < n} S(k+1)\, (w_k - w_{k+1}).`
:::

:::proof "by_parts_identity"
Abel summation; in Mathlib, `Finset.sum_range_by_parts'`.
:::

:::theorem "by_parts_bound" (lean := "abs_sum_range_mul_le_of_abs_sum_le, abs_tsum_mul_le_of_abs_sum_le")
Let $`e : \mathbb{N} \to \mathbb{R}` have partial sums bounded by $`C`, and let
$`f : \mathbb{N} \to \mathbb{R}` be nonnegative and antitone. Then every partial sum of
$`\sum_k e_k f_k` is bounded by $`2 C f_0`, and so is the sum of the series whenever it converges.
:::

:::proof "by_parts_bound" (uses := "by_parts_identity")
By the identity, $`|\sum_{k \leq n} e_k f_k| \leq C f_n + C \sum_{k<n} (f_k - f_{k+1}) = C f_0`, since
the differences $`f_k - f_{k+1}` are nonnegative and telescope. For the series, pass to the limit.
:::

# The Abel series

:::definition "abel_series" (lean := "abelSeries")
For $`a : \mathbb{N} \to \mathbb{C}` and $`q : \mathbb{N} \to \mathbb{N}`, with
$`S(n) = \sum_{j<n} a_j`, the *Abel series* is
$$`A(s) = \sum_{k \geq 0} S(k+1)\, \big( q_k^{-s} - q_{k+1}^{-s} \big).`
:::

:::lemma_ "cpow_difference" (lean := "norm_ofReal_cpow_neg_sub_cpow_neg_le")
For real $`1 \leq x \leq y` and $`0 < \delta \leq \operatorname{Re} s`,
$$`\big| x^{-s} - y^{-s} \big| \leq \frac{|s|}{\delta}\, \big( x^{-\delta} - y^{-\delta} \big).`
:::

:::proof "cpow_difference"
$`y^{-s} - x^{-s} = -s \int_x^y t^{-s-1}\, dt`, and
$`|t^{-s-1}| = t^{-\operatorname{Re} s - 1} \leq t^{-\delta - 1}` for $`t \geq 1`.
:::

:::lemma_ "abel_series_term" (lean := "antitone_natCast_rpow_neg, summable_sub_of_antitone, norm_abelSeries_term_le") (uses := "abel_series")
Let $`q` be strictly increasing with $`q_0 > 0` and suppose $`|S(n)| \leq C` for all $`n`. For
$`0 < \delta \leq \operatorname{Re} s`, the $`k`-th term of the Abel series has norm at most
$`C \frac{|s|}{\delta} (q_k^{-\delta} - q_{k+1}^{-\delta})`, and these bounds are summable.
:::

:::proof "abel_series_term" (uses := "cpow_difference")
The bound is the previous lemma. The sequence $`q_k^{-\delta}` is antitone and nonnegative, so the
differences telescope to a sum at most $`q_0^{-\delta}`.
:::

:::theorem "abel_series_summable" (lean := "summable_abelSeries") (uses := "abel_series")
Under the hypotheses of the previous lemma, the Abel series converges absolutely for every
$`s` with $`\operatorname{Re} s > 0`.
:::

:::proof "abel_series_summable" (uses := "abel_series_term")
Take $`\delta = \operatorname{Re} s`.
:::

:::theorem "abel_series_holomorphic" (lean := "differentiableOn_abelSeries") (uses := "abel_series")
Under the same hypotheses, $`A` is holomorphic on $`\operatorname{Re} s > 0`.
:::

:::proof "abel_series_holomorphic" (uses := "abel_series_term")
Near a point $`s_0` with $`\operatorname{Re} s_0 > 0`, take $`\delta = \operatorname{Re} s_0 / 2` and a
neighbourhood on which $`|s| \leq |s_0| + 1`. The term bounds are then uniform, so the series of
holomorphic functions converges locally uniformly and its sum is holomorphic.
:::

:::lemma_ "dirichlet_summable" (lean := "summable_natCast_rpow, summable_mul_cpow_neg")
If $`q` is strictly increasing with $`q_0 > 0`, then $`\sum_k q_k^{\,r}` converges for $`r < -1`,
and $`\sum_k a_k q_k^{-s}` converges absolutely for bounded $`a` and $`\operatorname{Re} s > 1`.
:::

:::proof "dirichlet_summable"
$`q_k \geq k + 1`, and $`\sum_k (k+1)^r` converges for $`r < -1`.
:::

:::theorem "abel_series_eq" (lean := "abelSeries_eq_tsum") (uses := "abel_series")
If the partial sums of $`a` are bounded and $`q` is strictly increasing with $`q_0 > 0`, then
$`A(s) = \sum_k a_k q_k^{-s}` for $`\operatorname{Re} s > 1`.
:::

:::proof "abel_series_eq" (uses := "by_parts_identity, abel_series_summable, dirichlet_summable")
By the summation by parts identity, the partial sums of the Dirichlet series are
$`S(n+1)\, q_n^{-s}` plus the partial sums of the Abel series. The boundary term tends to $`0`
because $`S` is bounded and $`q_n \to \infty`.
:::
