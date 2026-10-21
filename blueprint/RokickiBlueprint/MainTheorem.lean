/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint
import Comparator.Solution

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The main theorem" =>

%%%
tag := "chapter-main-theorem"
%%%

The comparator file `Comparator/Challenge.lean` states the problem without reference to the
development; `Comparator/Solution.lean` is the same file with the proof filled in.

:::definition "rho" (lean := "rho")
$$`\rho = \sum_{k \geq 0} \frac{[\,p_{k+2} \equiv 3 \pmod 4\,]}{2^{k+1}}.`
:::

:::theorem "main" (lean := "rho_irrational") (uses := "rho")
Rokicki's constant $`\rho` is irrational.
:::

:::proof "main" (uses := "rokicki_constant, digit_le_one, irrational_of_not_periodic, chi4_odd_prime_int, periodic_partial_sums, not_bounded, not_linear")
$`\rho` equals $`\sum_k d_k / 2^{k+1}` with $`d_k \in \{0, 1\}` the digits of
{ref "chapter-rokicki-constant"}[Chapter 2]. Suppose the digits were eventually periodic with
period $`p > 0`. Then so is $`k \mapsto \chi_4(q_k) = 1 - 2 d_k`, hence $`S(n) = c\,n + O(1)` for
some rational $`c`. If $`c = 0` the partial sums are bounded, contradicting
{bpref "not_bounded"}[]; if $`c \neq 0`, {bpref "not_linear"}[] is contradicted. Hence the digits
are not eventually periodic, and $`\rho` is irrational by {bpref "irrational_of_not_periodic"}[].
:::
