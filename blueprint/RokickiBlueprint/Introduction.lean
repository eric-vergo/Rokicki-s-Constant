/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Introduction" =>

%%%
tag := "chapter-introduction"
%%%

Let $`p_1 = 2 < p_2 = 3 < p_3 = 5 < \cdots` be the primes. For each odd prime $`p_k` (so
$`k \geq 2`) write a binary digit $`b_k = 1` if $`p_k \equiv 3 \pmod 4` and $`b_k = 0` if
$`p_k \equiv 1 \pmod 4`. Reading $`b_2 b_3 \cdots b_n` as a binary integer gives the sequence
A362583 of the On-Line Encyclopedia of Integer Sequences: $`1, 2, 5, 11, 22, 44, 89, 179, \ldots`
Tom Rokicki observed that $`A362583(n) / 2^{n-1}` converges. The limit is the binary fraction
$`0.b_2 b_3 b_4 \cdots`,
$$`\rho = \sum_{k \geq 2} \frac{b_k}{2^{k-1}} = 0.70040013796579773\ldots,`
which we call *Rokicki's constant*. This blueprint describes a complete formal proof, in Lean 4
and Mathlib, that $`\rho` is irrational.

# Strategy

A real number with binary digits $`(b_k)` is rational if and only if the digit sequence is
eventually periodic. So it suffices to show that the pattern of residues of the odd primes modulo
$`4` is not eventually periodic. Let $`\chi = \chi_4` be the nontrivial Dirichlet character
modulo $`4`, so that $`\chi(p_k) = 1 - 2 b_k` for odd $`p_k`, and let
$`S(n) = \sum_{k < n} \chi(p_{k+2})` be its partial sums over the odd primes. If the digits were
eventually periodic with period $`P`, then $`S(n) = c\, n + O(1)` where $`c` is the average
of $`\chi` over one period. We rule out both $`c \neq 0` and $`c = 0` using only the Euler
product of the Dirichlet $`L`-function,
$$`L(s, \chi) = \exp\Big( \sum_p \chi(p)\, p^{-s} + \sum_p \sum_{m \geq 2} \frac{\chi(p)^m p^{-ms}}{m} \Big), \qquad \operatorname{Re} s > 1,`
together with three facts that Mathlib provides: $`L(\cdot, \chi)` is entire, $`L(1, \chi) \neq 0`,
and $`\sum_p 1/p` diverges.

* If $`c \neq 0`, summation by parts gives $`\sum_p \chi(p) p^{-\sigma} = c \sum_p p^{-\sigma} + O(1)`
  for real $`\sigma > 1`, which tends to $`\pm\infty` as $`\sigma \to 1^+`, while the prime-power
  part stays bounded. Then $`L(\sigma, \chi)` would tend to $`0` or $`\infty`, contradicting
  $`L(1, \chi) \neq 0` and continuity.

* If $`c = 0`, the partial sums $`S(n)` are bounded, so summation by parts continues
  $`\sum_p \chi(p) p^{-s}` to a holomorphic function on $`\operatorname{Re} s > 0`. The prime-power
  part is holomorphic on $`\operatorname{Re} s > 1/2`, so by the identity theorem the exponential
  formula holds on $`\operatorname{Re} s > 1/2`. But as real $`\sigma \to 1/2^+` the $`m = 2` terms
  $`\sum_p p^{-2\sigma}/2` tend to $`+\infty` while everything else stays bounded, so
  $`|L(\sigma, \chi)| \to \infty`, contradicting the continuity of the entire function
  $`L(\cdot, \chi)` at $`1/2`.

Neither argument uses the prime number theorem, nor Dirichlet's theorem on primes in arithmetic
progressions. The second argument is the heart of the proof: it shows that $`\sum_{p \leq x} \chi_4(p)`
is unbounded, a weak form of the Chebyshev bias phenomenon, with elementary tools.

# Reading guide

{ref "chapter-rokicki-constant"}[The next chapter] defines $`\rho` and its digits.
{ref "chapter-binary-expansion"}[Chapter 3] proves the digit criterion for rationality.
{ref "chapter-partial-sums"}[Chapter 4] collects the real-variable tools: partial sums of
eventually periodic sequences, summation by parts, and the Abel series.
{ref "chapter-euler-product"}[Chapter 5] sets up $`\chi_4` and the Euler product.
{ref "chapter-character-sums"}[Chapter 6] draws the two contradictions, and
{ref "chapter-main-theorem"}[Chapter 7] assembles the main theorem. Every statement is formalized;
the dependency graph at the end records which results each proof uses.

# The formal statement

The comparator file `Comparator/Challenge.lean` states the problem with no reference to the
development, and `Comparator/Solution.lean` proves it:

```
noncomputable def rho : ℝ :=
  ∑' k : ℕ, (if Nat.nth Nat.Prime (k + 1) % 4 = 3 then (1 : ℝ) else 0) / 2 ^ (k + 1)

theorem rho_irrational : Irrational rho
```

Here `Nat.nth Nat.Prime (k + 1)` is the prime $`p_{k+2}`. Throughout the development the
odd primes are indexed from $`0`: we write $`q_k = p_{k+2}`, so that $`q_0 = 3`, and the digit
$`d_k = b_{k+2}` belongs to $`q_k`.
