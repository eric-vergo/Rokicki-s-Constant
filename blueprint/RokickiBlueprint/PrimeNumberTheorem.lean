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

#doc (Manual) "A second proof, by the prime number theorem" =>

%%%
tag := "chapter-prime-number-theorem"
%%%

This chapter proves the main theorem a second time. The reduction to the partial sums
$`S(n) = \sum_{k < n} \chi_4(q_k)` is unchanged, and so is the treatment of bounded $`S`. What
changes is the linear case: instead of letting $`\sigma \to 1^+` in the Euler product, we use the
prime number theorem in arithmetic progressions, which says that the primes are equidistributed
between the classes $`1` and $`3` modulo $`4`. The Lean development of this chapter is the
library `RokickiConstantPNT`. It depends on the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project, from
which the following theorem is taken.

Every statement of this chapter is formalized, and the name of its Lean declaration is given
next to it. Unlike in the other chapters, the statements are not nodes of the dependency graph
and are not linked to their declarations: PrimeNumberTheoremAnd imports LeanArchitect, which
declares an attribute named `blueprint`, as does Verso Blueprint, so a module cannot import both.
This chapter therefore does not import the Lean code it describes.

*Theorem* (`WeakPNT_AP`).
Let $`q \geq 1` and let $`0 \leq a < q` be coprime to $`q`. Then, with $`\Lambda` the von Mangoldt
function and $`\varphi` Euler's totient function,
$$`\frac{1}{N} \sum_{\substack{n < N \\ n \equiv a \ (\mathrm{mod}\ q)}} \Lambda(n) \to \frac{1}{\varphi(q)} \qquad (N \to \infty).`

*Proof.*
This is the prime number theorem in arithmetic progressions, proved in PrimeNumberTheoremAnd
from the Wiener–Ikehara theorem and the nonvanishing of Dirichlet $`L`-functions on the line
$`\operatorname{Re} s = 1`.

# From prime powers to primes

*Definition* (`RokickiConstant.PNT.thetaAP`).
For natural numbers $`q`, $`a` and $`N`, the Chebyshev function of the progression is
$$`\vartheta(N; q, a) = \sum_{\substack{p < N \\ p \equiv a \ (\mathrm{mod}\ q)}} \log p,`
the sum running over primes $`p`.

*Lemma* (`RokickiConstant.PNT.sum_vonMangoldt_sub_thetaAP_mem_Icc`, `RokickiConstant.PNT.tendsto_psi_sub_theta_div`).
Let $`\psi` and $`\theta` be the Chebyshev functions. For all $`q`, $`a` and $`N`,
$$`0 \leq \sum_{\substack{n < N \\ n \equiv a \ (\mathrm{mod}\ q)}} \Lambda(n) - \vartheta(N; q, a) \leq \psi(N) - \theta(N),`
and $`(\psi(N) - \theta(N)) / N \to 0`.

*Proof.*
$`\Lambda(p) = \log p` at primes, so the difference is the sum of $`\Lambda(n)` over the
$`n < N` in the residue class that are not prime, which is nonnegative and at most the sum of
$`\Lambda(n)` over all $`n \leq N` that are not prime. That sum is $`\psi(N) - \theta(N)`, and
Mathlib's Chebyshev bound gives $`\psi(x) - \theta(x) \leq C \sqrt{x}`.

*Theorem* (`RokickiConstant.PNT.tendsto_thetaAP_div`).
Let $`q \geq 1` and let $`0 \leq a < q` be coprime to $`q`. Then
$`\vartheta(N; q, a) / N \to 1 / \varphi(q)`.

*Proof.*
Subtract the two limits.

# Sums over the odd primes

*Lemma* (`RokickiConstant.PNT.sum_range_nth_prime`, `RokickiConstant.PNT.sum_range_oddPrime`).
For every $`f : \mathbb{N} \to \mathbb{R}` and every $`m`,
$$`\sum_{p < q_m} f(p) = f(2) + \sum_{k < m} f(q_k),`
the left sum running over primes $`p`.

*Proof.*
By induction on $`m`: the primes below the $`(m+1)`-st prime are those below the $`m`-th prime,
together with the $`m`-th prime.

*Lemma* (`RokickiConstant.PNT.thetaAP_four_oddPrime`).
For $`a \in \{1, 3\}` and every $`m`,
$$`\vartheta(q_m; 4, a) = \sum_{\substack{k < m \\ q_k \equiv a \ (\mathrm{mod}\ 4)}} \log q_k.`

*Proof.*
Take $`f(n) = \log n` for $`n \equiv a \pmod 4` and $`f(n) = 0` otherwise; the term $`f(2)`
vanishes.

*Lemma* (`RokickiConstant.PNT.abs_sum_range_mul_le_of_abs_sum_le_of_monotone`).
Let $`e, w : \mathbb{N} \to \mathbb{R}` with $`\big| \sum_{k<n} e_k \big| \leq C` for all $`n`,
and $`w` monotone with $`w_0 \geq 0`. Then for all $`n`,
$$`\Big| \sum_{k < n} e_k\, w_k \Big| \leq 2 C\, w_n.`

*Proof.*
By the summation by parts identity the sum over $`k \leq n` is the boundary term
$`E_{n+1} w_n` plus $`\sum_{k<n} E_{k+1} (w_k - w_{k+1})`, where $`E_k` are the partial sums of
$`e`. The first is at most $`C w_n` in absolute value, and the second at most
$`C \sum_{k<n} (w_{k+1} - w_k) = C (w_n - w_0)`.

# The linear case

*Theorem* (`RokickiConstant.PNT.not_exists_abs_sum_chi4_sub_mul_le`).
There are no real $`c \neq 0` and $`C` with $`|S(n) - c\,n| \leq C` for all $`n`.

*Proof.*
Suppose there were, and put
$$`B(m) = \sum_{k < m} (\chi(q_k) - c) \log q_k.`
The coefficients $`\chi(q_k) - c` have partial sums bounded by $`C`, and $`\log q_k` is
nonnegative and increasing, so $`|B(m)| \leq 2C \log q_m` by summation by parts. Since
$`q_m \to \infty`, this gives $`B(m) / q_m \to 0`.

On the other hand $`\chi(q_k) = 1` if $`q_k \equiv 1` and $`\chi(q_k) = -1` if $`q_k \equiv 3`
modulo $`4`, so
$$`B(m) = (1 - c)\, \vartheta(q_m; 4, 1) - (1 + c)\, \vartheta(q_m; 4, 3).`
By the prime number theorem in arithmetic progressions, with $`\varphi(4) = 2`, both
$`\vartheta(q_m; 4, 1) / q_m` and $`\vartheta(q_m; 4, 3) / q_m` tend to $`1/2`. Hence
$`B(m) / q_m \to (1 - c)/2 - (1 + c)/2 = -c`, and $`c = 0`.

# The main theorem again

*Theorem* (`RokickiConstant.PNT.rho_irrational`).
Rokicki's constant $`\rho` is irrational.

*Proof.*
As in {ref "chapter-main-theorem"}[the previous chapter], with the theorem above in
place of {bpref "not_linear"}[].

# What the prime number theorem does not give

The bounded case $`c = 0` is still handled by {bpref "not_bounded"}[], and we do not know how to
replace that step by the prime number theorem. The prime number theorem in arithmetic
progressions says that $`\pi(x; 4, 1) - \pi(x; 4, 3) = o(\pi(x))`, which is what a bounded $`S`
predicts, so it cannot contradict boundedness. Under the hypothesis that $`S` is bounded,
summation by parts gives $`\sum_{p \leq x} \chi(p) \log p = O(\log x)`, and then
$$`\sum_{n \leq x} \chi(n) \Lambda(n) = \sum_{p \leq \sqrt{x}} \log p + O(x^{1/3}) \sim \sqrt{x},`
because $`\chi(p^2) = 1` for every odd prime. The contradiction has to come from this secondary
term of size $`\sqrt{x}`, which the prime squares produce. Seeing that it is incompatible with
the analytic properties of $`L(s, \chi)` needs information about $`L(s, \chi)` at $`s = 1/2`,
inside the critical strip. The prime number theorem is a statement about the line
$`\operatorname{Re} s = 1` and an error term $`o(x)`, and carries no such information. The
argument of {ref "chapter-character-sums"}[Chapter 6], which continues the Euler product to
$`\operatorname{Re} s > 1/2` and lets $`\sigma \to 1/2^+`, is the direct way to use it.
