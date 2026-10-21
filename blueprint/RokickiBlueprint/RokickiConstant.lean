/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint
import RokickiConstant.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Rokicki's constant" =>

%%%
tag := "chapter-rokicki-constant"
file := "Rokickis-constant"
%%%

Throughout, $`q_k = p_{k+2}` denotes the $`k`-th odd prime, $`k \geq 0`, so that $`q_0 = 3`.
In Lean this is `RokickiConstant.oddPrime k`, defined as `Nat.nth Nat.Prime (k + 1)`.

:::definition "odd_prime" (lean := "RokickiConstant.oddPrime")
The $`k`-th odd prime $`q_k = p_{k+2}`.
:::

:::lemma_ "odd_prime_basic" (lean := "RokickiConstant.prime_oddPrime, RokickiConstant.oddPrime_pos, RokickiConstant.oddPrime_strictMono, RokickiConstant.oddPrime_zero") (uses := "odd_prime")
$`q_k` is prime and positive, $`k \mapsto q_k` is strictly increasing, and $`q_0 = 3`.
:::

:::proof "odd_prime_basic"
These are the basic properties of `Nat.nth` applied to the infinite set of primes.
:::

:::lemma_ "odd_prime_mod_four" (lean := "RokickiConstant.oddPrime_mod_four") (uses := "odd_prime")
$`q_k \equiv 1` or $`q_k \equiv 3 \pmod 4`.
:::

:::proof "odd_prime_mod_four" (uses := "odd_prime_basic")
$`q_k \neq 2` because `Nat.nth` is injective and $`p_1 = 2`; an odd number is $`1` or $`3`
modulo $`4`.
:::

:::definition "digit" (lean := "Real.rokickiDigit")
The $`k`-th binary digit of Rokicki's constant is $`d_k = 1` if $`q_k \equiv 3 \pmod 4` and
$`d_k = 0` otherwise.
:::

:::definition "rokicki_constant" (lean := "Real.rokickiConstant") (uses := "digit")
*Rokicki's constant* is
$$`\rho = \sum_{k \geq 0} \frac{d_k}{2^{k+1}}.`
In Lean it carries the scoped notation `ρ`.
:::

:::lemma_ "digit_le_one" (lean := "Real.rokickiDigit_le_one, Real.rokickiDigit_eq_one_iff, Real.rokickiDigit_eq_zero_iff") (uses := "digit")
$`d_k \in \{0, 1\}`; moreover $`d_k = 1` if and only if $`q_k \equiv 3 \pmod 4`, and $`d_k = 0` if
and only if $`q_k \equiv 1 \pmod 4`.
:::

:::proof "digit_le_one" (uses := "odd_prime_mod_four")
Immediate from the definition, since an odd prime is $`1` or $`3` modulo $`4`.
:::

:::lemma_ "rokicki_constant_mem_Icc" (lean := "Real.summable_rokickiDigit_div_two_pow, Real.rokickiConstant_mem_Icc") (uses := "rokicki_constant")
The series defining $`\rho` converges, and $`0 \leq \rho \leq 1`.
:::

:::proof "rokicki_constant_mem_Icc" (uses := "digit_le_one, binary_tail_basic")
Compare with the geometric series $`\sum_k 2^{-(k+1)} = 1`. In the development this is the tail
$`T_d(0)` of {ref "chapter-binary-expansion"}[the next chapter].
:::

:::definition "oeis" (lean := "Real.oeisA362583") (uses := "digit")
$`a_n = \sum_{k < n} d_k\, 2^{\,n-1-k}` is the integer with binary digits $`d_0 d_1 \cdots d_{n-1}`.
It equals $`A362583(n+1)`; the OEIS sequence has offset $`2`.
:::

:::theorem "tendsto_oeis" (lean := "Real.tendsto_oeisA362583_div_two_pow") (uses := "oeis, rokicki_constant")
(Rokicki's observation.) $`a_n / 2^n \to \rho` as $`n \to \infty`.
:::

:::proof "tendsto_oeis" (uses := "rokicki_constant_mem_Icc")
$`a_n / 2^n = \sum_{k<n} d_k / 2^{k+1}` is the $`n`-th partial sum of the convergent series
defining $`\rho`.
:::

:::lemma_ "chi4_odd_prime_int" (lean := "RokickiConstant.χ₄_oddPrime") (uses := "odd_prime, digit")
Let $`\chi_4` be Mathlib's integer-valued quadratic character modulo $`4` (`ZMod.χ₄`). Then
$`\chi_4(q_k) = 1 - 2 d_k`.
:::

:::proof "chi4_odd_prime_int" (uses := "digit_le_one, odd_prime_mod_four")
$`\chi_4(n) = 1` for $`n \equiv 1` and $`\chi_4(n) = -1` for $`n \equiv 3 \pmod 4`.
:::
