/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import RokickiConstant.CharacterSums

/-!
# Rokicki's constant is irrational

We prove that Rokicki's constant `ρ = ∑ₖ₌₂ [pₖ ≡ 3 (mod 4)] / 2 ^ (k - 1)` is irrational.

If `ρ` were rational, its binary digits `[pₖ ≡ 3 (mod 4)]` would be eventually periodic
(`eventuallyPeriodic_of_tsum_div_two_pow_mem_range_ratCast`), hence so would the values
`χ₄ pₖ = 1 - 2 · [pₖ ≡ 3 (mod 4)]` of the nontrivial Dirichlet character modulo `4` at the odd
primes. The partial sums of an eventually periodic sequence are `c · n + O(1)`
(`Function.EventuallyPeriodic.exists_abs_sum_sub_mul_le`), but the partial sums of `χ₄` over the
odd primes are neither bounded (`RokickiConstant.not_exists_abs_sum_chi4_le`) nor linear with
nonzero slope (`RokickiConstant.not_exists_abs_sum_chi4_sub_mul_le`): both would contradict the
Euler product of `L(s, χ₄)`.

The proof does not use the prime number theorem.

## Main statements

* `Real.irrational_rokickiConstant`: **Rokicki's constant is irrational**.

## Tags

Rokicki's constant, irrational, primes modulo 4, Dirichlet character
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Finset Function

namespace Real

open RokickiConstant

/-- **Rokicki's constant is irrational.** -/
theorem irrational_rokickiConstant : Irrational rokickiConstant := by
  refine irrational_tsum_div_two_pow rokickiDigit_le_one fun p hp hd ↦ ?_
  have ha : EventuallyPeriodic (fun k ↦ ZMod.χ₄ (oddPrime k)) p := by
    unfold EventuallyPeriodic at hd ⊢
    filter_upwards [hd] with n hn
    rw [χ₄_oddPrime, χ₄_oddPrime, hn]
  obtain ⟨c, C, hC⟩ := ha.exists_abs_sum_sub_mul_le hp
  by_cases hc : (c : ℝ) = 0
  · exact not_exists_abs_sum_chi4_le ⟨C, fun n ↦ by simpa [hc] using hC n⟩
  · exact not_exists_abs_sum_chi4_sub_mul_le ⟨c, hc, C, hC⟩

end Real
