/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Comparator.Solution
import RokickiConstantPNT.CharacterSums

/-!
# Rokicki's constant is irrational: a second proof, by the prime number theorem

This file proves `Irrational rho` a second time, for the constant `rho` of
`Comparator/Solution.lean`. The reduction is the one of `rho_irrational`: if `ρ` were rational its
binary digits would be eventually periodic, and the partial sums of `χ₄` over the odd primes would
be `c · n + O(1)` for some `c`.

* The case `c ≠ 0` is ruled out by the prime number theorem in arithmetic progressions
  (`RokickiConstant.PNT.not_exists_abs_sum_chi4_sub_mul_le`): the primes are equidistributed
  between the classes `1` and `3` modulo `4`, which forces `c = 0`. In the first proof this is the
  step `s → 1⁺`, which uses `L(1, χ₄) ≠ 0`.
* The case `c = 0` of bounded partial sums is ruled out as in the first proof
  (`RokickiConstant.not_exists_abs_sum_chi4_le`), by continuing the Euler product of `L(s, χ₄)` to
  `re s > 1 / 2` and letting `s → 1 / 2⁺`. The prime number theorem does not decide this case.

## Main statements

* `RokickiConstant.PNT.rho_irrational`: Rokicki's constant is irrational.
-/

set_option doc.verso true
set_option doc.verso.suggestions false

namespace RokickiConstant.PNT

/-- Rokicki's constant is irrational. This is `rho_irrational`, with the case of linearly growing
character sums handled by the prime number theorem in arithmetic progressions. -/
theorem rho_irrational : Irrational rho := by
  have h : rho = ∑' k : ℕ, (Real.rokickiDigit k : ℝ) / 2 ^ (k + 1) := by
    unfold rho Real.rokickiDigit
    congr 1
    funext k
    split_ifs <;> simp
  rw [h]
  refine irrational_tsum_div_two_pow Real.rokickiDigit_le_one fun p hp hd ↦ ?_
  have ha : Function.EventuallyPeriodic (fun k ↦ ZMod.χ₄ (oddPrime k)) p :=
    hd.mono fun n hn ↦ by simp only [χ₄_oddPrime, hn]
  obtain ⟨c, C, hC⟩ := ha.exists_abs_sum_sub_mul_le hp
  by_cases hc : (c : ℝ) = 0
  · exact RokickiConstant.not_exists_abs_sum_chi4_le ⟨C, fun n ↦ by simpa [hc] using hC n⟩
  · exact not_exists_abs_sum_chi4_sub_mul_le ⟨c, hc, C, hC⟩

end RokickiConstant.PNT
