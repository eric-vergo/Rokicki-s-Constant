/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib
import RokickiConstant.CharacterSums

/-!
# Solution: Rokicki's constant is irrational

Let `p₁ = 2 < p₂ = 3 < p₃ = 5 < ⋯` be the primes, so that `Nat.nth Nat.Prime (k + 1)` is `pₖ₊₂`.
**Rokicki's constant** is `ρ = ∑ₖ [pₖ₊₂ ≡ 3 (mod 4)] / 2 ^ (k + 1) ≈ 0.700400137965…`, the number
whose binary digits record, odd prime by odd prime, whether `p ≡ 3 (mod 4)`. Prove that `ρ` is
irrational.

This file differs from the challenge `Comparator/Challenge.lean` only in its imports and in the
proof of `rho_irrational`. If `ρ` were rational its binary digits would be eventually periodic
(`eventuallyPeriodic_of_tsum_div_two_pow_mem_range_ratCast`), hence so would the values
`χ₄ pₖ₊₂ = 1 - 2 · [pₖ₊₂ ≡ 3 (mod 4)]` of the nontrivial Dirichlet character modulo `4`, and the
partial sums of `χ₄` over the odd primes would be `c · n + O(1)`
(`Function.EventuallyPeriodic.exists_abs_sum_sub_mul_le`). But those partial sums are neither
bounded (`RokickiConstant.not_exists_abs_sum_chi4_le`) nor linear with nonzero slope
(`RokickiConstant.not_exists_abs_sum_chi4_sub_mul_le`), by the Euler product of `L(s, χ₄)`.
The proof does not use the prime number theorem.
-/

/-- **Rokicki's constant** `ρ = ∑ₖ [pₖ₊₂ ≡ 3 (mod 4)] / 2 ^ (k + 1)`. -/
noncomputable def rho : ℝ :=
  ∑' k : ℕ, (if Nat.nth Nat.Prime (k + 1) % 4 = 3 then (1 : ℝ) else 0) / 2 ^ (k + 1)

/-- Rokicki's constant is irrational. -/
theorem rho_irrational : Irrational rho := by
  have h : rho = ∑' k : ℕ, (Real.rokickiDigit k : ℝ) / 2 ^ (k + 1) := by
    unfold rho Real.rokickiDigit
    congr 1
    funext k
    split_ifs <;> simp
  rw [h]
  refine irrational_tsum_div_two_pow Real.rokickiDigit_le_one fun p hp hd ↦ ?_
  have ha : Function.EventuallyPeriodic (fun k ↦ ZMod.χ₄ (RokickiConstant.oddPrime k)) p :=
    hd.mono fun n hn ↦ by simp only [RokickiConstant.χ₄_oddPrime, hn]
  obtain ⟨c, C, hC⟩ := ha.exists_abs_sum_sub_mul_le hp
  by_cases hc : (c : ℝ) = 0
  · exact RokickiConstant.not_exists_abs_sum_chi4_le ⟨C, fun n ↦ by simpa [hc] using hC n⟩
  · exact RokickiConstant.not_exists_abs_sum_chi4_sub_mul_le ⟨c, hc, C, hC⟩
