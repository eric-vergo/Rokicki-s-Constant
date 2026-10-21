/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import RokickiConstant.Irrational

/-!
# Comparator statements

This file restates the specification of the project in the most direct terms possible, without
reference to the definitions used in the development, and checks that the development meets it.
Reading this file against the specification is all that is needed to audit the project: the
theorems here are proved only by appeal to the main results, and `lake build` confirms that the
statements match.

The specification. Let `p₁ = 2 < p₂ = 3 < p₃ = 5 < ⋯` be the primes, so that `pₖ₊₂` is
`Nat.nth Nat.Prime (k + 1)` for `k = 0, 1, 2, …`. Rokicki's constant is
`ρ = ∑ₖ [pₖ₊₂ ≡ 3 (mod 4)] / 2 ^ (k + 1)`, the limit of `A362583 (n + 1) / 2 ^ n`, where
`A362583` is given by the recurrence `a (n + 1) = 2 a n + [pₙ₊₂ ≡ 3 (mod 4)]` with `a 0 = 0`.
The comparator statement is that `ρ` is irrational.

## Main definitions

* `RokickiConstant.Comparator.rokickiConstantSpec`: `ρ` written out as the specified series.
* `RokickiConstant.Comparator.oeisA362583Spec`: `A362583` by its OEIS recurrence.

## Main statements

* `RokickiConstant.Comparator.rokickiConstant_eq_spec`: `Real.rokickiConstant` is the specified
  series.
* `RokickiConstant.Comparator.oeisA362583_eq_spec`: `Real.oeisA362583` is the OEIS recurrence.
* `RokickiConstant.Comparator.tendsto_oeisA362583Spec_div_two_pow`: `A362583 (n + 1) / 2 ^ n → ρ`.
* `RokickiConstant.Comparator.irrational_rokickiConstant`: **the comparator statement**,
  `Irrational Real.rokickiConstant`.
* `RokickiConstant.Comparator.irrational_rokickiConstantSpec`: the same for the series as
  written.

## Tags

Rokicki's constant, comparator, irrational
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology

namespace RokickiConstant.Comparator

/-- Rokicki's constant exactly as specified: the sum over `k ≥ 0` of `1 / 2 ^ (k + 1)` when the
prime `Nat.nth Nat.Prime (k + 1)` (that is, `pₖ₊₂`) is `3` modulo `4`. -/
noncomputable def rokickiConstantSpec : ℝ :=
  ∑' k : ℕ, (if Nat.nth Nat.Prime (k + 1) % 4 = 3 then (1 : ℝ) else 0) / 2 ^ (k + 1)

/-- The OEIS sequence A362583 (shifted by one index) by its defining recurrence: append the bit
`[pₙ₊₂ ≡ 3 (mod 4)]` to the binary expansion of the previous term. -/
noncomputable def oeisA362583Spec : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * oeisA362583Spec n + if Nat.nth Nat.Prime (n + 1) % 4 = 3 then 1 else 0

/-- The constant of the development is the specified series. -/
theorem rokickiConstant_eq_spec : Real.rokickiConstant = rokickiConstantSpec := by
  unfold Real.rokickiConstant rokickiConstantSpec
  congr 1
  funext k
  unfold Real.rokickiDigit
  split_ifs <;> simp

/-- The sequence of the development is the OEIS recurrence. -/
theorem oeisA362583_eq_spec (n : ℕ) : Real.oeisA362583 n = oeisA362583Spec n := by
  induction n with
  | zero => simp [Real.oeisA362583, oeisA362583Spec]
  | succ n ih =>
    rw [oeisA362583Spec, ← ih]
    unfold Real.oeisA362583 Real.rokickiDigit
    rw [Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' := Finset.mem_range.mp hk
      rw [show n + 1 - 1 - k = (n - 1 - k) + 1 by omega, pow_succ]
      ring
    · simp

/-- Tom Rokicki's observation, for the sequence as specified: `A362583 (n + 1) / 2 ^ n → ρ`. -/
theorem tendsto_oeisA362583Spec_div_two_pow :
    Tendsto (fun n : ℕ ↦ (oeisA362583Spec n : ℝ) / 2 ^ n) atTop (𝓝 rokickiConstantSpec) := by
  rw [← rokickiConstant_eq_spec]
  simpa [← oeisA362583_eq_spec] using Real.tendsto_oeisA362583_div_two_pow

/-- **The comparator statement**: Rokicki's constant is irrational. -/
theorem irrational_rokickiConstant : Irrational Real.rokickiConstant :=
  Real.irrational_rokickiConstant

/-- The comparator statement for the series as written. -/
theorem irrational_rokickiConstantSpec : Irrational rokickiConstantSpec :=
  rokickiConstant_eq_spec ▸ irrational_rokickiConstant

end RokickiConstant.Comparator
