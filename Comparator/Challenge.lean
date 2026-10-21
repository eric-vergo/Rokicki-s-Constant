/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib

/-!
# Challenge: Rokicki's constant is irrational

Let `p₁ = 2 < p₂ = 3 < p₃ = 5 < ⋯` be the primes, so that `Nat.nth Nat.Prime (k + 1)` is `pₖ₊₂`.
**Rokicki's constant** is `ρ = ∑ₖ [pₖ₊₂ ≡ 3 (mod 4)] / 2 ^ (k + 1) ≈ 0.700400137965…`, the number
whose binary digits record, odd prime by odd prime, whether `p ≡ 3 (mod 4)`. Prove that `ρ` is
irrational.

The solution is in `Comparator/Solution.lean`, which differs from this file only in its imports
and in the proof of `rho_irrational`.
-/

/-- **Rokicki's constant** `ρ = ∑ₖ [pₖ₊₂ ≡ 3 (mod 4)] / 2 ^ (k + 1)`. -/
noncomputable def rho : ℝ :=
  ∑' k : ℕ, (if Nat.nth Nat.Prime (k + 1) % 4 = 3 then (1 : ℝ) else 0) / 2 ^ (k + 1)

/-- Rokicki's constant is irrational. -/
theorem rho_irrational : Irrational rho := by
  sorry
