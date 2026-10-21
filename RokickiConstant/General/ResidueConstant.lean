/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import RokickiConstant.General.Irrational

/-!
# The residue constants `∑ₖ (pₖ mod q) / b ^ (k + 1)` are irrational for every `q ≥ 3`

For `q ≥ 3` and a base `b > q`, the number whose `k`-th base-`b` digit is the residue of the
`k`-th prime modulo `q` is irrational. If its digits were eventually periodic, so would be the
residues `pₖ mod q`, hence the values `χ(pₖ)` of any Dirichlet character modulo `q`; for a
nonprincipal quadratic `χ` this contradicts `RokickiConstant.General.CharacterSums`. The only
new ingredient is the existence of a nonprincipal quadratic character modulo every `q ≥ 3`:
the Legendre symbol modulo an odd prime factor of `q`, or `χ₄` if `q` is a power of `2`, lifted
to level `q` by `DirichletCharacter.changeLevel`.

## Main definitions

* `Real.residueConstant q b`: `∑ₖ (pₖ mod q) / b ^ (k + 1)`.

## Main statements

* `DirichletCharacter.exists_isQuadratic_ne_one`: every modulus `q ≥ 3` carries a nonprincipal
  quadratic Dirichlet character.
* `Real.irrational_residueConstant`: the residue constants are irrational.

## Tags

Dirichlet character, quadratic character, irrational, residues of primes
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Function

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

namespace DirichletCharacter

/-- Lifting a quadratic character to a higher level keeps it quadratic. -/
theorem IsQuadratic.changeLevel {n m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsQuadratic) (h : n ∣ m) : (changeLevel h χ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [changeLevel_eq_cast_of_dvd]
    exact hχ _
  · exact Or.inl (MulChar.map_nonunit _ ha)

/-- Lifting a nonprincipal character to a higher level keeps it nonprincipal. -/
theorem changeLevel_ne_one {n m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ n} (hχ : χ ≠ 1)
    (h : n ∣ m) : changeLevel h χ ≠ 1 :=
  (changeLevel_eq_one_iff h).not.mpr hχ

/-- **Every modulus `q ≥ 3` carries a nonprincipal quadratic Dirichlet character**: the Legendre
symbol modulo an odd prime factor of `q`, or `χ₄` when `q` is a power of `2`, lifted to level
`q`. -/
theorem exists_isQuadratic_ne_one (q : ℕ) [NeZero q] (hq : 3 ≤ q) :
    ∃ χ : DirichletCharacter ℂ q, χ.IsQuadratic ∧ χ ≠ 1 := by
  obtain h4 | ⟨ℓ, hℓ, hdvd, hodd⟩ := Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hq
  · exact ⟨changeLevel h4 RokickiConstant.chi4,
      IsQuadratic.changeLevel (ZMod.isQuadratic_χ₄.comp _) h4,
      changeLevel_ne_one RokickiConstant.chi4_ne_one h4⟩
  · have := Fact.mk hℓ
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      exact absurd hodd (by decide)
    exact ⟨changeLevel hdvd (Real.legendreChar ℓ),
      IsQuadratic.changeLevel (Real.isQuadratic_legendreChar ℓ) hdvd,
      changeLevel_ne_one (Real.legendreChar_ne_one ℓ hℓ2) hdvd⟩

/-- If the residues `pₖ mod q` are eventually periodic, so are the values `χ(pₖ)` of any
Dirichlet character modulo `q`. -/
theorem eventuallyPeriodic_apply_nthPrime_of_mod {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ}
    (h : EventuallyPeriodic (fun k ↦ nthPrime k % q) p) :
    EventuallyPeriodic (fun k ↦ χ (nthPrime k)) p := by
  filter_upwards [h] with k hk
  rw [← ZMod.natCast_mod, hk, ZMod.natCast_mod]

/-- The residues of the primes modulo `q ≥ 3` are not eventually periodic. -/
theorem not_eventuallyPeriodic_nthPrime_mod {q : ℕ} (hq : 3 ≤ q) {p : ℕ} (hp : 0 < p) :
    ¬ EventuallyPeriodic (fun k ↦ nthPrime k % q) p := by
  have : NeZero q := ⟨by omega⟩
  obtain ⟨χ, hχ, hχ₁⟩ := exists_isQuadratic_ne_one q hq
  exact fun hper ↦ IsQuadratic.not_eventuallyPeriodic_apply_nthPrime hχ hχ₁ hp
    (eventuallyPeriodic_apply_nthPrime_of_mod χ hper)

end DirichletCharacter

namespace Real

/-- The **residue constant** of modulus `q` in base `b`: the number whose `k`-th base-`b` digit
is the residue of the `k`-th prime modulo `q`. -/
noncomputable def residueConstant (q b : ℕ) : ℝ :=
  ∑' k : ℕ, ((nthPrime k % q : ℕ) : ℝ) / b ^ (k + 1)

/-- **Residue constants are irrational** for every modulus `q ≥ 3` and base `b > q`. -/
theorem irrational_residueConstant {q b : ℕ} (hq : 3 ≤ q) (hqb : q < b) :
    Irrational (residueConstant q b) := by
  exact irrational_tsum_div_pow (by omega) (fun k ↦ (Nat.mod_lt _ (by omega)).trans hqb)
    fun p hp ↦ DirichletCharacter.not_eventuallyPeriodic_nthPrime_mod hq hp

end Real
