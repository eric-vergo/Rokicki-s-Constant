/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import RokickiConstant.Defs
import RokickiConstant.General.CharacterSums
import RokickiConstant.General.Expansion

/-!
# Irrational numbers from quadratic characters at the primes

Let `χ` be a nonprincipal quadratic Dirichlet character modulo `q`, let `p₀ = 2 < p₁ < ⋯` be the
primes, let `b ≥ 2` be a base, and let `f` encode the values of `χ` as digits `f z < b` with
`f 1 ≠ f (-1)`. Then
$$`\sum_{k \geq 0} \frac{f(\chi(p_k))}{b^{k+1}}`
is irrational (`DirichletCharacter.IsQuadratic.irrational_tsum`). If the digits were eventually
periodic, so would be `χ(pₖ)` (which is nonzero for all large `k`), hence its partial sums would
be `c · n + O(1)`, contradicting `RokickiConstant.General.CharacterSums`.

Consequences:

* `Real.irrational_rokickiConstantBase`: Rokicki's digit sequence read in any base `b ≥ 2`
  gives an irrational number; `b = 2` is Rokicki's constant. The digits are the invariant, the
  base is only a way of reading them.
* `Real.irrational_legendreConstant`: for an odd prime `ℓ`, the number whose `k`-th digit records
  whether `pₖ` is a quadratic non-residue modulo `ℓ` is irrational.
* `Real.irrational_rokickiConstant'`: a second proof that Rokicki's constant is irrational, as a
  special case of the general theorem.

## Main statements

* `DirichletCharacter.IsQuadratic.irrational_tsum`
* `Real.irrational_rokickiConstantBase`
* `Real.irrational_legendreConstant`

## Tags

Dirichlet character, quadratic character, irrational, Legendre symbol
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Function

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

namespace DirichletCharacter.IsQuadratic

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsQuadratic)
include hχ

/-- If the digits `f (χ pₖ)` are eventually periodic and `f 1 ≠ f (-1)`, then `k ↦ χ(pₖ)` is
eventually periodic with the same period. -/
theorem eventuallyPeriodic_apply_nthPrime {f : ℂ → ℕ} (hf : f 1 ≠ f (-1)) {p : ℕ}
    (h : EventuallyPeriodic (fun k ↦ f (χ (nthPrime k))) p) :
    EventuallyPeriodic (fun k ↦ χ (nthPrime k)) p := by
  sorry

/-- The sequence `k ↦ χ(pₖ)` of a nonprincipal quadratic character is not eventually periodic. -/
theorem not_eventuallyPeriodic_apply_nthPrime (hχ₁ : χ ≠ 1) {p : ℕ} (hp : 0 < p) :
    ¬ EventuallyPeriodic (fun k ↦ χ (nthPrime k)) p := by
  sorry

/-- **Irrationality from a quadratic character.** For a nonprincipal quadratic character `χ`, a
base `b ≥ 2` and digits `f (χ pₖ) < b` with `f 1 ≠ f (-1)`, the number `∑ₖ f (χ pₖ) / b ^ (k + 1)`
is irrational. -/
theorem irrational_tsum (hχ₁ : χ ≠ 1) {b : ℕ} (hb : 2 ≤ b) {f : ℂ → ℕ} (hfb : ∀ z, f z < b)
    (hf : f 1 ≠ f (-1)) :
    Irrational (∑' k : ℕ, (f (χ (nthPrime k)) : ℝ) / b ^ (k + 1)) := by
  sorry

end DirichletCharacter.IsQuadratic

namespace Real

/-- Rokicki's digit sequence read in base `b`: `∑ₖ rokickiDigit k / b ^ (k + 1)`. For `b = 2` this
is Rokicki's constant. -/
noncomputable def rokickiConstantBase (b : ℕ) : ℝ := ∑' k : ℕ, (rokickiDigit k : ℝ) / b ^ (k + 1)

/-- In base `2`, `rokickiConstantBase 2 = ρ`. -/
theorem rokickiConstantBase_two : rokickiConstantBase 2 = rokickiConstant := by
  sorry

/-- Rokicki's digit sequence is not eventually periodic. -/
theorem not_eventuallyPeriodic_rokickiDigit {p : ℕ} (hp : 0 < p) :
    ¬ EventuallyPeriodic rokickiDigit p := by
  sorry

/-- **Rokicki's digits give an irrational number in every base** `b ≥ 2`. -/
theorem irrational_rokickiConstantBase {b : ℕ} (hb : 2 ≤ b) :
    Irrational (rokickiConstantBase b) := by
  sorry

/-- A second proof that Rokicki's constant is irrational, as a special case of the general
theorem. -/
theorem irrational_rokickiConstant' : Irrational rokickiConstant := by
  sorry

/-- The Legendre symbol modulo an odd prime `ℓ`, as a Dirichlet character with values in `ℂ`. -/
noncomputable def legendreChar (ℓ : ℕ) [Fact ℓ.Prime] : DirichletCharacter ℂ ℓ :=
  (quadraticChar (ZMod ℓ)).ringHomComp (Int.castRingHom ℂ)

/-- The Legendre character is quadratic. -/
theorem isQuadratic_legendreChar (ℓ : ℕ) [Fact ℓ.Prime] : (legendreChar ℓ).IsQuadratic := by
  sorry

/-- The Legendre character is nonprincipal for odd `ℓ`. -/
theorem legendreChar_ne_one (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) : legendreChar ℓ ≠ 1 := by
  sorry

/-- The **Legendre constant** of an odd prime `ℓ` in base `b`: the number whose `k`-th base-`b`
digit is `1` if the `k`-th prime `pₖ` is a quadratic non-residue modulo `ℓ`, and `0` otherwise
(so the digit is `0` for `pₖ = ℓ` and for quadratic residues). For `ℓ = 2` and `b = 2`, compare
Rokicki's constant, which encodes the residue of `pₖ` modulo `4` instead. -/
noncomputable def legendreConstant (ℓ b : ℕ) [Fact ℓ.Prime] : ℝ :=
  ∑' k : ℕ, (if legendreChar ℓ (nthPrime k) = -1 then (1 : ℝ) else 0) / b ^ (k + 1)

/-- **Legendre constants are irrational**: for every odd prime `ℓ` and base `b ≥ 2`. -/
theorem irrational_legendreConstant (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) {b : ℕ} (hb : 2 ≤ b) :
    Irrational (legendreConstant ℓ b) := by
  sorry

end Real
