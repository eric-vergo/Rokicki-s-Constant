/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import RokickiConstant.EulerProduct

/-!
# The Euler product of `L(s, χ)` for an arbitrary Dirichlet character

This generalizes `RokickiConstant.EulerProduct` from `χ₄` to any Dirichlet character `χ`
modulo `q`, and from the odd primes to all primes `p₀ = 2 < p₁ = 3 < ⋯`, written
`Nat.nth Nat.Prime k`. We set `zₖ(s) = χ(pₖ) pₖ ^ (-s)`, `primePart χ s = ∑ₖ zₖ(s)` and
`primePowerPart χ s = ∑ₖ (-log (1 - zₖ(s)) - zₖ(s))`, so that
`L(s, χ) = exp (primePart χ s + primePowerPart χ s)` for `re s > 1`.

The prime-power part is holomorphic on `re s > 1 / 2` and bounded on `re s ≥ 1` for every `χ`.
Its real part tends to `+∞` as `s → 1 / 2⁺` along the reals when `χ` is *quadratic*, that is,
takes values in `{0, 1, -1}`: then `χ(p)² = 1` for all but the finitely many primes dividing
`q`, and the `m = 2` terms `∑ₚ p ^ (-2σ) / 2` of the prime-power part diverge as `σ → 1 / 2⁺`.

## Main definitions

* `DirichletCharacter.primeTerm χ k s`: `χ(pₖ) pₖ ^ (-s)`.
* `DirichletCharacter.primePart χ s`, `DirichletCharacter.primePowerPart χ s`.

## Main statements

* `DirichletCharacter.exp_primePart_add_primePowerPart`: the Euler product.
* `DirichletCharacter.differentiableOn_primePowerPart`, `exists_norm_primePowerPart_le`.
* `DirichletCharacter.IsQuadratic.tendsto_re_primePowerPart`: the blow-up at `1 / 2`.
* `tendsto_tsum_nthPrime_rpow_neg`: `∑ₖ pₖ ^ (-σ) → +∞` as `σ → 1⁺`.

## Tags

Dirichlet character, Euler product, quadratic character
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

section Primes

/-- `∑ₖ 1 / pₖ` diverges. -/
theorem not_summable_nthPrime_inv : ¬ Summable fun k : ℕ ↦ ((nthPrime k : ℝ))⁻¹ := by
  sorry

/-- `∑ₖ pₖ ^ r` converges for `r < -1`. -/
theorem summable_nthPrime_rpow {r : ℝ} (hr : r < -1) :
    Summable fun k : ℕ ↦ (nthPrime k : ℝ) ^ r := by
  sorry

/-- `∑ₖ pₖ ^ (-σ) → +∞` as `σ → 1⁺`. -/
theorem tendsto_tsum_nthPrime_rpow_neg :
    Tendsto (fun σ : ℝ ↦ ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ)) (𝓝[>] (1 : ℝ)) atTop := by
  sorry

/-- A sum over the primes is a sum over `k` of the `k`-th prime. -/
theorem tsum_primes_eq_tsum_nthPrime {F : Nat.Primes → ℂ} (hF : Summable F) :
    ∑' p : Nat.Primes, F p = ∑' k : ℕ, F ⟨nthPrime k, Nat.prime_nth_prime k⟩ := by
  sorry

end Primes

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The term `zₖ(s) = χ(pₖ) pₖ ^ (-s)` of the Dirichlet series of `χ` over the primes. -/
noncomputable def primeTerm (k : ℕ) (s : ℂ) : ℂ := χ (nthPrime k) * (nthPrime k : ℂ) ^ (-s)

/-- `‖zₖ(s)‖ ≤ pₖ ^ (-re s)`. -/
theorem norm_primeTerm_le (k : ℕ) (s : ℂ) : ‖χ.primeTerm k s‖ ≤ (nthPrime k : ℝ) ^ (-s.re) := by
  sorry

/-- `‖zₖ(s)‖ ≤ 3 / 4` when `re s > 1 / 2`. -/
theorem norm_primeTerm_le_three_quarters (k : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖χ.primeTerm k s‖ ≤ 3 / 4 := by
  sorry

/-- The prime part `∑ₖ χ(pₖ) pₖ ^ (-s)` of the logarithm of the Euler product. -/
noncomputable def primePart (s : ℂ) : ℂ := ∑' k : ℕ, χ.primeTerm k s

/-- The prime-power part `∑ₖ (-log (1 - zₖ(s)) - zₖ(s))` of the logarithm of the Euler product,
the contribution of the prime powers `pₖ ^ m`, `m ≥ 2`. -/
noncomputable def primePowerPart (s : ℂ) : ℂ :=
  ∑' k : ℕ, (-log (1 - χ.primeTerm k s) - χ.primeTerm k s)

/-- For `1 / 2 < σ₀ ≤ re s`, the `k`-th term of `primePowerPart χ s` has norm at most
`2 pₖ ^ (-2σ₀)`. -/
theorem norm_primePowerPart_term_le (k : ℕ) {σ₀ : ℝ} {s : ℂ} (hσ₀ : 1 / 2 < σ₀)
    (hs : σ₀ ≤ s.re) :
    ‖-log (1 - χ.primeTerm k s) - χ.primeTerm k s‖ ≤ 2 * (nthPrime k : ℝ) ^ (-(2 * σ₀)) := by
  sorry

/-- The prime part converges absolutely for `re s > 1`. -/
theorem summable_primeTerm {s : ℂ} (hs : 1 < s.re) : Summable fun k ↦ χ.primeTerm k s := by
  sorry

/-- The prime-power part converges absolutely for `re s > 1 / 2`. -/
theorem summable_primePowerPart_term {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun k ↦ -log (1 - χ.primeTerm k s) - χ.primeTerm k s := by
  sorry

/-- **Euler product** for `L(s, χ)` in exponential form, `re s > 1`. -/
theorem exp_primePart_add_primePowerPart {s : ℂ} (hs : 1 < s.re) :
    exp (χ.primePart s + χ.primePowerPart s) = LFunction χ s := by
  sorry

/-- The prime-power part is holomorphic on `re s > 1 / 2`. -/
theorem differentiableOn_primePowerPart :
    DifferentiableOn ℂ χ.primePowerPart {s : ℂ | 1 / 2 < s.re} := by
  sorry

/-- The prime-power part is bounded on the closed half-plane `re s ≥ 1`. -/
theorem exists_norm_primePowerPart_le :
    ∃ M : ℝ, ∀ s : ℂ, 1 ≤ s.re → ‖χ.primePowerPart s‖ ≤ M := by
  sorry

/-- A quadratic character vanishes at `pₖ` only for the finitely many primes dividing `q`:
`χ(pₖ) = 0` if and only if `pₖ ∣ q`. -/
theorem apply_nthPrime_eq_zero_iff (k : ℕ) : χ (nthPrime k) = 0 ↔ nthPrime k ∣ q := by
  sorry

/-- `χ(pₖ) ≠ 0` for all sufficiently large `k`. -/
theorem eventually_apply_nthPrime_ne_zero : ∀ᶠ k in atTop, χ (nthPrime k) ≠ 0 := by
  sorry

/-- For a quadratic character, `χ(pₖ)² ∈ {0, 1}`, and it is `1` unless `pₖ ∣ q`. -/
theorem IsQuadratic.sq_apply_nthPrime (hχ : χ.IsQuadratic) (k : ℕ) :
    χ (nthPrime k) ^ 2 = if nthPrime k ∣ q then 0 else 1 := by
  sorry

/-- For a quadratic character and real `σ > 1 / 2`, the real part of `primePowerPart χ σ` is at
least `∑ₖ pₖ ^ (-2σ) / 2` minus a constant depending only on `q`. -/
theorem IsQuadratic.le_re_primePowerPart (hχ : χ.IsQuadratic) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' k : ℕ, (nthPrime k : ℝ) ^ (-(2 * σ))) / 2 - (q.primeFactors.card : ℝ) / 2 -
        2 * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-3 / 2 : ℝ) ≤
      (χ.primePowerPart σ).re := by
  sorry

/-- For a quadratic character, `re (primePowerPart χ σ) → +∞` as `σ → 1 / 2⁺`. -/
theorem IsQuadratic.tendsto_re_primePowerPart (hχ : χ.IsQuadratic) :
    Tendsto (fun σ : ℝ ↦ (χ.primePowerPart σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop := by
  sorry

end DirichletCharacter
