/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RokickiConstant.General.EulerProduct

/-!
# Partial sums of a quadratic character over the primes are neither bounded nor linear

Let `χ` be a nonprincipal quadratic Dirichlet character modulo `q` (values in `{0, 1, -1}`),
let `p₀ = 2 < p₁ < ⋯` be the primes and `S n = ∑_{k < n} χ(pₖ)`. We prove

* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_sub_mul_le`: `S n` is not of the form
  `c · n + O(1)` with `c ≠ 0`;
* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_le`: `S n` is not bounded;

and the same two statements for the sums `∑_{p < x} χ(p)` over the primes below `x`
(`Nat.primesBelow`). The proofs are those of `RokickiConstant.CharacterSums` for `χ₄`, with the
Euler product `L(s, χ) = exp (primePart χ s + primePowerPart χ s)` of
`RokickiConstant.General.EulerProduct`: the linear case is ruled out at `s → 1⁺` using
`L(1, χ) ≠ 0`, and the bounded case by continuing the Euler product to `re s > 1 / 2` through the
Abel series and letting `s → 1 / 2⁺`, where the prime-power part blows up while the entire
function `L(·, χ)` stays bounded.

Neither argument uses the prime number theorem, nor Dirichlet's theorem on primes in
arithmetic progressions.

## Main statements

* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_sub_mul_le`
* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_le`
* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_primesBelow_sub_mul_le`
* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_primesBelow_le`

## Tags

Dirichlet character, quadratic character, L-function, Chebyshev bias
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- If `exp (F σ) = L(σ, χ)` to the right of `x`, then `exp (re (F σ)) → ‖L(x, χ)‖` as
`σ → x⁺`, for nonprincipal `χ`. -/
theorem tendsto_exp_re_of_exp_eq_LFunction (hχ : χ ≠ 1) {F : ℂ → ℂ} {x : ℝ}
    (hF : ∀ σ : ℝ, x < σ → exp (F σ) = LFunction χ σ) :
    Tendsto (fun σ : ℝ ↦ Real.exp (F σ).re) (𝓝[>] x) (𝓝 ‖LFunction χ x‖) := by
  sorry

/-- The sums over the primes below `x` are partial sums of the sums over `k`. -/
theorem sum_primesBelow_eq (x : ℕ) :
    ∑ p ∈ Nat.primesBelow x, χ p = ∑ k ∈ range (Nat.primeCounting' x), χ (nthPrime k) := by
  sorry

namespace IsQuadratic

variable {χ} (hχ : χ.IsQuadratic)
include hχ

/-- Summation by parts: if `∑_{k < n} χ(pₖ) = c · n + O(1)` then
`re (primePart χ σ) = c ∑ₖ pₖ ^ (-σ) + O(1)` for real `σ > 1`. -/
theorem abs_re_primePart_sub_mul_tsum_le {c C : ℝ}
    (h : ∀ n, ‖(∑ k ∈ range n, χ (nthPrime k)) - c * n‖ ≤ C) {σ : ℝ} (hσ : 1 < σ) :
    |(χ.primePart σ).re - c * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ)| ≤ 2 * C := by
  sorry

/-- The partial sums `∑_{k < n} χ(pₖ)` of a nonprincipal quadratic character are not of the form
`c · n + O(1)` with `c ≠ 0`. -/
theorem not_exists_norm_sum_sub_mul_le (hχ₁ : χ ≠ 1) :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n, ‖(∑ k ∈ range n, χ (nthPrime k)) - c * n‖ ≤ C := by
  sorry

/-- Under bounded partial sums, the Abel series of `χ` over the primes is holomorphic on
`re s > 0`. -/
theorem differentiableOn_abelSeries {C : ℝ} (hC : ∀ n, ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C) :
    DifferentiableOn ℂ (abelSeries (fun k ↦ χ (nthPrime k)) nthPrime) {s : ℂ | 0 < s.re} := by
  sorry

/-- **Analytic continuation of the Euler product.** Under bounded partial sums,
`L(s, χ) = exp (abelSeries s + primePowerPart χ s)` for all `re s > 1 / 2`. -/
theorem exp_abelSeries_add_primePowerPart (hχ₁ : χ ≠ 1) {C : ℝ}
    (hC : ∀ n, ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C) {s : ℂ} (hs : 1 / 2 < s.re) :
    exp (abelSeries (fun k ↦ χ (nthPrime k)) nthPrime s + χ.primePowerPart s) =
      LFunction χ s := by
  sorry

/-- The partial sums `∑_{k < n} χ(pₖ)` of a nonprincipal quadratic character are unbounded. -/
theorem not_exists_norm_sum_le (hχ₁ : χ ≠ 1) :
    ¬ ∃ C : ℝ, ∀ n, ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C := by
  sorry

/-- The sums `∑_{p < x} χ(p)` of a nonprincipal quadratic character over the primes below `x`
are not of the form `c · π(x) + O(1)` with `c ≠ 0`. -/
theorem not_exists_norm_sum_primesBelow_sub_mul_le (hχ₁ : χ ≠ 1) :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ x,
      ‖(∑ p ∈ Nat.primesBelow x, χ p) - c * Nat.primeCounting' x‖ ≤ C := by
  sorry

/-- The sums `∑_{p < x} χ(p)` of a nonprincipal quadratic character over the primes below `x`
are unbounded. -/
theorem not_exists_norm_sum_primesBelow_le (hχ₁ : χ ≠ 1) :
    ¬ ∃ C : ℝ, ∀ x, ‖∑ p ∈ Nat.primesBelow x, χ p‖ ≤ C := by
  sorry

end IsQuadratic

end DirichletCharacter
