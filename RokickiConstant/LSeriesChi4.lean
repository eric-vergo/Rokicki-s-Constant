/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.SumPrimeReciprocals
import RokickiConstant.Defs
import RokickiConstant.PartialSums

/-!
# The character sums `∑ χ₄ p` over primes are neither bounded nor linear

Let `χ₄` be the nontrivial Dirichlet character modulo `4`, so that `χ₄ p = 1` for primes
`p ≡ 1 (mod 4)` and `χ₄ p = -1` for primes `p ≡ 3 (mod 4)`. Writing `3 = p₂ < p₃ < ⋯` for the
odd primes, we show that the partial sums `S n = ∑_{k < n} χ₄ pₖ₊₂` are
* not of the form `c · n + O(1)` with `c ≠ 0`
  (`RokickiConstant.not_exists_abs_sum_chi4_sub_mul_le`), and
* not bounded (`RokickiConstant.not_exists_abs_sum_chi4_le`).

Both statements come from the Euler product of `L(s, χ₄)` in the form
$$
  L(s, χ₄) = \exp\Big(\sum_p χ₄(p) p^{-s} + \sum_p \sum_{m ≥ 2} \frac{χ₄(p)^m p^{-ms}}{m}\Big),
  \qquad \operatorname{re} s > 1,
$$
which Mathlib provides as `DirichletCharacter.LSeries_eulerProduct_exp_log`. The first sum is
`primePart s`, the second `primePowerPart s`.

* If `S n = c · n + O(1)` with `c ≠ 0`, summation by parts gives
  `primePart σ = c ∑_p p^{-σ} + O(1)` for real `σ > 1`, which tends to `±∞` as `σ → 1⁺`
  because `∑_p 1 / p` diverges, while `primePowerPart` stays bounded. So `L(σ, χ₄) → 0` or
  `∞`, contradicting `L(1, χ₄) ≠ 0` and the continuity of `L(·, χ₄)` at `1`.
* If `S n` is bounded, summation by parts (`abelSeries`) continues `primePart` holomorphically to
  `re s > 0`, and `primePowerPart` is holomorphic on `re s > 1 / 2`; by the identity theorem
  `L(s, χ₄) = exp (abelSeries s + primePowerPart s)` on `re s > 1 / 2`. But the real part of
  `primePowerPart σ` tends to `+∞` as `σ → 1 / 2⁺` (its `m = 2` terms are `∑_p p^{-2σ} / 2`),
  so `|L(σ, χ₄)| → ∞`, contradicting the continuity of the entire function `L(·, χ₄)` at `1 / 2`.

Neither argument uses the prime number theorem, nor Dirichlet's theorem on primes in
arithmetic progressions.

## Main definitions

* `RokickiConstant.chi4`: the nontrivial Dirichlet character modulo `4` with values in `ℂ`.
* `RokickiConstant.primePart s`: `∑ₖ χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)`.
* `RokickiConstant.primePowerPart s`: `∑ₖ ∑_{m ≥ 2} χ₄ pₖ₊₂ ^ m · pₖ₊₂ ^ (-m s) / m`.

## Main statements

* `RokickiConstant.exp_primePart_add_primePowerPart`: the Euler product in the form above.
* `RokickiConstant.not_exists_abs_sum_chi4_sub_mul_le`: the partial sums of `χ₄` over the odd
  primes are not `c · n + O(1)` with `c ≠ 0`.
* `RokickiConstant.not_exists_abs_sum_chi4_le`: the partial sums of `χ₄` over the odd primes are
  not bounded.

## Tags

Dirichlet character, L-function, Euler product, Chebyshev bias
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

namespace RokickiConstant

open Real

/-- The nontrivial Dirichlet character modulo `4`, with values in `ℂ`: `chi4 n = 1` if
`n ≡ 1 (mod 4)`, `-1` if `n ≡ 3 (mod 4)`, and `0` for even `n`. -/
noncomputable def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem chi4_natCast (n : ℕ) : chi4 n = (ZMod.χ₄ n : ℂ) := by
  sorry

theorem chi4_ne_one : chi4 ≠ 1 := by
  sorry

theorem chi4_oddPrime (k : ℕ) : chi4 (oddPrime k) = 1 - 2 * (rokickiDigit k : ℂ) := by
  sorry

theorem chi4_oddPrime_sq (k : ℕ) : chi4 (oddPrime k) ^ 2 = 1 := by
  sorry

theorem norm_chi4_oddPrime (k : ℕ) : ‖chi4 (oddPrime k)‖ = 1 := by
  sorry

theorem chi4_two : chi4 2 = 0 := by
  sorry

/-- A sum over all primes splits as the term at `2` plus a sum over the odd primes. -/
theorem tsum_primes_eq_add_tsum_oddPrime {F : Nat.Primes → ℂ} (hF : Summable F) :
    ∑' p : Nat.Primes, F p = F ⟨2, Nat.prime_two⟩ + ∑' k : ℕ, F ⟨oddPrime k, oddPrime_prime k⟩ := by
  sorry

theorem not_summable_oddPrime_inv : ¬ Summable fun k : ℕ ↦ ((oddPrime k : ℝ))⁻¹ := by
  sorry

theorem summable_oddPrime_rpow {r : ℝ} (hr : r < -1) :
    Summable fun k : ℕ ↦ (oddPrime k : ℝ) ^ r := by
  sorry

/-- `∑ₖ pₖ₊₂ ^ (-σ) → ∞` as `σ → 1⁺`, since `∑_p 1 / p` diverges. -/
theorem tendsto_tsum_oddPrime_rpow_neg :
    Tendsto (fun σ : ℝ ↦ ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ)) (𝓝[>] (1 : ℝ)) atTop := by
  sorry

section EulerProduct

/-- The prime part `∑ₖ χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)` of the logarithm of the Euler product of
`L(s, χ₄)`; absolutely convergent for `1 < re s`. -/
noncomputable def primePart (s : ℂ) : ℂ := ∑' k : ℕ, chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s)

/-- The prime power part `∑ₖ ∑_{m ≥ 2} χ₄ pₖ₊₂ ^ m · pₖ₊₂ ^ (-m s) / m` of the logarithm of the
Euler product of `L(s, χ₄)`; absolutely convergent for `1 / 2 < re s`. -/
noncomputable def primePowerPart (s : ℂ) : ℂ :=
  ∑' k : ℕ, ∑' m : ℕ,
    chi4 (oddPrime k) ^ (m + 2) * ((oddPrime k : ℂ) ^ (-s)) ^ (m + 2) / (m + 2)

theorem norm_oddPrime_cpow_neg_lt_one {k : ℕ} {s : ℂ} (hs : 0 < s.re) :
    ‖(oddPrime k : ℂ) ^ (-s)‖ < 1 := by
  sorry

/-- The Taylor expansion `-log (1 - z) = z + ∑_{m ≥ 2} z ^ m / m` at `z = χ₄ p · p ^ (-s)`. -/
theorem neg_log_one_sub_eq (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    -log (1 - chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s)) =
      chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s) +
        ∑' m : ℕ, chi4 (oddPrime k) ^ (m + 2) * ((oddPrime k : ℂ) ^ (-s)) ^ (m + 2) / (m + 2) := by
  sorry

theorem summable_primePart {s : ℂ} (hs : 1 < s.re) :
    Summable fun k : ℕ ↦ chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s) := by
  sorry

/-- For `1 / 2 < re s`, the inner sums of `primePowerPart` are dominated by `2 · p ^ (-2 re s)`. -/
theorem norm_tsum_primePowerPart_le (k : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖∑' m : ℕ, chi4 (oddPrime k) ^ (m + 2) * ((oddPrime k : ℂ) ^ (-s)) ^ (m + 2) / (m + 2)‖ ≤
      2 * (oddPrime k : ℝ) ^ (-2 * s.re) := by
  sorry

theorem summable_primePowerPart {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun k : ℕ ↦
      ∑' m : ℕ, chi4 (oddPrime k) ^ (m + 2) * ((oddPrime k : ℂ) ^ (-s)) ^ (m + 2) / (m + 2) := by
  sorry

/-- **Euler product** for `L(s, χ₄)` in exponential form, `1 < re s`. -/
theorem exp_primePart_add_primePowerPart {s : ℂ} (hs : 1 < s.re) :
    exp (primePart s + primePowerPart s) = DirichletCharacter.LFunction chi4 s := by
  sorry

theorem differentiableOn_primePowerPart :
    DifferentiableOn ℂ primePowerPart {s : ℂ | 1 / 2 < s.re} := by
  sorry

/-- `primePowerPart` is bounded on the closed half-plane `1 ≤ re s`. -/
theorem exists_norm_primePowerPart_le : ∃ M : ℝ, ∀ s : ℂ, 1 ≤ s.re → ‖primePowerPart s‖ ≤ M := by
  sorry

/-- For real `σ > 1 / 2`, the real part of `primePowerPart σ` is at least
`∑ₖ pₖ₊₂ ^ (-2σ) / 2` minus a constant, because `χ₄ p ^ 2 = 1`. -/
theorem le_re_primePowerPart {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' k : ℕ, (oddPrime k : ℝ) ^ (-2 * σ)) / 2 - 2 * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-3 / 2 : ℝ) ≤
      (primePowerPart σ).re := by
  sorry

/-- The real part of `primePowerPart σ` tends to `+∞` as `σ → 1 / 2⁺`. -/
theorem tendsto_re_primePowerPart :
    Tendsto (fun σ : ℝ ↦ (primePowerPart σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop := by
  sorry

end EulerProduct

section Linear

/-- Summation by parts: if `∑_{k < n} χ₄ pₖ₊₂ = c · n + O(1)` then
`re (primePart σ) = c ∑ₖ pₖ₊₂ ^ (-σ) + O(1)` for real `σ > 1`. -/
theorem abs_re_primePart_sub_mul_tsum_le {c C : ℝ}
    (h : ∀ n, |(∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)) - c * n| ≤ C) {σ : ℝ} (hσ : 1 < σ) :
    |(primePart σ).re - c * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ)| ≤ 2 * C := by
  sorry

theorem tendsto_norm_LFunction_chi4_one :
    Tendsto (fun σ : ℝ ↦ ‖DirichletCharacter.LFunction chi4 σ‖) (𝓝[>] (1 : ℝ))
      (𝓝 ‖DirichletCharacter.LFunction chi4 1‖) := by
  sorry

theorem LFunction_chi4_one_ne_zero : DirichletCharacter.LFunction chi4 1 ≠ 0 := by
  sorry

/-- The partial sums `∑_{k < n} χ₄ pₖ₊₂` are not of the form `c · n + O(1)` with `c ≠ 0`. -/
theorem not_exists_abs_sum_chi4_sub_mul_le :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n,
      |(∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)) - c * n| ≤ C := by
  sorry

end Linear

section Bounded

variable {C : ℝ} (hC : ∀ n, |∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)| ≤ C)
include hC

/-- Under bounded partial sums, the Abel series of `χ₄` over the odd primes agrees with
`primePart` for `1 < re s`. -/
theorem abelSeries_eq_primePart {s : ℂ} (hs : 1 < s.re) :
    abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime s = primePart s := by
  sorry

theorem differentiableOn_abelSeries_chi4 :
    DifferentiableOn ℂ (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime) {s : ℂ | 0 < s.re} := by
  sorry

/-- **Analytic continuation of the Euler product.** Under bounded partial sums,
`L(s, χ₄) = exp (abelSeries s + primePowerPart s)` for all `1 / 2 < re s`. -/
theorem exp_abelSeries_add_primePowerPart {s : ℂ} (hs : 1 / 2 < s.re) :
    exp (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime s + primePowerPart s) =
      DirichletCharacter.LFunction chi4 s := by
  sorry

theorem tendsto_re_abelSeries_chi4 :
    Tendsto (fun σ : ℝ ↦ (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime σ).re)
      (𝓝[>] (1 / 2 : ℝ))
      (𝓝 (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime (1 / 2 : ℝ)).re) := by
  sorry

omit hC in
theorem tendsto_norm_LFunction_chi4_one_half :
    Tendsto (fun σ : ℝ ↦ ‖DirichletCharacter.LFunction chi4 σ‖) (𝓝[>] (1 / 2 : ℝ))
      (𝓝 ‖DirichletCharacter.LFunction chi4 (1 / 2 : ℝ)‖) := by
  sorry

end Bounded

/-- The partial sums `∑_{k < n} χ₄ pₖ₊₂` are unbounded. -/
theorem not_exists_abs_sum_chi4_le :
    ¬ ∃ C : ℝ, ∀ n, |∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)| ≤ C := by
  sorry

end RokickiConstant
