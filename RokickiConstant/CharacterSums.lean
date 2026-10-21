/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RokickiConstant.EulerProduct

/-!
# The character sums `∑ χ₄ p` over primes are neither bounded nor linear

Writing `3 = p₂ < p₃ < ⋯` for the odd primes and `χ₄` for the nontrivial Dirichlet character
modulo `4`, we show that the partial sums `S n = ∑_{k < n} χ₄ pₖ₊₂` are
* not of the form `c · n + O(1)` with `c ≠ 0`
  (`RokickiConstant.not_exists_abs_sum_chi4_sub_mul_le`), and
* not bounded (`RokickiConstant.not_exists_abs_sum_chi4_le`).

Both statements come from the Euler product
`L(s, χ₄) = exp (primePart s + primePowerPart s)` for `re s > 1`
(`RokickiConstant.exp_primePart_add_primePowerPart`).

* If `S n = c · n + O(1)` with `c ≠ 0`, summation by parts gives
  `re (primePart σ) = c ∑_p p^{-σ} + O(1)` for real `σ > 1`, which tends to `±∞` as `σ → 1⁺`
  because `∑_p 1 / p` diverges, while `primePowerPart` stays bounded. So `‖L(σ, χ₄)‖ → 0` or
  `∞`, contradicting `L(1, χ₄) ≠ 0` and the continuity of `L(·, χ₄)` at `1`.
* If `S n` is bounded, summation by parts (`abelSeries`) continues `primePart` holomorphically to
  `re s > 0`, and `primePowerPart` is holomorphic on `re s > 1 / 2`; by the identity theorem
  `L(s, χ₄) = exp (abelSeries s + primePowerPart s)` on `re s > 1 / 2`. But the real part of
  `primePowerPart σ` tends to `+∞` as `σ → 1 / 2⁺`, so `‖L(σ, χ₄)‖ → ∞`, contradicting the
  continuity of the entire function `L(·, χ₄)` at `1 / 2`.

Neither argument uses the prime number theorem, nor Dirichlet's theorem on primes in
arithmetic progressions.

## Main statements

* `RokickiConstant.abs_re_primePart_sub_mul_tsum_le`: summation by parts for `primePart` under
  `S n = c · n + O(1)`.
* `RokickiConstant.exp_abelSeries_add_primePowerPart`: under bounded `S n`, the Euler product
  continues to `re s > 1 / 2`.
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

/-- If `exp (F σ) = L(σ, χ₄)` for real `σ` near `x` on the right, then
`Real.exp (re (F σ)) = ‖L(σ, χ₄)‖ → ‖L(x, χ₄)‖` as `σ → x⁺`, since `L(·, χ₄)` is entire. -/
theorem tendsto_exp_re_of_exp_eq_LFunction {F : ℝ → ℂ} {x : ℝ}
    (hF : ∀ᶠ σ : ℝ in 𝓝[>] x, exp (F σ) = DirichletCharacter.LFunction chi4 σ) :
    Tendsto (fun σ ↦ Real.exp (F σ).re) (𝓝[>] x) (𝓝 ‖DirichletCharacter.LFunction chi4 x‖) :=
  (tendsto_nhdsWithin_of_tendsto_nhds (((DirichletCharacter.differentiable_LFunction
    chi4_ne_one).continuous.comp continuous_ofReal).norm.tendsto x)).congr'
    (hF.mono fun σ hσ ↦ by simp [← hσ, Complex.norm_exp])

section Linear

/-- Summation by parts: if `∑_{k < n} χ₄ pₖ₊₂ = c · n + O(1)` then
`re (primePart σ) = c ∑ₖ pₖ₊₂ ^ (-σ) + O(1)` for real `σ > 1`. -/
theorem abs_re_primePart_sub_mul_tsum_le {c C : ℝ}
    (h : ∀ n, |(∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)) - c * n| ≤ C) {σ : ℝ} (hσ : 1 < σ) :
    |(primePart σ).re - c * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ)| ≤ 2 * C := by
  have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
  have hfs : Summable fun k ↦ (oddPrime k : ℝ) ^ (-σ) := summable_oddPrime_rpow (by linarith)
  have hterm : ∀ k, (chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-(σ : ℂ))).re =
      (ZMod.χ₄ (oddPrime k) : ℝ) * (oddPrime k : ℝ) ^ (-σ) := fun k ↦ by
    rw [chi4_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hs : HasSum (fun k ↦ ((ZMod.χ₄ (oddPrime k) : ℝ) - c) * (oddPrime k : ℝ) ^ (-σ))
      ((primePart σ).re - c * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ)) := by
    convert (hasSum_re (summable_primePart hσ').hasSum).sub (hfs.hasSum.mul_left c) using 1
    · exact funext fun k ↦ by rw [sub_mul, ← hterm k]; rfl
    · rfl
  have he : ∀ n, |∑ k ∈ range n, ((ZMod.χ₄ (oddPrime k) : ℝ) - c)| ≤ C := fun n ↦ by
    simpa [Finset.sum_sub_distrib, mul_comm] using h n
  have hC : 0 ≤ C := (abs_nonneg _).trans (h 0)
  have hf0 : (oddPrime 0 : ℝ) ^ (-σ) ≤ 1 := by
    rw [oddPrime_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  rw [← hs.tsum_eq]
  calc _ ≤ 2 * C * (oddPrime 0 : ℝ) ^ (-σ) :=
        abs_tsum_mul_le_of_abs_sum_le he (fun _ ↦ by positivity)
          (antitone_natCast_rpow_neg (oddPrime_pos 0) oddPrime_strictMono (by linarith)) hs.summable
    _ ≤ 2 * C := mul_le_of_le_one_right (by linarith) hf0

/-- The partial sums `∑_{k < n} χ₄ pₖ₊₂` are not of the form `c · n + O(1)` with `c ≠ 0`. -/
theorem not_exists_abs_sum_chi4_sub_mul_le :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n,
      |(∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)) - c * n| ≤ C := by
  rintro ⟨c, hc, C, h⟩
  obtain ⟨M, hM⟩ := exists_norm_primePowerPart_le
  -- `re (primePart σ + primePowerPart σ) = log ‖L(σ, χ₄)‖` converges as `σ → 1⁺` ...
  have hlim := (tendsto_exp_re_of_exp_eq_LFunction (F := fun σ ↦ primePart σ + primePowerPart σ)
    (eventually_nhdsWithin_of_forall fun σ (hσ : 1 < σ) ↦
      exp_primePart_add_primePowerPart (by simpa using hσ))).log
    (by simpa using DirichletCharacter.LFunction_apply_one_ne_zero chi4_ne_one)
  simp only [Real.log_exp] at hlim
  -- ... but its absolute value is at least `|c| ∑ₖ pₖ₊₂ ^ (-σ) - 2 C - M → ∞`.
  refine not_tendsto_atTop_of_tendsto_nhds hlim.abs (tendsto_atTop_mono' _ ?_
    (tendsto_atTop_add_const_right _ (-(2 * C + M))
      (tendsto_tsum_oddPrime_rpow_neg.const_mul_atTop (abs_pos.2 hc))))
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have h1 := abs_re_primePart_sub_mul_tsum_le h hσ
  have h2 := (abs_re_le_norm _).trans (hM σ (by simp [hσ.le]))
  rw [abs_le] at h1 h2
  rcases abs_cases c with ⟨hc', -⟩ | ⟨hc', -⟩ <;> rw [hc', add_re, le_abs] <;> [left; right] <;>
    linarith [h1.1, h1.2, h2.1, h2.2]

end Linear

section Bounded

variable {C : ℝ} (hC : ∀ n, |∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)| ≤ C)
include hC

/-- Under bounded partial sums of `χ₄` over the odd primes, the complex partial sums of `chi4`
over the odd primes are bounded by the same constant. -/
theorem norm_sum_chi4_le (n : ℕ) : ‖∑ j ∈ range n, chi4 (oddPrime j)‖ ≤ C := by
  have : ∑ j ∈ range n, chi4 (oddPrime j) =
      ((∑ j ∈ range n, (ZMod.χ₄ (oddPrime j) : ℝ) : ℝ) : ℂ) := by
    push_cast [chi4_natCast]
    rfl
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact hC n

/-- Under bounded partial sums, the Abel series of `χ₄` over the odd primes is holomorphic on
`0 < re s`. -/
theorem differentiableOn_abelSeries_chi4 :
    DifferentiableOn ℂ (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime) {s : ℂ | 0 < s.re} :=
  differentiableOn_abelSeries (norm_sum_chi4_le hC) (oddPrime_pos 0)
    oddPrime_strictMono

/-- **Analytic continuation of the Euler product.** Under bounded partial sums,
`L(s, χ₄) = exp (abelSeries s + primePowerPart s)` for all `1 / 2 < re s`. -/
theorem exp_abelSeries_add_primePowerPart {s : ℂ} (hs : 1 / 2 < s.re) :
    exp (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime s + primePowerPart s) =
      DirichletCharacter.LFunction chi4 s := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ
      (fun s ↦ exp (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime s + primePowerPart s))
      {s : ℂ | 1 / 2 < s.re} :=
    (((differentiableOn_abelSeries_chi4 hC).mono fun s (hs : 1 / 2 < s.re) ↦
      show 0 < s.re by linarith).add differentiableOn_primePowerPart).cexp.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi4) {s : ℂ | 1 / 2 < s.re} :=
    (DirichletCharacter.differentiable_LFunction chi4_ne_one).differentiableOn.analyticOnNhd hU
  have hfg : (fun s ↦ exp (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime s +
      primePowerPart s)) =ᶠ[𝓝 2] DirichletCharacter.LFunction chi4 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
    rw [abelSeries_eq_tsum (norm_sum_chi4_le hC) (oddPrime_pos 0) oddPrime_strictMono hs]
    exact exp_primePart_add_primePowerPart hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num) hfg hs

end Bounded

/-- The partial sums `∑_{k < n} χ₄ pₖ₊₂` are unbounded. -/
theorem not_exists_abs_sum_chi4_le :
    ¬ ∃ C : ℝ, ∀ n, |∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)| ≤ C := by
  rintro ⟨C, hC⟩
  set A := abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime
  -- `re (A σ)` is continuous at `σ = 1 / 2`, while `re (primePowerPart σ) → ∞` as `σ → 1 / 2⁺`
  have hA : ContinuousAt (fun σ : ℝ ↦ (A σ).re) (1 / 2) :=
    continuous_re.continuousAt.comp (((differentiableOn_abelSeries_chi4 hC).continuousOn
      |>.continuousAt ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 0 < ((1 / 2 : ℝ) : ℂ).re by norm_num))).comp continuous_ofReal.continuousAt)
  exact not_tendsto_atTop_of_tendsto_nhds (tendsto_exp_re_of_exp_eq_LFunction
    (F := fun σ ↦ A σ + primePowerPart σ) (eventually_nhdsWithin_of_forall
      fun σ (hσ : 1 / 2 < σ) ↦ exp_abelSeries_add_primePowerPart hC (by simpa using hσ)))
    (Real.tendsto_exp_atTop.comp
      ((hA.tendsto.mono_left nhdsWithin_le_nhds).add_atTop tendsto_re_primePowerPart))

end RokickiConstant
