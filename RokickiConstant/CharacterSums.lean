/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.Analytic.Uniqueness
import RokickiConstant.LSeriesChi4

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
  `primePart σ = c ∑_p p^{-σ} + O(1)` for real `σ > 1`, which tends to `±∞` as `σ → 1⁺`
  because `∑_p 1 / p` diverges, while `primePowerPart` stays bounded. So `L(σ, χ₄) → 0` or
  `∞`, contradicting `L(1, χ₄) ≠ 0` and the continuity of `L(·, χ₄)` at `1`.
* If `S n` is bounded, summation by parts (`abelSeries`) continues `primePart` holomorphically to
  `re s > 0`, and `primePowerPart` is holomorphic on `re s > 1 / 2`; by the identity theorem
  `L(s, χ₄) = exp (abelSeries s + primePowerPart s)` on `re s > 1 / 2`. But the real part of
  `primePowerPart σ` tends to `+∞` as `σ → 1 / 2⁺`, so `|L(σ, χ₄)| → ∞`, contradicting the
  continuity of the entire function `L(·, χ₄)` at `1 / 2`.

Neither argument uses the prime number theorem, nor Dirichlet's theorem on primes in
arithmetic progressions.

## Main statements

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

section Linear

/-- Summation by parts: if `∑_{k < n} χ₄ pₖ₊₂ = c · n + O(1)` then
`re (primePart σ) = c ∑ₖ pₖ₊₂ ^ (-σ) + O(1)` for real `σ > 1`. -/
theorem abs_re_primePart_sub_mul_tsum_le {c C : ℝ}
    (h : ∀ n, |(∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)) - c * n| ≤ C) {σ : ℝ} (hσ : 1 < σ) :
    |(primePart σ).re - c * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ)| ≤ 2 * C := by
  have hq₀ : 0 < oddPrime 0 := by rw [oddPrime_zero]; norm_num
  have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
  have hfs : Summable fun k ↦ (oddPrime k : ℝ) ^ (-σ) := summable_oddPrime_rpow (by linarith)
  have hterm : ∀ k, (chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-(σ : ℂ))).re =
      (ZMod.χ₄ (oddPrime k) : ℝ) * (oddPrime k : ℝ) ^ (-σ) := fun k ↦ by
    rw [chi4_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hχs : Summable fun k ↦ (ZMod.χ₄ (oddPrime k) : ℝ) * (oddPrime k : ℝ) ^ (-σ) :=
    (Complex.reCLM.summable (summable_primePart hσ')).congr fun k ↦ hterm k
  have hre : (primePart σ).re = ∑' k, (ZMod.χ₄ (oddPrime k) : ℝ) * (oddPrime k : ℝ) ^ (-σ) := by
    rw [primePart, Complex.re_tsum (summable_primePart hσ')]
    exact tsum_congr hterm
  have key : (primePart σ).re - c * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ) =
      ∑' k, ((ZMod.χ₄ (oddPrime k) : ℝ) - c) * (oddPrime k : ℝ) ^ (-σ) := by
    rw [hre, ← tsum_mul_left, ← hχs.tsum_sub (hfs.mul_left c)]
    exact tsum_congr fun k ↦ by ring
  have hes : Summable fun k ↦ ((ZMod.χ₄ (oddPrime k) : ℝ) - c) * (oddPrime k : ℝ) ^ (-σ) :=
    (hχs.sub (hfs.mul_left c)).congr fun k ↦ by ring
  have he : ∀ n, |∑ k ∈ range n, ((ZMod.χ₄ (oddPrime k) : ℝ) - c)| ≤ C := fun n ↦ by
    simpa [Finset.sum_sub_distrib, mul_comm] using h n
  have hC : 0 ≤ C := (abs_nonneg _).trans (h 0)
  have hf0 : (oddPrime 0 : ℝ) ^ (-σ) ≤ 1 := by
    rw [oddPrime_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  rw [key]
  calc _ ≤ 2 * C * (oddPrime 0 : ℝ) ^ (-σ) :=
        abs_tsum_mul_le_of_abs_sum_le he (fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (antitone_natCast_rpow_neg hq₀ oddPrime_strictMono (by linarith)) hes
    _ ≤ 2 * C := mul_le_of_le_one_right (by linarith) hf0

theorem tendsto_norm_LFunction_chi4_one :
    Tendsto (fun σ : ℝ ↦ ‖DirichletCharacter.LFunction chi4 σ‖) (𝓝[>] (1 : ℝ))
      (𝓝 ‖DirichletCharacter.LFunction chi4 1‖) := by
  have h := ((DirichletCharacter.differentiable_LFunction chi4_ne_one).continuous.comp
    Complex.continuous_ofReal).norm.tendsto 1
  simp only [Function.comp_def, Complex.ofReal_one] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

theorem LFunction_chi4_one_ne_zero : DirichletCharacter.LFunction chi4 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero chi4_ne_one

/-- The partial sums `∑_{k < n} χ₄ pₖ₊₂` are not of the form `c · n + O(1)` with `c ≠ 0`. -/
theorem not_exists_abs_sum_chi4_sub_mul_le :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n,
      |(∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)) - c * n| ≤ C := by
  rintro ⟨c, hc, C, h⟩
  obtain ⟨M, hM⟩ := exists_norm_primePowerPart_le
  have hnorm : ∀ σ : ℝ, 1 < σ → ‖DirichletCharacter.LFunction chi4 σ‖ =
      Real.exp ((primePart σ).re + (primePowerPart σ).re) := fun σ hσ ↦ by
    rw [← exp_primePart_add_primePowerPart (by simpa using hσ), Complex.norm_exp, Complex.add_re]
  have hP : ∀ σ : ℝ, 1 < σ → |(primePowerPart σ).re| ≤ M := fun σ hσ ↦
    (Complex.abs_re_le_norm _).trans (hM _ (by simp; linarith))
  have hev : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 1 < σ := self_mem_nhdsWithin
  rcases hc.lt_or_gt with hc | hc
  · have hlim : Tendsto
        (fun σ : ℝ ↦ Real.exp (c * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ) + (2 * C + M)))
        (𝓝[>] (1 : ℝ)) (𝓝 0) :=
      Real.tendsto_exp_atBot.comp <| tendsto_atBot_add_const_right _ _ <|
        tendsto_tsum_oddPrime_rpow_neg.const_mul_atTop_of_neg hc
    have h0 : Tendsto (fun σ : ℝ ↦ ‖DirichletCharacter.LFunction chi4 σ‖) (𝓝[>] 1) (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) (hev.mono fun σ hσ ↦ by
        rw [hnorm σ hσ]
        exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hP σ hσ)).2,
          (abs_le.1 (abs_re_primePart_sub_mul_tsum_le h hσ)).2])) hlim
    exact LFunction_chi4_one_ne_zero
      (norm_eq_zero.1 (tendsto_nhds_unique tendsto_norm_LFunction_chi4_one h0))
  · have hlim : Tendsto
        (fun σ : ℝ ↦ Real.exp (c * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ) + -(2 * C + M)))
        (𝓝[>] (1 : ℝ)) atTop :=
      Real.tendsto_exp_atTop.comp <| tendsto_atTop_add_const_right _ _ <|
        tendsto_tsum_oddPrime_rpow_neg.const_mul_atTop hc
    refine not_tendsto_atTop_of_tendsto_nhds tendsto_norm_LFunction_chi4_one
      (tendsto_atTop_mono' _ (hev.mono fun σ hσ ↦ ?_) hlim)
    dsimp only
    rw [hnorm σ hσ]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hP σ hσ)).1,
      (abs_le.1 (abs_re_primePart_sub_mul_tsum_le h hσ)).1])

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

/-- Under bounded partial sums, the Abel series of `χ₄` over the odd primes agrees with
`primePart` for `1 < re s`. -/
theorem abelSeries_eq_primePart {s : ℂ} (hs : 1 < s.re) :
    abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime s = primePart s := by
  rw [primePart]
  exact abelSeries_eq_tsum (norm_sum_chi4_le hC) (by rw [oddPrime_zero]; norm_num)
    oddPrime_strictMono hs

theorem differentiableOn_abelSeries_chi4 :
    DifferentiableOn ℂ (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime) {s : ℂ | 0 < s.re} :=
  differentiableOn_abelSeries (norm_sum_chi4_le hC) (by rw [oddPrime_zero]; norm_num)
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
    rw [abelSeries_eq_primePart hC hs, exp_primePart_add_primePowerPart hs]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num) hfg hs

theorem tendsto_re_abelSeries_chi4 :
    Tendsto (fun σ : ℝ ↦ (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime σ).re)
      (𝓝[>] (1 / 2 : ℝ))
      (𝓝 (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime (1 / 2 : ℝ)).re) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcont : ContinuousAt (abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime)
      ((1 / 2 : ℝ) : ℂ) :=
    (differentiableOn_abelSeries_chi4 hC).continuousOn.continuousAt
      (hU.mem_nhds (show 0 < ((1 / 2 : ℝ) : ℂ).re by norm_num))
  exact tendsto_nhdsWithin_of_tendsto_nhds (Complex.continuous_re.continuousAt.tendsto.comp
    (hcont.tendsto.comp (Complex.continuous_ofReal.tendsto _)))

omit hC in
theorem tendsto_norm_LFunction_chi4_one_half :
    Tendsto (fun σ : ℝ ↦ ‖DirichletCharacter.LFunction chi4 σ‖) (𝓝[>] (1 / 2 : ℝ))
      (𝓝 ‖DirichletCharacter.LFunction chi4 (1 / 2 : ℝ)‖) :=
  tendsto_nhdsWithin_of_tendsto_nhds
    (((DirichletCharacter.differentiable_LFunction chi4_ne_one).continuous.comp
      Complex.continuous_ofReal).norm.tendsto (1 / 2 : ℝ))

end Bounded

/-- The partial sums `∑_{k < n} χ₄ pₖ₊₂` are unbounded. -/
theorem not_exists_abs_sum_chi4_le :
    ¬ ∃ C : ℝ, ∀ n, |∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)| ≤ C := by
  rintro ⟨C, hC⟩
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ), Real.exp
      ((abelSeries (fun k ↦ chi4 (oddPrime k)) oddPrime σ).re + (primePowerPart σ).re) =
        ‖DirichletCharacter.LFunction chi4 σ‖ :=
    eventually_nhdsWithin_of_forall fun σ (hσ : 1 / 2 < σ) ↦ by
      rw [← exp_abelSeries_add_primePowerPart hC (by simpa using hσ), Complex.norm_exp,
        Complex.add_re]
  exact not_tendsto_atTop_of_tendsto_nhds tendsto_norm_LFunction_chi4_one_half
    ((Real.tendsto_exp_atTop.comp
      ((tendsto_re_abelSeries_chi4 hC).add_atTop tendsto_re_primePowerPart)).congr' hev)

end RokickiConstant
