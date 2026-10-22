/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Probability.Moments.ComplexMGF
import RokickiConstant.General.Oscillation

/-!
# Landau's theorem and the one-sided bias of quadratic characters

**Landau's theorem** (the analogue for Laplace transforms of Pringsheim's theorem on power series
with nonnegative coefficients): if `μ` is a measure on `[0, ∞)` and its Laplace transform
`F(s) = ∫ exp (-s u) dμ(u)` converges absolutely for real `s > σ₀`, then `F` cannot be continued
analytically to a neighbourhood of the real point `σ₀` unless the integral converges somewhat to
the left of `σ₀`. The proof expands `F` in its Taylor series at a real point `s₁ > σ₀`: the
coefficients `(-1) ^ n ∫ u ^ n exp (-s₁ u) dμ(u) / n!` (Mathlib's `iteratedDeriv_complexMGF`)
alternate in sign, so at a real `σ = s₁ - t < s₁` every term of the Taylor series is nonnegative,
and Tonelli's theorem sums the resulting double integral in the other order,
`∑ₙ ∫ (t u) ^ n / n! · exp (-s₁ u) dμ = ∫ exp (-σ u) dμ`. The Cauchy-Taylor expansion of the
continuation on the largest disc of holomorphy (`Complex.hasSum_taylorSeries_on_ball`) gives the
convergence of the left side. Dirichlet series `∑ₖ cₖ λₖ ^ (-s)` with `cₖ ≥ 0` are the case
`μ = ∑ₖ cₖ δ_{log λₖ}`; Mellin transforms `∫ h(x) x ^ (-s - 1) dx` of nonnegative step functions
`h` are the case `μ = ∑ₖ Hₖ 1_{(log qₖ, log qₖ₊₁]}(u) du`.

**The one-sided bias theorem.** For a nonprincipal quadratic character `χ` and `A > 1`, the sums
`∑_{p < x} χ(p)` go below `-C √x / (log x) ^ A` for arbitrarily large `x`, for every `C`:
`∑_{p < x} χ(p) = Ω₋(√x / (log x) ^ A)`, the direction of Chebyshev's bias. If
`S*(x) ≥ -C g(x)` with `g(x) = √x / (log x) ^ A`, then `h = S* + C g ≥ 0` and Landau's theorem
applies to the Mellin transform of `h`, which on the real axis equals
`(log ‖L(σ, χ)‖ - re (primePowerPart χ σ) + Γ(σ)) / σ` to the right of its abscissa of convergence
`σ_c`, with `Γ` (the transform of `C g`) continuous on `[1 / 2, 2]` because `A > 1`
(`continuousOn_abelSeries_of_le_rpow_div_log_rpow`). At `σ_c` there are three cases:
`σ_c = 1 / 2`, where the prime-power part (the prime squares) tends to `+∞`; a real zero
`L(σ_c, χ) = 0`, where `log ‖L‖ → -∞`; or `σ_c > 1 / 2` with `L(σ_c, χ) ≠ 0`, where a local
logarithm of `L` continues the transform across `σ_c`, contradicting Landau's theorem. In the
first two cases the transform of `h ≥ 0` tends to `-∞`, a contradiction. No information on the
zeros of `L(s, χ)` is needed: real zeros only help, and nonreal zeros play no role. For the same
reason the method gives nothing in the direction `Ω₊`, where `C g - S* ≥ 0` has transform tending
to `+∞`, which is consistent: `Ω₊` needs a nonreal zero of `L(s, χ)` (see `research/landau.md`).

## Main statements

* `integrable_exp_neg_mul_of_differentiableOn_ball`: Landau's theorem, Pringsheim form (the
  Laplace transform converges on the real part of every disc of holomorphy about a real point of
  convergence).
* `exists_lt_integrable_exp_neg_mul`: Landau's theorem, abscissa form (holomorphy near the real
  point `σ₀` gives convergence at some `σ < σ₀`).
* `exists_lt_summable_mul_rpow_neg`: the same for general Dirichlet series `∑ₖ cₖ λₖ ^ (-s)` with
  `cₖ ≥ 0`, `λₖ ≥ 1`.
* `DirichletCharacter.IsQuadratic.not_exists_le_re_sum_succ_nthPrime_rpow_div_log_rpow`: the core
  one-sided theorem, `A > 1`, `∑_{j ≤ k} χ(pⱼ) ≥ -C pₖ ^ (1 / 2) / (log pₖ) ^ A` fails.
* `DirichletCharacter.IsQuadratic.frequently_re_sum_primesBelow_lt_rpow_div_log_rpow`,
  `DirichletCharacter.IsQuadratic.not_exists_le_sum_primesBelow_rpow_div_log_rpow`: the `x`-scale
  `Ω₋` theorem, `A > 1`.
* `DirichletCharacter.IsQuadratic.frequently_re_sum_lt_rpow_div_log_rpow`,
  `DirichletCharacter.IsQuadratic.not_exists_le_re_sum_rpow_div_log_rpow`: the index scale,
  `A > 1 / 2`.
* `RokickiConstant.frequently_card_rokickiDigit_one_sub_card_zero_gt`,
  `RokickiConstant.not_exists_card_rokickiDigit_one_sub_card_zero_le`: among the first `n` binary
  digits of `ρ`, the ones outnumber the zeros by more than `C √n / (log n) ^ A` infinitely often
  (`A > 1 / 2`, every `C`).

## References

* E. Landau, *Über einen Satz von Tschebyschef*, Math. Ann. 61 (1905).
* A. E. Ingham, *The distribution of prime numbers*, Chapter V.
* H. L. Montgomery, R. C. Vaughan, *Multiplicative number theory I*, Theorem 1.7 and Chapter 15.

## Tags

Landau's theorem, Pringsheim's theorem, Laplace transform, Chebyshev bias, Omega theorem
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex MeasureTheory ProbabilityTheory
open scoped Nat

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

section Landau

variable {μ : Measure ℝ}

/-- For a measure carried by `[0, ∞)`, integrability of `u ↦ exp (-σ u)` passes from `σ` to every
`τ ≥ σ`. -/
theorem integrable_exp_neg_mul_of_le (hμ : ∀ᵐ u ∂μ, 0 ≤ u) {σ τ : ℝ} (hστ : σ ≤ τ)
    (hσ : Integrable (fun u ↦ Real.exp (-(σ * u))) μ) :
    Integrable (fun u ↦ Real.exp (-(τ * u))) μ := by
  refine hσ.mono' (by fun_prop) ?_
  filter_upwards [hμ] with u hu
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.2 (by nlinarith)

/-- Membership in the interval of integrability of the moment-generating function of `u ↦ -u`. -/
theorem mem_integrableExpSet_neg_iff {σ : ℝ} :
    σ ∈ integrableExpSet (fun u : ℝ ↦ -u) μ ↔ Integrable (fun u ↦ Real.exp (-(σ * u))) μ := by
  simp [integrableExpSet, mul_neg]

/-- If `u ↦ exp (-(σ - δ) u)` is integrable for some `δ > 0`, then `σ` is an interior point of the
interval of integrability. -/
theorem mem_interior_integrableExpSet_neg (hμ : ∀ᵐ u ∂μ, 0 ≤ u) {σ δ : ℝ} (hδ : 0 < δ)
    (h : Integrable (fun u ↦ Real.exp (-((σ - δ) * u))) μ) :
    σ ∈ interior (integrableExpSet (fun u : ℝ ↦ -u) μ) := by
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (Ioi_mem_nhds (show σ - δ < σ by linarith)) fun τ hτ ↦ ?_
  exact mem_integrableExpSet_neg_iff.2 (integrable_exp_neg_mul_of_le hμ (le_of_lt hτ) h)

/-- **Landau's theorem**, Pringsheim form. Let `μ` be a measure carried by `[0, ∞)` whose Laplace
transform `F(s) = ∫ exp (-s u) dμ(u)` converges absolutely at `s₁ - δ` for some `δ > 0`. If `F`
coincides near `s₁` with a function `Ψ` holomorphic on the disc of radius `r` about `s₁`, then the
Laplace transform converges absolutely at every real `σ > s₁ - r`. The Taylor coefficients of `F`
at `s₁` have alternating signs, so at a real point `σ = s₁ - t < s₁` all terms of the Taylor series
are nonnegative and the double series can be summed in the other order. -/
theorem integrable_exp_neg_mul_of_differentiableOn_ball (hμ : ∀ᵐ u ∂μ, 0 ≤ u) {s₁ δ r : ℝ}
    (hδ : 0 < δ) (hint : Integrable (fun u ↦ Real.exp (-((s₁ - δ) * u))) μ) {Ψ : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball (s₁ : ℂ) r))
    (hΨF : Ψ =ᶠ[𝓝 (s₁ : ℂ)] complexMGF (fun u ↦ -u) μ) {σ : ℝ} (hσ : s₁ - r < σ) :
    Integrable (fun u ↦ Real.exp (-(σ * u))) μ := by
  rcases le_or_gt s₁ σ with h | h
  · exact integrable_exp_neg_mul_of_le hμ (by linarith) hint
  obtain ⟨t, rfl⟩ : ∃ t, σ = s₁ - t := ⟨s₁ - σ, by ring⟩
  have ht : 0 < t := by linarith
  have hs₁ : (s₁ : ℂ).re ∈ interior (integrableExpSet (fun u : ℝ ↦ -u) μ) := by
    simpa using mem_interior_integrableExpSet_neg hμ hδ hint
  -- the terms of the Taylor series at `s₁ - t`
  set f : ℕ → ℝ → ℝ := fun n u ↦ (t * u) ^ n / n ! * Real.exp (-(s₁ * u)) with hf
  have hfint : ∀ n, Integrable (f n) μ := fun n ↦ by
    refine ((integrable_pow_mul_exp_of_mem_interior_integrableExpSet hs₁ n).const_mul
      ((-t) ^ n / n !)).congr (ae_of_all _ fun u ↦ ?_)
    simp only [hf, Complex.ofReal_re]
    rw [show (t * u) ^ n = (-t) ^ n * (-u) ^ n by rw [← mul_pow, neg_mul_neg],
      show -(s₁ * u) = s₁ * -u by ring]
    ring
  have hf0 : ∀ n, 0 ≤ᵐ[μ] f n := fun n ↦ by
    filter_upwards [hμ] with u hu
    exact mul_nonneg (div_nonneg (pow_nonneg (mul_nonneg ht.le hu) n) (Nat.cast_nonneg _))
      (Real.exp_pos _).le
  set a : ℕ → ℝ := fun n ↦ ∫ u, f n u ∂μ with ha
  have hterm : ∀ n, (n ! : ℂ)⁻¹ • (((s₁ - t : ℝ) : ℂ) - s₁) ^ n • iteratedDeriv n Ψ s₁ =
      (a n : ℂ) := fun n ↦ by
    change _ = ((∫ u, f n u ∂μ : ℝ) : ℂ)
    rw [hΨF.iteratedDeriv_eq, iteratedDeriv_complexMGF hs₁, ← integral_complex_ofReal, smul_eq_mul,
      smul_eq_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
    simp only [hf]
    push_cast
    rw [show ((s₁ : ℂ) - t - s₁) = -t by ring, mul_neg, ← mul_assoc ((-(t : ℂ)) ^ n), ← mul_pow,
      neg_mul_neg]
    field_simp
  have hsum : HasSum (fun n ↦ (a n : ℂ)) (Ψ ((s₁ - t : ℝ) : ℂ)) := by
    refine (Complex.hasSum_taylorSeries_on_ball hΨ ?_).congr_fun fun n ↦ (hterm n).symm
    rw [Metric.mem_ball, Complex.dist_eq]
    push_cast
    rw [show (s₁ : ℂ) - t - s₁ = -t by ring, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    linarith
  have hsa : Summable a := Complex.summable_ofReal.1 hsum.summable
  -- Tonelli: `∫ exp (-(s₁ - t) u) = ∑ₙ ∫ (t u) ^ n / n! exp (-s₁ u) < ∞`
  have hpt : ∀ᵐ u ∂μ, ENNReal.ofReal (Real.exp (-((s₁ - t) * u))) =
      ∑' n, ENNReal.ofReal (f n u) := by
    filter_upwards [hμ] with u hu
    have h1 : HasSum (fun n ↦ f n u) (Real.exp (-((s₁ - t) * u))) := by
      have := (NormedSpace.expSeries_div_hasSum_exp (t * u)).mul_right (Real.exp (-(s₁ * u)))
      rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add] at this
      convert this using 2
      ring
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ mul_nonneg (div_nonneg
      (pow_nonneg (mul_nonneg ht.le hu) n) (Nat.cast_nonneg _)) (Real.exp_pos _).le) h1.summable,
      h1.tsum_eq]
  have hlin : ∫⁻ u, ENNReal.ofReal (Real.exp (-((s₁ - t) * u))) ∂μ < ⊤ := by
    rw [lintegral_congr_ae hpt, lintegral_tsum fun n ↦ (by fun_prop : Measurable (f n)).aemeasurable
      |>.ennreal_ofReal]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hfint _) (hf0 _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ integral_nonneg_of_ae (hf0 n)) hsa]
    exact ENNReal.ofReal_lt_top
  exact ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun u ↦ (Real.exp_pos _).le)).2 hlin⟩

/-- The Laplace transform `s ↦ ∫ exp (-s u) dμ(u)` is holomorphic on the half-plane of absolute
convergence. -/
theorem differentiableOn_complexMGF_neg (hμ : ∀ᵐ u ∂μ, 0 ≤ u) {σ₀ : ℝ}
    (hint : ∀ σ, σ₀ < σ → Integrable (fun u ↦ Real.exp (-(σ * u))) μ) :
    DifferentiableOn ℂ (complexMGF (fun u ↦ -u) μ) {s : ℂ | σ₀ < s.re} :=
  differentiableOn_complexMGF.mono fun s (hs : σ₀ < s.re) ↦
    mem_interior_integrableExpSet_neg hμ (δ := (s.re - σ₀) / 2) (by linarith)
      (hint _ (by linarith))

/-- A point of the disc of radius `1 + ε ^ 2 / 3` about `σ₀ + 1` (with `0 < ε ≤ 1`) that is not in
the half-plane `re s > σ₀` lies in the disc of radius `ε` about `σ₀`. -/
theorem mem_ball_of_mem_ball_of_re_le {σ₀ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {s : ℂ}
    (hs : s ∈ Metric.ball ((σ₀ + 1 : ℝ) : ℂ) (1 + ε ^ 2 / 3)) (hre : s.re ≤ σ₀) :
    s ∈ Metric.ball (σ₀ : ℂ) ε := by
  rw [Metric.mem_ball, Complex.dist_eq] at hs ⊢
  have h1 : ‖s - ((σ₀ + 1 : ℝ) : ℂ)‖ ^ 2 = (s.re - σ₀ - 1) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
    ring
  have h2 : ‖s - (σ₀ : ℂ)‖ ^ 2 = (s.re - σ₀) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
    ring
  have h3 : ‖s - ((σ₀ + 1 : ℝ) : ℂ)‖ ^ 2 < (1 + ε ^ 2 / 3) ^ 2 :=
    pow_lt_pow_left₀ hs (norm_nonneg _) two_ne_zero
  have h4 : ‖s - (σ₀ : ℂ)‖ ^ 2 < ε ^ 2 := by
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h4

/-- **Landau's theorem**, abscissa form. Let `μ` be a measure carried by `[0, ∞)` whose Laplace
transform `F(s) = ∫ exp (-s u) dμ(u)` converges absolutely for every real `σ > σ₀`. If `F` extends
holomorphically to a neighbourhood of the real point `σ₀`, that is, if some `G` holomorphic on a
disc about `σ₀` agrees with `F` on the part of the disc where `re s > σ₀`, then the Laplace
transform converges absolutely at some real `σ < σ₀`. In other words, the abscissa of convergence
of the Laplace transform of a positive measure is a singularity. -/
theorem exists_lt_integrable_exp_neg_mul (hμ : ∀ᵐ u ∂μ, 0 ≤ u) {σ₀ : ℝ}
    (hint : ∀ σ, σ₀ < σ → Integrable (fun u ↦ Real.exp (-(σ * u))) μ) {G : ℂ → ℂ} {ε : ℝ}
    (hε : 0 < ε) (hG : DifferentiableOn ℂ G (Metric.ball (σ₀ : ℂ) ε))
    (hGF : ∀ s ∈ Metric.ball (σ₀ : ℂ) ε, σ₀ < s.re → G s = complexMGF (fun u ↦ -u) μ s) :
    ∃ σ < σ₀, Integrable (fun u ↦ Real.exp (-(σ * u))) μ := by
  wlog hε1 : ε ≤ 1 generalizing ε
  · exact this one_pos (hG.mono (Metric.ball_subset_ball (by linarith)))
      (fun s hs ↦ hGF s (Metric.ball_subset_ball (by linarith) hs)) le_rfl
  set F := complexMGF (fun u : ℝ ↦ -u) μ
  have hF := differentiableOn_complexMGF_neg hμ hint
  set Ψ : ℂ → ℂ := fun s ↦ if σ₀ < s.re then F s else G s with hΨ
  have hU : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const continuous_re
  have hΨG : ∀ s ∈ Metric.ball (σ₀ : ℂ) ε, Ψ s = G s := fun s hs ↦ by
    simp only [hΨ]
    split_ifs with h
    exacts [(hGF s hs h).symm, rfl]
  have hΨF : ∀ s : ℂ, σ₀ < s.re → Ψ =ᶠ[𝓝 s] F := fun s hs ↦ by
    filter_upwards [hU.mem_nhds hs] with z (hz : σ₀ < z.re)
    simp [hΨ, hz]
  have hΨd : DifferentiableOn ℂ Ψ (Metric.ball ((σ₀ + 1 : ℝ) : ℂ) (1 + ε ^ 2 / 3)) := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hre : σ₀ < s.re
    · exact ((hF s hre).differentiableAt (hU.mem_nhds hre)).congr_of_eventuallyEq (hΨF s hre)
    · have hsb := mem_ball_of_mem_ball_of_re_le hε hε1 hs (not_lt.1 hre)
      exact ((hG s hsb).differentiableAt (Metric.isOpen_ball.mem_nhds hsb)).congr_of_eventuallyEq
        (eventually_of_mem (Metric.isOpen_ball.mem_nhds hsb) hΨG)
  have hε2 : 0 < ε ^ 2 := by positivity
  exact ⟨σ₀ - ε ^ 2 / 6, by linarith, integrable_exp_neg_mul_of_differentiableOn_ball hμ
    (s₁ := σ₀ + 1) (δ := 1 / 2) (by norm_num) (hint _ (by linarith)) hΨd
    (hΨF _ (by simp)) (by linarith)⟩

end Landau

section StepMeasure

/-! ## Mellin transforms of step functions as Laplace transforms -/

/-- For `a ≤ b` and `σ ≠ 0`, `∫_{(a, b]} exp (-σ u) du = (exp (-σ a) - exp (-σ b)) / σ`. -/
theorem integral_Ioc_exp_neg_mul {a b σ : ℝ} (hab : a ≤ b) (hσ : σ ≠ 0) :
    ∫ u in Set.Ioc a b, Real.exp (-(σ * u)) = (Real.exp (-(σ * a)) - Real.exp (-(σ * b))) / σ := by
  have hd : ∀ u, HasDerivAt (fun u ↦ -(Real.exp (-(σ * u)) / σ)) (Real.exp (-(σ * u))) u := by
    intro u
    have h : HasDerivAt (fun u ↦ -(σ * u)) (-σ) u := by
      simpa [neg_mul] using (hasDerivAt_id u).const_mul (-σ)
    convert h.exp.div_const σ |>.neg using 1
    field_simp
  rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hd u)
    ((by fun_prop : Continuous fun u ↦ Real.exp (-(σ * u))).intervalIntegrable _ _)]
  ring

/-- For `a ≤ b` and `s ≠ 0`, `∫_{(a, b]} exp (-s u) du = (exp (-s a) - exp (-s b)) / s`. -/
theorem integral_Ioc_cexp_mul_neg {a b : ℝ} (hab : a ≤ b) {s : ℂ} (hs : s ≠ 0) :
    ∫ u in Set.Ioc a b, cexp (s * ((-u : ℝ) : ℂ)) = (cexp (-s * a) - cexp (-s * b)) / s := by
  rw [← intervalIntegral.integral_of_le hab]
  simp_rw [ofReal_neg, mul_neg, ← neg_mul]
  rw [integral_exp_mul_complex (neg_ne_zero.2 hs)]
  field_simp
  ring

/-- The measure `∑ₖ Hₖ · 1_{(log qₖ, log qₖ₊₁]}(u) du` on `ℝ`. Under `u = log x` it is the measure
`h(x) dx / x` for the step function `h` equal to `Hₖ` on `[qₖ, qₖ₊₁)`, so its Laplace transform
`∫ exp (-s u) dμ(u) = ∫ h(x) x ^ (-s - 1) dx` is the Mellin transform of `h`. -/
noncomputable def stepMeasure (H : ℕ → ℝ) (q : ℕ → ℕ) : Measure ℝ :=
  Measure.sum fun k ↦ ENNReal.ofReal (H k) •
    volume.restrict (Set.Ioc (Real.log (q k)) (Real.log (q (k + 1))))

variable {H : ℕ → ℝ} {q : ℕ → ℕ}

/-- `stepMeasure H q` is carried by `[0, ∞)`. -/
theorem ae_nonneg_stepMeasure (hq₀ : 0 < q 0) (hq : StrictMono q) :
    ∀ᵐ u ∂stepMeasure H q, 0 ≤ u := by
  rw [stepMeasure, Measure.ae_sum_iff]
  intro k
  refine Measure.ae_smul_measure (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu ↦ ?_) _
  exact (Real.log_nonneg (Nat.one_le_cast.2 (hq₀.trans_le (hq.monotone k.zero_le)))).trans
    hu.1.le

/-- `∫ exp (-σ u) d(stepMeasure H q)(u) = ∑ₖ Hₖ (qₖ ^ (-σ) - qₖ₊₁ ^ (-σ)) / σ` for `σ > 0`. -/
theorem lintegral_stepMeasure (hH : ∀ k, 0 ≤ H k) (hq₀ : 0 < q 0) (hq : StrictMono q) {σ : ℝ}
    (hσ : 0 < σ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(σ * u))) ∂stepMeasure H q =
      ∑' k, ENNReal.ofReal (H k * ((q k : ℝ) ^ (-σ) - (q (k + 1) : ℝ) ^ (-σ)) / σ) := by
  rw [stepMeasure, lintegral_sum_measure]
  refine tsum_congr fun k ↦ ?_
  have hpos : ∀ k, (0 : ℝ) < q k := fun k ↦ by
    exact_mod_cast hq₀.trans_le (hq.monotone k.zero_le)
  have hle : Real.log (q k) ≤ Real.log (q (k + 1)) :=
    Real.log_le_log (hpos k) (by exact_mod_cast hq.monotone k.le_succ)
  rw [lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous fun u ↦ Real.exp (-(σ * u))).integrableOn_Ioc)
    (ae_of_all _ fun u ↦ (Real.exp_pos _).le), integral_Ioc_exp_neg_mul hle hσ.ne', smul_eq_mul,
    ← ENNReal.ofReal_mul (hH k), Real.rpow_def_of_pos (hpos k),
    Real.rpow_def_of_pos (hpos (k + 1))]
  congr 1
  ring_nf

/-- If `∑ₖ Hₖ (qₖ ^ (-σ) - qₖ₊₁ ^ (-σ))` converges, `σ > 0`, then `u ↦ exp (-σ u)` is integrable
for `stepMeasure H q`. -/
theorem integrable_stepMeasure (hH : ∀ k, 0 ≤ H k) (hq₀ : 0 < q 0) (hq : StrictMono q) {σ : ℝ}
    (hσ : 0 < σ) (hs : Summable fun k ↦ H k * ((q k : ℝ) ^ (-σ) - (q (k + 1) : ℝ) ^ (-σ))) :
    Integrable (fun u ↦ Real.exp (-(σ * u))) (stepMeasure H q) := by
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun u ↦ (Real.exp_pos _).le)).2 ?_⟩
  rw [lintegral_stepMeasure hH hq₀ hq hσ, ← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ div_nonneg
    (mul_nonneg (hH k) (sub_nonneg.2 (antitone_natCast_rpow_neg hq₀ hq hσ.le k.le_succ))) hσ.le)
    (hs.div_const σ)]
  exact ENNReal.ofReal_lt_top

/-- The Laplace transform of `stepMeasure H q` is `(1 / s) ∑ₖ Hₖ (qₖ ^ (-s) - qₖ₊₁ ^ (-s))`, the
Mellin transform of the step function, wherever the series converges absolutely. -/
theorem mul_complexMGF_stepMeasure (hH : ∀ k, 0 ≤ H k) (hq₀ : 0 < q 0) (hq : StrictMono q)
    {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable fun k ↦ H k * ((q k : ℝ) ^ (-s.re) - (q (k + 1) : ℝ) ^ (-s.re))) :
    s * complexMGF (fun u ↦ -u) (stepMeasure H q) s =
      ∑' k, (H k : ℂ) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s)) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hint : Integrable (fun u : ℝ ↦ cexp (s * ((-u : ℝ) : ℂ))) (stepMeasure H q) :=
    integrable_cexp_mul_of_re_mem_integrableExpSet measurable_neg.aemeasurable
      (mem_integrableExpSet_neg_iff.2 (integrable_stepMeasure hH hq₀ hq hs hsum))
  rw [complexMGF, stepMeasure, integral_sum_measure hint, ← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  have hpos : ∀ k, 0 < q k := fun k ↦ hq₀.trans_le (hq.monotone k.zero_le)
  have hle : Real.log (q k) ≤ Real.log (q (k + 1)) :=
    Real.log_le_log (by exact_mod_cast hpos k) (by exact_mod_cast hq.monotone k.le_succ)
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hH k), integral_Ioc_cexp_mul_neg hle hs0,
    Complex.real_smul, natCast_log, natCast_log,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (hpos k).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (hpos (k + 1)).ne')]
  field_simp

end StepMeasure

section DiracMeasure

/-! ## Landau's theorem for general Dirichlet series with nonnegative coefficients -/

/-- The measure `∑ₖ cₖ δ_{log λₖ}` on `ℝ`; its Laplace transform is the general Dirichlet series
`∑ₖ cₖ λₖ ^ (-s)`. -/
noncomputable def diracMeasure (c : ℕ → ℝ) (l : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun k ↦ ENNReal.ofReal (c k) • Measure.dirac (Real.log (l k))

variable {c : ℕ → ℝ} {l : ℕ → ℝ}

/-- `diracMeasure c l` is carried by `[0, ∞)` when `λₖ ≥ 1`. -/
theorem ae_nonneg_diracMeasure (hl : ∀ k, 1 ≤ l k) : ∀ᵐ u ∂diracMeasure c l, 0 ≤ u := by
  rw [diracMeasure, Measure.ae_sum_iff]
  exact fun k ↦ Measure.ae_smul_measure ((ae_dirac_iff (measurableSet_le measurable_const
    measurable_id)).2 (Real.log_nonneg (hl k))) _

/-- `∫ exp (-σ u) d(diracMeasure c l)(u) = ∑ₖ cₖ λₖ ^ (-σ)`. -/
theorem lintegral_diracMeasure (hc : ∀ k, 0 ≤ c k) (hl : ∀ k, 1 ≤ l k) (σ : ℝ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(σ * u))) ∂diracMeasure c l =
      ∑' k, ENNReal.ofReal (c k * l k ^ (-σ)) := by
  rw [diracMeasure, lintegral_sum_measure]
  refine tsum_congr fun k ↦ ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, ← ENNReal.ofReal_mul (hc k),
    Real.rpow_def_of_pos (by linarith [hl k])]
  ring_nf

/-- `u ↦ exp (-σ u)` is integrable for `diracMeasure c l` if and only if `∑ₖ cₖ λₖ ^ (-σ)`
converges. -/
theorem integrable_diracMeasure_iff (hc : ∀ k, 0 ≤ c k) (hl : ∀ k, 1 ≤ l k) (σ : ℝ) :
    Integrable (fun u ↦ Real.exp (-(σ * u))) (diracMeasure c l) ↔
      Summable fun k ↦ c k * l k ^ (-σ) := by
  have h0 : ∀ k, 0 ≤ c k * l k ^ (-σ) := fun k ↦
    mul_nonneg (hc k) (Real.rpow_nonneg (by linarith [hl k]) _)
  rw [Integrable, and_iff_right (by fun_prop), hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun u ↦ (Real.exp_pos _).le), lintegral_diracMeasure hc hl]
  constructor
  · intro h
    simpa [ENNReal.toReal_ofReal (h0 _)] using ENNReal.summable_toReal h.ne
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg h0 h]
    exact ENNReal.ofReal_lt_top

/-- The Laplace transform of `diracMeasure c l` is the Dirichlet series `∑ₖ cₖ λₖ ^ (-s)` where
the latter converges absolutely. -/
theorem complexMGF_diracMeasure (hc : ∀ k, 0 ≤ c k) (hl : ∀ k, 1 ≤ l k) {s : ℂ}
    (hs : Summable fun k ↦ c k * l k ^ (-s.re)) :
    complexMGF (fun u ↦ -u) (diracMeasure c l) s = ∑' k, (c k : ℂ) * (l k : ℂ) ^ (-s) := by
  have hint : Integrable (fun u : ℝ ↦ cexp (s * ((-u : ℝ) : ℂ))) (diracMeasure c l) :=
    integrable_cexp_mul_of_re_mem_integrableExpSet measurable_neg.aemeasurable
      (mem_integrableExpSet_neg_iff.2 ((integrable_diracMeasure_iff hc hl _).2 hs))
  rw [complexMGF, diracMeasure, integral_sum_measure hint]
  refine tsum_congr fun k ↦ ?_
  have hl0 : (0 : ℝ) < l k := by linarith [hl k]
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc k), Complex.real_smul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hl0.ne'), ← ofReal_log hl0.le]
  push_cast
  ring_nf

/-- **Landau's theorem for Dirichlet series with nonnegative coefficients.** Let `cₖ ≥ 0` and
`λₖ ≥ 1`, and suppose that `F(s) = ∑ₖ cₖ λₖ ^ (-s)` converges for every real `s > σ₀`. If `F`
extends holomorphically to a neighbourhood of the real point `σ₀` (some `G` holomorphic on a disc
about `σ₀` agrees with `F` where `re s > σ₀`), then the series converges at some real `σ < σ₀`.
In particular the abscissa of convergence of such a series is a singularity of its sum. -/
theorem exists_lt_summable_mul_rpow_neg (hc : ∀ k, 0 ≤ c k) (hl : ∀ k, 1 ≤ l k) {σ₀ : ℝ}
    (hsum : ∀ σ, σ₀ < σ → Summable fun k ↦ c k * l k ^ (-σ)) {G : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hG : DifferentiableOn ℂ G (Metric.ball (σ₀ : ℂ) ε))
    (hGF : ∀ s ∈ Metric.ball (σ₀ : ℂ) ε, σ₀ < s.re → G s = ∑' k, (c k : ℂ) * (l k : ℂ) ^ (-s)) :
    ∃ σ < σ₀, Summable fun k ↦ c k * l k ^ (-σ) := by
  obtain ⟨σ, hσ, h⟩ := exists_lt_integrable_exp_neg_mul (ae_nonneg_diracMeasure hl)
    (fun σ hσ ↦ (integrable_diracMeasure_iff hc hl σ).2 (hsum σ hσ)) hε hG
    fun s hs hre ↦ by rw [hGF s hs hre, complexMGF_diracMeasure hc hl (hsum _ hre)]
  exact ⟨σ, hσ, (integrable_diracMeasure_iff hc hl σ).1 h⟩

end DiracMeasure

section Bias

/-- If `0 ≤ Hₖ ≤ B qₖ ^ θ` with `0 ≤ θ < σ`, then `∑ₖ Hₖ (qₖ ^ (-σ) - qₖ₊₁ ^ (-σ))` converges. -/
theorem summable_mul_rpow_neg_sub_of_le_rpow {H : ℕ → ℝ} {q : ℕ → ℕ} {B θ σ : ℝ}
    (hH : ∀ k, 0 ≤ H k) (hHB : ∀ k, H k ≤ B * (q k : ℝ) ^ θ) (hq₀ : 0 < q 0) (hq : StrictMono q)
    (hθ : 0 ≤ θ) (hθσ : θ < σ) :
    Summable fun k ↦ H k * ((q k : ℝ) ^ (-σ) - (q (k + 1) : ℝ) ^ (-σ)) := by
  have hd : ∀ k, 0 ≤ (q k : ℝ) ^ (-σ) - (q (k + 1) : ℝ) ^ (-σ) := fun k ↦
    sub_nonneg.2 (antitone_natCast_rpow_neg hq₀ hq (by linarith) k.le_succ)
  have hB : 0 ≤ B := nonneg_of_mul_nonneg_left ((hH 0).trans (hHB 0))
    (Real.rpow_pos_of_pos (by exact_mod_cast hq₀) _)
  refine .of_nonneg_of_le (fun k ↦ mul_nonneg (hH k) (hd k)) (fun k ↦ ?_)
    ((summable_sub_of_antitone (antitone_natCast_rpow_neg hq₀ hq (by linarith : 0 ≤ σ - θ))
      fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).mul_left (B * (σ / (σ - θ))))
  have hqk : (0 : ℝ) < q k := by exact_mod_cast hq₀.trans_le (hq.monotone k.zero_le)
  calc H k * ((q k : ℝ) ^ (-σ) - (q (k + 1) : ℝ) ^ (-σ))
      ≤ B * (q k : ℝ) ^ θ * ((q k : ℝ) ^ (-σ) - (q (k + 1) : ℝ) ^ (-σ)) :=
        mul_le_mul_of_nonneg_right (hHB k) (hd k)
    _ = B * ((q k : ℝ) ^ θ * ((q k : ℝ) ^ (-σ) - (q (k + 1) : ℝ) ^ (-σ))) := by ring
    _ ≤ B * (σ / (σ - θ) * ((q k : ℝ) ^ (-(σ - θ)) - (q (k + 1) : ℝ) ^ (-(σ - θ)))) :=
        mul_le_mul_of_nonneg_left (rpow_mul_rpow_neg_sub_rpow_neg_le hqk
          (by exact_mod_cast hq.monotone k.le_succ) hθ hθσ) hB
    _ = _ := by ring

/-- Every sequence is the sequence of partial sums `∑_{j ≤ k} a j` of some sequence `a`. -/
theorem exists_sum_range_succ_eq {M : Type*} [AddCommGroup M] (b : ℕ → M) :
    ∃ a : ℕ → M, ∀ k, ∑ j ∈ range (k + 1), a j = b k := by
  refine ⟨fun j ↦ b j - if j = 0 then 0 else b (j - 1), fun k ↦ ?_⟩
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; simp

/-- One-sided analogue of `exists_forall_norm_le_mul_of_isBigO`: an eventual lower bound
`-(C g k) ≤ r k` with `g > 0` becomes a bound for all `k` after enlarging `C`. -/
theorem exists_forall_neg_mul_le_of_eventually {r g : ℕ → ℝ} (hg : ∀ k, 0 < g k) {C : ℝ}
    (h : ∀ᶠ k in atTop, -(C * g k) ≤ r k) : ∃ C' : ℝ, ∀ k, -(C' * g k) ≤ r k := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  set M := ∑ k ∈ range N, |r k| / g k
  have hM : 0 ≤ M := sum_nonneg fun k _ ↦ div_nonneg (abs_nonneg _) (hg k).le
  refine ⟨|C| + M, fun k ↦ ?_⟩
  by_cases hk : N ≤ k
  · nlinarith [hN k hk, mul_nonneg (sub_nonneg.2 (le_abs_self C)) (hg k).le,
      mul_nonneg hM (hg k).le]
  · have h1 : |r k| / g k ≤ M :=
      single_le_sum (fun j _ ↦ div_nonneg (abs_nonneg _) (hg j).le) (mem_range.2 (by omega))
    rw [div_le_iff₀ (hg k)] at h1
    nlinarith [neg_abs_le (r k), mul_nonneg (abs_nonneg C) (hg k).le]

/-- `(x + 1) ^ (1 / 2) / (log (x + 1)) ^ A ≤ 2 ^ (1 / 2) · x ^ (1 / 2) / (log x) ^ A` for `x ≥ 2`
and `A ≥ 0`. -/
theorem rpow_div_log_rpow_add_one_le {x A : ℝ} (hx : 2 ≤ x) (hA : 0 ≤ A) :
    (x + 1) ^ (1 / 2 : ℝ) / Real.log (x + 1) ^ A ≤
      2 ^ (1 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) / Real.log x ^ A) := by
  rw [← mul_div_assoc, ← Real.mul_rpow (by norm_num) (by linarith)]
  exact div_le_div₀ (by positivity) (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
    (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A)
    (Real.rpow_le_rpow (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith)
      (by linarith)) hA)

/-- For `k ≥ 4096` and `A ≥ 0`,
`k ^ (1 / 2) / (log k) ^ A ≤ 5 ^ (1 / 2) 2 ^ A · pₖ ^ (1 / 2) / (log pₖ) ^ (A + 1 / 2)`, by
Chebyshev's bounds `(k + 1) log pₖ ≤ 5 pₖ` and `log pₖ ≤ 2 log k`. -/
theorem rpow_div_log_rpow_le_nthPrime {k : ℕ} (hk : 4096 ≤ k) {A : ℝ} (hA : 0 ≤ A) :
    (k : ℝ) ^ (1 / 2 : ℝ) / Real.log k ^ A ≤ (5 : ℝ) ^ (1 / 2 : ℝ) * 2 ^ A *
      ((nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ (A + 1 / 2)) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hkp : (k : ℝ) ≤ nthPrime k := by
    exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)
  have hlk := Real.log_pos hk1
  have hL := Real.log_pos (hk1.trans_le hkp)
  have hlog := Nat.log_nth_prime_le_two_mul_log hk
  have hU := Nat.succ_mul_log_nth_prime_le k
  rw [mul_div_assoc', div_le_div_iff₀ (Real.rpow_pos_of_pos hlk A) (Real.rpow_pos_of_pos hL _),
    Real.rpow_add hL]
  have h1 : (k : ℝ) ^ (1 / 2 : ℝ) * Real.log (nthPrime k) ^ (1 / 2 : ℝ) ≤
      (5 : ℝ) ^ (1 / 2 : ℝ) * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) hL.le, ← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
  have h2 : Real.log (nthPrime k) ^ A ≤ 2 ^ A * Real.log k ^ A := by
    rw [← Real.mul_rpow (by norm_num) hlk.le]
    exact Real.rpow_le_rpow hL.le hlog hA
  calc (k : ℝ) ^ (1 / 2 : ℝ) * (Real.log (nthPrime k) ^ A * Real.log (nthPrime k) ^ (1 / 2 : ℝ))
      = (k : ℝ) ^ (1 / 2 : ℝ) * Real.log (nthPrime k) ^ (1 / 2 : ℝ) *
          Real.log (nthPrime k) ^ A := by ring
    _ ≤ (5 : ℝ) ^ (1 / 2 : ℝ) * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) * (2 ^ A * Real.log k ^ A) := by
        gcongr
    _ = _ := by ring

end Bias

namespace DirichletCharacter.IsQuadratic

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **The one-sided bias theorem, prime-scale form.** For a nonprincipal quadratic character `χ`
and `A > 1`, there is no constant `C` with `∑_{j ≤ k} χ(pⱼ) ≥ -C pₖ ^ (1 / 2) / (log pₖ) ^ A` for
all `k`: the partial sums dip below `-C pₖ ^ (1 / 2) / (log pₖ) ^ A` infinitely often, for every
`C`.

Under such a bound `h = S + C g ≥ 0` (with `g(x) = x ^ (1 / 2) / (log x) ^ A`), and the Mellin
transform `F(σ) = ∫ h(x) x ^ (-σ - 1) dx ≥ 0` of `h` satisfies
`σ F(σ) = log ‖L(σ, χ)‖ + Γ(σ) - re (primePowerPart χ σ)` to the right of its abscissa of
convergence `σ_c`, where `Γ` (the transform of `C g`) is continuous on `[1 / 2, 2]`. By Landau's
theorem `σ_c` is a singularity, so either `σ_c = 1 / 2`, where the prime-power part tends to `+∞`,
or `L(σ_c, χ) = 0`, where `log ‖L‖ → -∞`; in both cases the right side tends to `-∞`, which
contradicts `F ≥ 0`. -/
theorem not_exists_le_re_sum_succ_nthPrime_rpow_div_log_rpow (hχ : χ.IsQuadratic)
    (hχ₁ : χ ≠ 1) {A : ℝ} (hA : 1 < A) :
    ¬ ∃ C : ℝ, ∀ k, -(C * ((nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ A)) ≤
      (∑ j ∈ range (k + 1), χ (nthPrime j)).re := by
  rintro ⟨C, hC⟩
  set S : ℕ → ℂ := fun k ↦ ∑ j ∈ range (k + 1), χ (nthPrime j) with hS
  set g : ℕ → ℝ := fun k ↦ (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ A with hg
  have hp2 : ∀ k, (2 : ℝ) ≤ nthPrime k := fun k ↦ by
    exact_mod_cast (Nat.prime_nth_prime k).two_le
  have hg0 : ∀ k, 0 < g k := fun k ↦ rpow_div_log_rpow_pos (by linarith [hp2 k]) _ _
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, -(C * g k) ≤ (S k).re :=
    ⟨|C|, abs_nonneg C, fun k ↦ (neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self C)
      (hg0 k).le)).trans (hC k)⟩
  have hq₀ : 0 < nthPrime 0 := (Nat.prime_nth_prime 0).pos
  have hl2 : 0 < Real.log 2 ^ A := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) A
  -- `S k` is real, and `‖S k‖ ≤ k + 1 ≤ pₖ`
  have hSre : ∀ k, (((S k).re : ℝ) : ℂ) = S k := fun k ↦ by
    simp only [hS]
    rw [sum_congr rfl fun j _ ↦ apply_eq_ofReal_re hχ _]
    simp
  have hSn : ∀ k, ‖S k‖ ≤ 1 * (nthPrime k : ℝ) ^ (1 : ℝ) := fun k ↦ by
    rw [one_mul, Real.rpow_one]
    refine (norm_sum_le _ _).trans ((sum_le_card_nsmul _ _ 1 fun j _ ↦ χ.norm_le_one _).trans ?_)
    simp only [card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)
  have hgle : ∀ k, g k ≤ (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log 2 ^ A := fun k ↦
    div_le_div_of_nonneg_left (by positivity) hl2 (Real.rpow_le_rpow
      (Real.log_nonneg one_le_two) (Real.log_le_log two_pos (hp2 k)) (by linarith))
  -- the nonnegative function `h = S + C g`, through its values `H k` on `[pₖ, pₖ₊₁)`
  set H : ℕ → ℝ := fun k ↦ (S k).re + C * g k with hH
  have hH0 : ∀ k, 0 ≤ H k := fun k ↦ by simp only [hH]; linarith [hC k]
  have hHle : ∀ k, H k ≤ (1 + C / Real.log 2 ^ A) * (nthPrime k : ℝ) ^ (1 : ℝ) := fun k ↦ by
    have h1 : (S k).re ≤ nthPrime k := (re_le_norm _).trans (by simpa using hSn k)
    have h2 : (nthPrime k : ℝ) ^ (1 / 2 : ℝ) ≤ nthPrime k := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith [hp2 k] : (1 : ℝ) ≤ nthPrime k)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have h3 : C * g k ≤ C / Real.log 2 ^ A * nthPrime k := by
      calc C * g k ≤ C * ((nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log 2 ^ A) :=
            mul_le_mul_of_nonneg_left (hgle k) hC0
        _ ≤ C * (nthPrime k / Real.log 2 ^ A) := by gcongr
        _ = _ := by ring
    rw [Real.rpow_one, add_mul, one_mul]
    simp only [hH]
    linarith
  set μ := stepMeasure H nthPrime with hμdef
  have hμ : ∀ᵐ u ∂μ, 0 ≤ u := ae_nonneg_stepMeasure hq₀ nthPrime_strictMono
  have hsum1 : ∀ σ : ℝ, 1 < σ →
      Summable fun k ↦ H k * ((nthPrime k : ℝ) ^ (-σ) - (nthPrime (k + 1) : ℝ) ^ (-σ)) :=
    fun σ hσ ↦ summable_mul_rpow_neg_sub_of_le_rpow hH0 hHle hq₀ nthPrime_strictMono
      zero_le_one hσ
  have hint1 : ∀ σ : ℝ, 1 < σ → Integrable (fun u ↦ Real.exp (-(σ * u))) μ := fun σ hσ ↦
    integrable_stepMeasure hH0 hq₀ nthPrime_strictMono (by linarith) (hsum1 σ hσ)
  set F := complexMGF (fun u : ℝ ↦ -u) μ with hF
  -- the transform `Γ` of `C g`, an Abel series with partial sums `C g k`
  obtain ⟨a, ha⟩ := exists_sum_range_succ_eq fun k ↦ ((C * g k : ℝ) : ℂ)
  set Γ := abelSeries a nthPrime with hΓ
  have haC : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤
      C * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ A := fun k ↦ by
    rw [ha k, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC0 (hg0 k).le), mul_div_assoc]
  have haC' : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤
      C / Real.log 2 ^ A * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) := fun k ↦ by
    rw [ha k, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC0 (hg0 k).le)]
    calc C * g k ≤ C * ((nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log 2 ^ A) :=
          mul_le_mul_of_nonneg_left (hgle k) hC0
      _ = _ := by ring
  have hΓd : DifferentiableOn ℂ Γ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_abelSeries_of_le_rpow (by norm_num) haC' hq₀ nthPrime_strictMono
  have hΓc : ContinuousOn (fun σ : ℝ ↦ Γ σ) (Set.Icc (1 / 2) 2) :=
    continuousOn_abelSeries_of_le_rpow_div_log_rpow hA haC (Nat.prime_nth_prime 0).two_le
      nthPrime_strictMono Nat.nth_prime_succ_le_two_mul
  set P := χ.primePowerPart with hP
  have hPd : DifferentiableOn ℂ P {s : ℂ | 1 / 2 < s.re} := χ.differentiableOn_primePowerPart
  set L := LFunction χ with hL
  have hLd : Differentiable ℂ L := differentiable_LFunction hχ₁
  -- `s F(s) = primePart χ s + Γ(s)` for `re s > 1`
  have hFid : ∀ s : ℂ, 1 < s.re → s * F s = χ.primePart s + Γ s := by
    intro s hs
    rw [hF, hμdef, mul_complexMGF_stepMeasure hH0 hq₀ nthPrime_strictMono (by linarith)
      (hsum1 _ hs)]
    have h1 := summable_abelSeries_of_le_rpow zero_le_one hSn hq₀ nthPrime_strictMono hs
    have h2 := summable_abelSeries_of_le_rpow (by norm_num) haC' hq₀ nthPrime_strictMono
      (show (1 / 2 : ℝ) < s.re by linarith)
    have h3 : χ.primePart s = abelSeries (fun k ↦ χ (nthPrime k)) nthPrime s :=
      (abelSeries_eq_tsum_of_le_rpow zero_le_one hSn (fun _ ↦ χ.norm_le_one _) hq₀
        nthPrime_strictMono hs hs).symm
    rw [h3, hΓ, abelSeries, abelSeries, ← h1.tsum_add h2]
    refine tsum_congr fun k ↦ ?_
    rw [ha k, ← add_mul]
    congr 1
    simp only [hH]
    push_cast
    rw [hSre k]
  -- `E(s) = s F(s) - Γ(s) + primePowerPart χ s` is a logarithm of `L(s, χ)`
  set E : ℂ → ℂ := fun s ↦ s * F s - Γ s + P s with hE
  -- the abscissa of convergence `σc ∈ [1 / 2, 3 / 2]` of the Mellin transform `F`
  set T : Set ℝ := {σ | 1 / 2 < σ ∧ Integrable (fun u ↦ Real.exp (-(σ * u))) μ} with hT
  have hT32 : (3 / 2 : ℝ) ∈ T := ⟨by norm_num, hint1 _ (by norm_num)⟩
  have hTb : BddBelow T := ⟨1 / 2, fun σ hσ ↦ hσ.1.le⟩
  set σc := sInf T with hσcdef
  have hσc : 1 / 2 ≤ σc := le_csInf ⟨_, hT32⟩ fun σ hσ ↦ hσ.1.le
  have hσc2 : σc < 2 := (csInf_le hTb hT32).trans_lt (by norm_num)
  have hTc : ∀ σ : ℝ, σc < σ → Integrable (fun u ↦ Real.exp (-(σ * u))) μ := fun σ hσ ↦ by
    obtain ⟨τ, hτ, hτσ⟩ := exists_lt_of_csInf_lt ⟨_, hT32⟩ hσ
    exact integrable_exp_neg_mul_of_le hμ hτσ.le hτ.2
  have hsub : {s : ℂ | σc < s.re} ⊆ {s : ℂ | 1 / 2 < s.re} := fun s (hs : σc < s.re) ↦
    show 1 / 2 < s.re by linarith
  have hFd : DifferentiableOn ℂ F {s : ℂ | σc < s.re} := differentiableOn_complexMGF_neg hμ hTc
  have hEd : DifferentiableOn ℂ E {s : ℂ | σc < s.re} :=
    ((differentiableOn_id.mul hFd).sub (hΓd.mono hsub)).add (hPd.mono hsub)
  have hU : IsOpen {s : ℂ | σc < s.re} := isOpen_lt continuous_const continuous_re
  have hEL : ∀ s : ℂ, σc < s.re → exp (E s) = L s := by
    have hfg : (fun s ↦ exp (E s)) =ᶠ[𝓝 2] L := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s (hs : 1 < s.re)
      simp only [hE]
      rw [hFid s hs, add_sub_cancel_right]
      exact χ.exp_primePart_add_primePowerPart hs
    intro s hs
    exact (hEd.cexp.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      (hLd.differentiableOn.analyticOnNhd hU) (convex_halfSpace_re_gt σc).isPreconnected
      (show σc < (2 : ℂ).re by simpa using hσc2) hfg hs
  have hLne : ∀ s : ℂ, σc < s.re → L s ≠ 0 := fun s hs ↦ by
    rw [← hEL s hs]
    exact exp_ne_zero _
  -- on the real axis: `0 ≤ σ F(σ) = log ‖L(σ, χ)‖ + Γ(σ) - primePowerPart χ σ`
  have hkey : ∀ σ : ℝ, σc < σ → 0 ≤ Real.log ‖L σ‖ + (Γ σ).re - (P σ).re := by
    intro σ hσ
    have hσ' : σc < (σ : ℂ).re := by simpa using hσ
    have h1 : Real.log ‖L σ‖ = (E σ).re := by
      rw [← hEL σ hσ', Complex.norm_exp, Real.log_exp]
    have h2 : 0 ≤ ((σ : ℂ) * F σ).re := by
      rw [hF, complexMGF_ofReal, ← ofReal_mul, ofReal_re]
      exact mul_nonneg (by linarith) mgf_nonneg
    have h3 : (σ : ℂ) * F σ = E σ + Γ σ - P σ := by
      simp only [hE]
      ring
    rw [h3, sub_re, add_re] at h2
    linarith
  have hcontra : ∀ f : ℝ → ℝ, Tendsto f (𝓝[>] σc) atBot → (∀ σ, σc < σ → 0 ≤ f σ) → False :=
    fun f hf h0 ↦ by
      obtain ⟨σ, h1, h2⟩ := ((hf.eventually (eventually_lt_atBot 0)).and
        (eventually_nhdsWithin_of_forall h0)).exists
      linarith
  have hLc : Tendsto (fun σ : ℝ ↦ ‖L σ‖) (𝓝 σc) (𝓝 ‖L σc‖) :=
    (hLd.continuous.comp continuous_ofReal).norm.tendsto σc
  have hΓlim : Tendsto (fun σ : ℝ ↦ (Γ σ).re) (𝓝[>] σc) (𝓝 (Γ σc).re) :=
    continuous_re.continuousAt.tendsto.comp ((hΓc σc ⟨hσc, hσc2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT_of_mem ⟨hσc, hσc2⟩)).tendsto
  rcases hσc.eq_or_lt with h12 | h12
  · -- `σc = 1 / 2`: the prime-power part tends to `+∞` while `log ‖L‖` stays bounded above
    have hPlim : Tendsto (fun σ : ℝ ↦ (P σ).re) (𝓝[>] σc) atTop := by
      rw [← h12]
      exact IsQuadratic.tendsto_re_primePowerPart χ hχ
    have hup : ∀ᶠ σ : ℝ in 𝓝[>] σc, Real.log ‖L σ‖ ≤ Real.log (‖L σc‖ + 1) := by
      filter_upwards [nhdsWithin_le_nhds (hLc.eventually (gt_mem_nhds (lt_add_one _))),
        self_mem_nhdsWithin] with σ h1 (hσ : σc < σ)
      exact Real.log_le_log (norm_pos_iff.2 (hLne σ (by simpa using hσ))) h1.le
    have h2 : Tendsto (fun σ : ℝ ↦ (Γ σ).re + -(P σ).re) (𝓝[>] σc) atBot :=
      hΓlim.add_atBot (tendsto_neg_atTop_atBot.comp hPlim)
    refine hcontra _ (tendsto_atBot_mono' _ ?_
      (tendsto_atBot_add_const_left _ (Real.log (‖L σc‖ + 1)) h2)) hkey
    filter_upwards [hup] with σ hσ
    linarith
  have hPlim : Tendsto (fun σ : ℝ ↦ (P σ).re) (𝓝[>] σc) (𝓝 (P σc).re) :=
    (continuous_re.continuousAt.tendsto.comp ((hPd.continuousOn.continuousAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (show 1 / 2 < (σc : ℂ).re by
        simpa using h12))).comp continuous_ofReal.continuousAt).tendsto).mono_left
      nhdsWithin_le_nhds
  by_cases hL0 : L σc = 0
  · -- a real zero `L(σc, χ) = 0`: `log ‖L‖ → -∞` while the other terms converge
    have hnorm : Tendsto (fun σ : ℝ ↦ ‖L σ‖) (𝓝[>] σc) (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by simpa [hL0] using hLc.mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun σ (hσ : σc < σ) ↦
          norm_pos_iff.2 (hLne σ (by simpa using hσ))⟩
    refine hcontra _ ?_ hkey
    simpa [add_sub_assoc] using (Real.tendsto_log_nhdsGT_zero.comp hnorm).atBot_add
      (hΓlim.sub hPlim)
  -- `L(σc, χ) ≠ 0` and `σc > 1 / 2`: the transform continues analytically across `σc`,
  -- contradicting Landau's theorem
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.continuousAt_iff.1
    ((hLd.continuous.continuousAt (x := (σc : ℂ))).div_const (L σc)) 1 one_pos
  set ε := min ε₀ ((σc - 1 / 2) / 2) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by linarith)
  have hεb : ∀ s ∈ Metric.ball (σc : ℂ) ε, ‖L s / L σc - 1‖ < 1 := fun s hs ↦ by
    have := hball (lt_of_lt_of_le hs (min_le_left _ _))
    rwa [div_self hL0, dist_eq_norm] at this
  have hre : ∀ s ∈ Metric.ball (σc : ℂ) ε, 1 / 2 < s.re ∧ σc - ε < s.re := fun s hs ↦ by
    have h1 := (abs_re_le_norm (s - σc)).trans_lt (by simpa [dist_eq_norm] using hs)
    rw [sub_re, ofReal_re, abs_lt] at h1
    have : ε ≤ (σc - 1 / 2) / 2 := min_le_right _ _
    constructor <;> linarith
  have hslit : ∀ s ∈ Metric.ball (σc : ℂ) ε, L s / L σc ∈ slitPlane := fun s hs ↦ by
    simpa using mem_slitPlane_of_norm_lt_one (hεb s hs)
  set ℓ : ℂ → ℂ := fun s ↦ log (L s / L σc) with hℓ
  have hℓd : DifferentiableOn ℂ ℓ (Metric.ball (σc : ℂ) ε) := fun s hs ↦
    (((hLd s).div_const _).clog (hslit s hs)).differentiableWithinAt
  have hℓexp : ∀ s ∈ Metric.ball (σc : ℂ) ε, exp (ℓ s) = L s / L σc := fun s hs ↦
    exp_log (slitPlane_ne_zero (hslit s hs))
  -- `E - ℓ` is constant on the right half of the disc
  set U := Metric.ball (σc : ℂ) ε ∩ {s : ℂ | σc < s.re} with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball.inter hU
  have hUc : IsPreconnected U :=
    ((convex_ball _ _).inter (convex_halfSpace_re_gt σc)).isPreconnected
  set d : ℂ → ℂ := fun s ↦ E s - ℓ s with hd
  have hdd : DifferentiableOn ℂ d U :=
    (hEd.mono Set.inter_subset_right).sub (hℓd.mono Set.inter_subset_left)
  have hdexp : ∀ s ∈ U, exp (d s) = L σc := fun s hs ↦ by
    rw [hd, exp_sub, hEL s hs.2, hℓexp s hs.1]
    field_simp [hLne s hs.2]
  have hd0 : U.EqOn (deriv d) 0 := fun s hs ↦ by
    have h1 : HasDerivAt (fun z ↦ exp (d z)) (exp (d s) * deriv d s) s :=
      ((hdd s hs).differentiableAt (hUo.mem_nhds hs)).hasDerivAt.cexp
    have h2 : HasDerivAt (fun z ↦ exp (d z)) 0 s :=
      (hasDerivAt_const s (L σc)).congr_of_eventuallyEq
        (eventually_of_mem (hUo.mem_nhds hs) hdexp)
    simpa [exp_ne_zero] using h1.unique h2
  have hs₀ : ((σc + ε / 2 : ℝ) : ℂ) ∈ U := by
    refine ⟨?_, show σc < ((σc + ε / 2 : ℝ) : ℂ).re by simp; linarith⟩
    rw [Metric.mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  set c := d ((σc + ε / 2 : ℝ) : ℂ) with hc
  -- the analytic continuation `G` of `F` to the disc about `σc`
  set G : ℂ → ℂ := fun s ↦ (ℓ s + c + Γ s - P s) / s with hG
  have hsubb : Metric.ball (σc : ℂ) ε ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs ↦ (hre s hs).1
  have hGd : DifferentiableOn ℂ G (Metric.ball (σc : ℂ) ε) :=
    ((((hℓd.add_const c).add (hΓd.mono hsubb)).sub (hPd.mono hsubb)).div differentiableOn_id
      fun s hs ↦ fun h ↦ by have := (hre s hs).1; simp [h] at this; linarith)
  have hGF : ∀ s ∈ Metric.ball (σc : ℂ) ε, σc < s.re → G s = F s := fun s hs hsre ↦ by
    have hdc : d s = c := hUo.is_const_of_deriv_eq_zero hUc hdd hd0 ⟨hs, hsre⟩ hs₀
    have hs0 : s ≠ 0 := fun h ↦ by have := (hre s hs).1; simp [h] at this; linarith
    simp only [hG]
    rw [div_eq_iff hs0]
    simp only [hd, hE] at hdc
    linear_combination -hdc
  obtain ⟨σ, hσ, hσint⟩ := exists_lt_integrable_exp_neg_mul hμ hTc hε hGd hGF
  have hσ'T : max σ ((σc + 1 / 2) / 2) ∈ T :=
    ⟨lt_max_of_lt_right (by linarith), integrable_exp_neg_mul_of_le hμ (le_max_left _ _) hσint⟩
  have h1 := csInf_le hTb hσ'T
  have h2 : max σ ((σc + 1 / 2) / 2) < σc := max_lt hσ (by linarith)
  linarith

/-- **The one-sided bias theorem, prime-scale `Ω₋` form.** For a nonprincipal quadratic character
`χ`, `A > 1` and every `C`, `∑_{j ≤ k} χ(pⱼ) < -C pₖ ^ (1 / 2) / (log pₖ) ^ A` for infinitely
many `k`. -/
theorem frequently_re_sum_succ_lt_nthPrime_rpow_div_log_rpow (hχ : χ.IsQuadratic)
    (hχ₁ : χ ≠ 1) {A : ℝ} (hA : 1 < A) (C : ℝ) :
    ∃ᶠ k in atTop, (∑ j ∈ range (k + 1), χ (nthPrime j)).re <
      -(C * ((nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ A)) := by
  by_contra h
  rw [not_frequently] at h
  exact not_exists_le_re_sum_succ_nthPrime_rpow_div_log_rpow hχ hχ₁ hA
    (exists_forall_neg_mul_le_of_eventually (fun k ↦ rpow_div_log_rpow_pos
      (by exact_mod_cast (Nat.prime_nth_prime k).one_lt) _ _) (h.mono fun _ hk ↦ not_lt.1 hk))

/-- **The one-sided bias theorem.** For a nonprincipal quadratic character `χ`, `A > 1` and
every `C`, `∑_{p < x} χ(p) < -C x ^ (1 / 2) / (log x) ^ A` for infinitely many `x`: in Landau's
notation, `∑_{p < x} χ(p) = Ω₋(x ^ (1 / 2) / (log x) ^ A)`. This is the direction of Chebyshev's
bias (more primes with `χ(p) = -1`). -/
theorem frequently_re_sum_primesBelow_lt_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1)
    {A : ℝ} (hA : 1 < A) (C : ℝ) :
    ∃ᶠ x : ℕ in atTop, (∑ p ∈ Nat.primesBelow x, χ p).re <
      -(C * ((x : ℝ) ^ (1 / 2 : ℝ) / Real.log x ^ A)) := by
  refine ((tendsto_add_atTop_nat 1).comp nthPrime_strictMono.tendsto_atTop).frequently_map _
    (fun k hk ↦ ?_)
    (frequently_re_sum_succ_lt_nthPrime_rpow_div_log_rpow hχ hχ₁ hA (|C| * 2 ^ (1 / 2 : ℝ)))
  have hp : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast (Nat.prime_nth_prime k).two_le
  simp only [Function.comp_apply]
  rw [χ.sum_primesBelow_eq, show Nat.primeCounting' (nthPrime k + 1) = k + 1 from
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k]
  refine hk.trans_le (neg_le_neg ?_)
  have h1 := rpow_div_log_rpow_add_one_le hp (by linarith : (0 : ℝ) ≤ A)
  have h2 : 0 ≤ ((nthPrime k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k + 1 : ℕ) ^ A :=
    (rpow_div_log_rpow_pos (by push_cast; linarith) _ _).le
  push_cast at h2 ⊢
  calc C * ((nthPrime k + 1 : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k + 1) ^ A)
      ≤ |C| * ((nthPrime k + 1 : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k + 1) ^ A) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) h2
    _ ≤ |C| * (2 ^ (1 / 2 : ℝ) * ((nthPrime k : ℝ) ^ (1 / 2 : ℝ) /
          Real.log (nthPrime k) ^ A)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = _ := by ring

/-- **The one-sided bias theorem**, bound form. For a nonprincipal quadratic character `χ` and
`A > 1`, there is no constant `C` with `∑_{p < x} χ(p) ≥ -C x ^ (1 / 2) / (log x) ^ A` for all
`x ≥ 2`. -/
theorem not_exists_le_sum_primesBelow_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1)
    {A : ℝ} (hA : 1 < A) :
    ¬ ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      -C * (x : ℝ) ^ (1 / 2 : ℝ) / Real.log x ^ A ≤ (∑ p ∈ Nat.primesBelow x, χ p).re := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx, h2⟩ := ((frequently_re_sum_primesBelow_lt_rpow_div_log_rpow hχ hχ₁ hA
    C).and_eventually (eventually_ge_atTop 2)).exists
  have := hC x h2
  rw [neg_mul, neg_div, mul_div_assoc] at this
  linarith

/-- **The one-sided bias theorem in the index scale.** For a nonprincipal quadratic character `χ`,
`A > 1 / 2` and every `C`, `∑_{j ≤ k} χ(pⱼ) < -C k ^ (1 / 2) / (log k) ^ A` for infinitely many
`k`. -/
theorem frequently_re_sum_succ_lt_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {A : ℝ}
    (hA : 1 / 2 < A) (C : ℝ) :
    ∃ᶠ k : ℕ in atTop, (∑ j ∈ range (k + 1), χ (nthPrime j)).re <
      -(C * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k ^ A)) := by
  refine (((frequently_re_sum_succ_lt_nthPrime_rpow_div_log_rpow hχ hχ₁ (A := A + 1 / 2)
    (by linarith) (|C| * ((5 : ℝ) ^ (1 / 2 : ℝ) * 2 ^ A))).and_eventually
      (eventually_ge_atTop 4096)).mono fun k ⟨hk, hk4⟩ ↦ hk.trans_le (neg_le_neg ?_))
  have h1 := rpow_div_log_rpow_le_nthPrime hk4 (by linarith : (0 : ℝ) ≤ A)
  have h2 : 0 ≤ (k : ℝ) ^ (1 / 2 : ℝ) / Real.log k ^ A :=
    (rpow_div_log_rpow_pos (by exact_mod_cast (by omega : 1 < k)) _ _).le
  calc C * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k ^ A)
      ≤ |C| * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k ^ A) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) h2
    _ ≤ |C| * ((5 : ℝ) ^ (1 / 2 : ℝ) * 2 ^ A * ((nthPrime k : ℝ) ^ (1 / 2 : ℝ) /
          Real.log (nthPrime k) ^ (A + 1 / 2))) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = _ := by ring

/-- **The one-sided bias theorem in the index scale.** For a nonprincipal quadratic character `χ`,
`A > 1 / 2` and every `C`, `∑_{k < n} χ(pₖ) < -C n ^ (1 / 2) / (log n) ^ A` for infinitely many
`n`. -/
theorem frequently_re_sum_lt_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {A : ℝ}
    (hA : 1 / 2 < A) (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, (∑ k ∈ range n, χ (nthPrime k)).re <
      -(C * ((n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ A)) := by
  refine (tendsto_add_atTop_nat 1).frequently_map _ (fun k hk ↦ ?_)
    (((frequently_re_sum_succ_lt_rpow_div_log_rpow hχ hχ₁ hA (|C| * 2 ^ (1 / 2 : ℝ))).and_eventually
      (eventually_ge_atTop 2)))
  obtain ⟨hk, hk2⟩ := hk
  refine hk.trans_le (neg_le_neg ?_)
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have h1 := rpow_div_log_rpow_add_one_le hk2' (by linarith : (0 : ℝ) ≤ A)
  have h2 : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / Real.log (k + 1 : ℕ) ^ A :=
    (rpow_div_log_rpow_pos (by push_cast; linarith) _ _).le
  push_cast at h2 ⊢
  calc C * (((k : ℝ) + 1) ^ (1 / 2 : ℝ) / Real.log ((k : ℝ) + 1) ^ A)
      ≤ |C| * (((k : ℝ) + 1) ^ (1 / 2 : ℝ) / Real.log ((k : ℝ) + 1) ^ A) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) h2
    _ ≤ |C| * (2 ^ (1 / 2 : ℝ) * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k ^ A)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = _ := by ring

/-- **The one-sided bias theorem in the index scale**, bound form. For a nonprincipal quadratic
character `χ` and `A > 1 / 2`, there is no constant `C` with
`∑_{k < n} χ(pₖ) ≥ -C n ^ (1 / 2) / (log n) ^ A` for all `n ≥ 2`. -/
theorem not_exists_le_re_sum_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {A : ℝ}
    (hA : 1 / 2 < A) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      -C * (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ A ≤ (∑ k ∈ range n, χ (nthPrime k)).re := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn, h2⟩ := ((frequently_re_sum_lt_rpow_div_log_rpow hχ hχ₁ hA C).and_eventually
    (eventually_ge_atTop 2)).exists
  have := hC n h2
  rw [neg_mul, neg_div, mul_div_assoc] at this
  linarith

end DirichletCharacter.IsQuadratic

namespace RokickiConstant

/-- **The digits of `ρ` lean towards `1`.** For `A > 1 / 2` and every `C`, among the first `n`
binary digits of `ρ` the digits `1` outnumber the digits `0` by more than
`C n ^ (1 / 2) / (log n) ^ A` for infinitely many `n`. (A digit `1` records a prime `≡ 3 mod 4`,
where `χ₄ = -1`; so this is the `Ω₋` theorem for `χ₄`, the direction of Chebyshev's bias.) -/
theorem frequently_card_rokickiDigit_one_sub_card_zero_gt {A : ℝ} (hA : 1 / 2 < A) (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, C * ((n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ A) <
      (#{k ∈ range n | Real.rokickiDigit k = 1} : ℝ) -
        #{k ∈ range n | Real.rokickiDigit k = 0} := by
  have hχ : chi4.IsQuadratic := ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)
  refine (DirichletCharacter.IsQuadratic.frequently_re_sum_succ_lt_rpow_div_log_rpow hχ
    chi4_ne_one hA C).mono fun n hn ↦ ?_
  rw [sum_range_succ_chi4_nthPrime, ofReal_re, sum_one_sub_two_mul_rokickiDigit] at hn
  linarith

/-- **The digits of `ρ` lean towards `1`**, bound form. For `A > 1 / 2` there is no constant `C`
such that, for all `n ≥ 2`, the number of digits `1` minus the number of digits `0` among the
first `n` binary digits of `ρ` is at most `C n ^ (1 / 2) / (log n) ^ A`. -/
theorem not_exists_card_rokickiDigit_one_sub_card_zero_le {A : ℝ} (hA : 1 / 2 < A) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      (#{k ∈ range n | Real.rokickiDigit k = 1} : ℝ) - #{k ∈ range n | Real.rokickiDigit k = 0} ≤
        C * (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ A := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn, h2⟩ := ((frequently_card_rokickiDigit_one_sub_card_zero_gt hA C).and_eventually
    (eventually_ge_atTop 2)).exists
  have := hC n h2
  rw [mul_div_assoc] at this
  linarith

end RokickiConstant
