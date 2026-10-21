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

variable {q : ℕ} (χ : DirichletCharacter ℂ q)

variable [NeZero q] in
/-- If `exp (F σ) = L(σ, χ)` to the right of `x`, then `exp (re (F σ)) → ‖L(x, χ)‖` as
`σ → x⁺`, for nonprincipal `χ`. -/
theorem tendsto_exp_re_of_exp_eq_LFunction (hχ : χ ≠ 1) {F : ℂ → ℂ} {x : ℝ}
    (hF : ∀ σ : ℝ, x < σ → exp (F σ) = LFunction χ σ) :
    Tendsto (fun σ : ℝ ↦ Real.exp (F σ).re) (𝓝[>] x) (𝓝 ‖LFunction χ x‖) :=
  (tendsto_nhdsWithin_of_tendsto_nhds (((differentiable_LFunction hχ).continuous.comp
    continuous_ofReal).norm.tendsto x)).congr'
    (eventually_nhdsWithin_of_forall fun σ hσ ↦ by simp [← hF σ hσ, Complex.norm_exp])

/-- The sums over the primes below `x` are partial sums of the sums over `k`. -/
theorem sum_primesBelow_eq (x : ℕ) :
    ∑ p ∈ Nat.primesBelow x, χ p = ∑ k ∈ range (Nat.primeCounting' x), χ (nthPrime k) := by
  have h : Nat.primesBelow x = (range (Nat.primeCounting' x)).image nthPrime := by
    ext p
    simp only [Nat.mem_primesBelow, mem_image, mem_range]
    constructor
    · rintro ⟨hpx, hp⟩
      refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hp⟩
      exact (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2 (by rwa [Nat.nth_count hp])
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).1 hk, Nat.prime_nth_prime k⟩
  rw [h, sum_image fun _ _ _ _ h ↦ nthPrime_strictMono.injective h]

namespace IsQuadratic

variable {χ} (hχ : χ.IsQuadratic)
include hχ

/-- A quadratic character takes real values: `χ n = re (χ n)`. -/
theorem apply_eq_ofReal_re (n : ZMod q) : χ n = ((χ n).re : ℂ) := by
  rcases hχ n with h | h | h <;> simp [h]

/-- Summation by parts: if `∑_{k < n} χ(pₖ) = c · n + O(1)` then
`re (primePart χ σ) = c ∑ₖ pₖ ^ (-σ) + O(1)` for real `σ > 1`. -/
theorem abs_re_primePart_sub_mul_tsum_le {c C : ℝ}
    (h : ∀ n, ‖(∑ k ∈ range n, χ (nthPrime k)) - c * n‖ ≤ C) {σ : ℝ} (hσ : 1 < σ) :
    |(χ.primePart σ).re - c * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ)| ≤ 2 * C := by
  have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
  have hfs : Summable fun k ↦ (nthPrime k : ℝ) ^ (-σ) := summable_nthPrime_rpow (by linarith)
  have hterm : ∀ k, (χ (nthPrime k) * (nthPrime k : ℂ) ^ (-(σ : ℂ))).re =
      (χ (nthPrime k)).re * (nthPrime k : ℝ) ^ (-σ) := fun k ↦ by
    rw [apply_eq_ofReal_re hχ, ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.ofReal_re]
  have hs : HasSum (fun k ↦ ((χ (nthPrime k)).re - c) * (nthPrime k : ℝ) ^ (-σ))
      ((χ.primePart σ).re - c * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ)) := by
    convert (hasSum_re (χ.summable_primeTerm hσ').hasSum).sub (hfs.hasSum.mul_left c) using 1
    · exact funext fun k ↦ by rw [sub_mul, ← hterm k]; rfl
    · rfl
  have he : ∀ n, |∑ k ∈ range n, ((χ (nthPrime k)).re - c)| ≤ C := fun n ↦ by
    refine le_trans (le_of_eq ?_) ((abs_re_le_norm _).trans (h n))
    simp [Finset.sum_sub_distrib, mul_comm]
  have hC : 0 ≤ C := (norm_nonneg _).trans (h 0)
  have hf0 : (nthPrime 0 : ℝ) ^ (-σ) ≤ 1 := by
    rw [Nat.nth_prime_zero_eq_two]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  rw [← hs.tsum_eq]
  calc _ ≤ 2 * C * (nthPrime 0 : ℝ) ^ (-σ) :=
        abs_tsum_mul_le_of_abs_sum_le he (fun _ ↦ by positivity)
          (antitone_natCast_rpow_neg (Nat.prime_nth_prime 0).pos nthPrime_strictMono
            (by linarith)) hs.summable
    _ ≤ 2 * C := mul_le_of_le_one_right (by linarith) hf0

variable [NeZero q] in
/-- The partial sums `∑_{k < n} χ(pₖ)` of a nonprincipal quadratic character are not of the form
`c · n + O(1)` with `c ≠ 0`. -/
theorem not_exists_norm_sum_sub_mul_le (hχ₁ : χ ≠ 1) :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n, ‖(∑ k ∈ range n, χ (nthPrime k)) - c * n‖ ≤ C := by
  rintro ⟨c, hc, C, h⟩
  obtain ⟨M, hM⟩ := χ.exists_norm_primePowerPart_le
  -- `re (primePart χ σ + primePowerPart χ σ) = log ‖L(σ, χ)‖` converges as `σ → 1⁺` ...
  have hlim := (χ.tendsto_exp_re_of_exp_eq_LFunction hχ₁
    (F := fun s ↦ χ.primePart s + χ.primePowerPart s)
    fun σ (hσ : 1 < σ) ↦ χ.exp_primePart_add_primePowerPart (by simpa using hσ)).log
    (by simpa using LFunction_apply_one_ne_zero hχ₁)
  simp only [Real.log_exp] at hlim
  -- ... but its absolute value is at least `|c| ∑ₖ pₖ ^ (-σ) - 2 C - M → ∞`.
  refine not_tendsto_atTop_of_tendsto_nhds hlim.abs (tendsto_atTop_mono' _ ?_
    (tendsto_atTop_add_const_right _ (-(2 * C + M))
      (tendsto_tsum_nthPrime_rpow_neg.const_mul_atTop (abs_pos.2 hc))))
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have h1 := abs_re_primePart_sub_mul_tsum_le hχ h hσ
  have h2 := (abs_re_le_norm _).trans (hM σ (by simp [hσ.le]))
  rw [abs_le] at h1 h2
  rcases abs_cases c with ⟨hc', -⟩ | ⟨hc', -⟩ <;> rw [hc', add_re, le_abs] <;> [left; right] <;>
    linarith [h1.1, h1.2, h2.1, h2.2]

omit hχ in
/-- Under bounded partial sums, the Abel series of `χ` over the primes is holomorphic on
`re s > 0`. -/
theorem differentiableOn_abelSeries {C : ℝ} (hC : ∀ n, ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C) :
    DifferentiableOn ℂ (abelSeries (fun k ↦ χ (nthPrime k)) nthPrime) {s : ℂ | 0 < s.re} :=
  _root_.differentiableOn_abelSeries hC (Nat.prime_nth_prime 0).pos nthPrime_strictMono

variable [NeZero q]

omit hχ in
/-- **Analytic continuation of the Euler product.** Under bounded partial sums,
`L(s, χ) = exp (abelSeries s + primePowerPart χ s)` for all `re s > 1 / 2`. -/
theorem exp_abelSeries_add_primePowerPart (hχ₁ : χ ≠ 1) {C : ℝ}
    (hC : ∀ n, ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C) {s : ℂ} (hs : 1 / 2 < s.re) :
    exp (abelSeries (fun k ↦ χ (nthPrime k)) nthPrime s + χ.primePowerPart s) =
      LFunction χ s := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ
      (fun s ↦ exp (abelSeries (fun k ↦ χ (nthPrime k)) nthPrime s + χ.primePowerPart s))
      {s : ℂ | 1 / 2 < s.re} :=
    (((IsQuadratic.differentiableOn_abelSeries hC).mono fun s (hs : 1 / 2 < s.re) ↦
      show 0 < s.re by linarith).add χ.differentiableOn_primePowerPart).cexp.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (LFunction χ) {s : ℂ | 1 / 2 < s.re} :=
    (differentiable_LFunction hχ₁).differentiableOn.analyticOnNhd hU
  have hfg : (fun s ↦ exp (abelSeries (fun k ↦ χ (nthPrime k)) nthPrime s +
      χ.primePowerPart s)) =ᶠ[𝓝 2] LFunction χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
    rw [abelSeries_eq_tsum hC (Nat.prime_nth_prime 0).pos nthPrime_strictMono hs]
    exact χ.exp_primePart_add_primePowerPart hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num) hfg hs

/-- The partial sums `∑_{k < n} χ(pₖ)` of a nonprincipal quadratic character are unbounded. -/
theorem not_exists_norm_sum_le (hχ₁ : χ ≠ 1) :
    ¬ ∃ C : ℝ, ∀ n, ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C := by
  rintro ⟨C, hC⟩
  set A := abelSeries (fun k ↦ χ (nthPrime k)) nthPrime
  -- `re (A σ)` is continuous at `σ = 1 / 2`, while `re (primePowerPart χ σ) → ∞` as `σ → 1 / 2⁺`
  have hA : ContinuousAt (fun σ : ℝ ↦ (A σ).re) (1 / 2) :=
    continuous_re.continuousAt.comp (((IsQuadratic.differentiableOn_abelSeries hC).continuousOn
      |>.continuousAt ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 0 < ((1 / 2 : ℝ) : ℂ).re by norm_num))).comp continuous_ofReal.continuousAt)
  exact not_tendsto_atTop_of_tendsto_nhds (χ.tendsto_exp_re_of_exp_eq_LFunction hχ₁
    (F := fun s ↦ A s + χ.primePowerPart s)
      fun σ (hσ : 1 / 2 < σ) ↦ exp_abelSeries_add_primePowerPart hχ₁ hC (by simpa using hσ))
    (Real.tendsto_exp_atTop.comp ((hA.tendsto.mono_left nhdsWithin_le_nhds).add_atTop
      (IsQuadratic.tendsto_re_primePowerPart χ hχ)))

/-- The sums `∑_{p < x} χ(p)` of a nonprincipal quadratic character over the primes below `x`
are not of the form `c · π(x) + O(1)` with `c ≠ 0`. -/
theorem not_exists_norm_sum_primesBelow_sub_mul_le (hχ₁ : χ ≠ 1) :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ x,
      ‖(∑ p ∈ Nat.primesBelow x, χ p) - c * Nat.primeCounting' x‖ ≤ C := by
  rintro ⟨c, hc, C, h⟩
  refine not_exists_norm_sum_sub_mul_le hχ hχ₁ ⟨c, hc, C, fun n ↦ ?_⟩
  simpa [sum_primesBelow_eq, Nat.primeCounting'_nth_eq] using h (nthPrime n)

/-- The sums `∑_{p < x} χ(p)` of a nonprincipal quadratic character over the primes below `x`
are unbounded. -/
theorem not_exists_norm_sum_primesBelow_le (hχ₁ : χ ≠ 1) :
    ¬ ∃ C : ℝ, ∀ x, ‖∑ p ∈ Nat.primesBelow x, χ p‖ ≤ C := by
  rintro ⟨C, h⟩
  refine not_exists_norm_sum_le hχ hχ₁ ⟨C, fun n ↦ ?_⟩
  simpa [sum_primesBelow_eq, Nat.primeCounting'_nth_eq] using h (nthPrime n)

end IsQuadratic

end DirichletCharacter
