/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import RokickiConstant.Chi4

/-!
# The Euler product of `L(s, χ₄)`

Let `χ₄` be the nontrivial Dirichlet character modulo `4` and write `3 = p₂ < p₃ < ⋯` for the odd
primes. Mathlib provides the Euler product of `L(s, χ₄)` in logarithmic form,
`L(s, χ₄) = exp (∑_p -log (1 - χ₄(p) p^{-s}))` for `re s > 1`
(`DirichletCharacter.LSeries_eulerProduct_exp_log`). Since `χ₄(2) = 0`, splitting off the
linear term of each logarithm gives
$$`L(s, \chi_4) = \exp\Big(\sum_p \chi_4(p) p^{-s}
  + \sum_p \big(-\log(1 - \chi_4(p) p^{-s}) - \chi_4(p) p^{-s}\big)\Big),
  \qquad \operatorname{re} s > 1,`
where the sums run over the odd primes. The first sum is `primePart s`, the second
`primePowerPart s`; by the Taylor series of the logarithm, its `p`-th term is
`∑_{m ≥ 2} χ₄(p)^m p^{-ms} / m`. Using Mathlib's bounds on the Taylor remainders of the
logarithm we prove that `primePowerPart` is holomorphic on `re s > 1 / 2`, bounded on `re s ≥ 1`,
and that its real part tends to `+∞` as `s → 1 / 2⁺` along the reals: its `p`-th term is
`p^{-2s} / 2 + O(p^{-3s})` there, and `∑_p 1 / p` diverges.

The consequences for the partial sums of `χ₄` over the primes are drawn in
`RokickiConstant.CharacterSums`.

## Main definitions

* `RokickiConstant.primePart s`: `∑ₖ χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)`.
* `RokickiConstant.primePowerPart s`:
  `∑ₖ (-log (1 - χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)) - χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s))`, the terms with `m ≥ 2` of the
  Taylor series of the logarithm.

## Main statements

* `RokickiConstant.exp_primePart_add_primePowerPart`: the Euler product in the form above.
* `RokickiConstant.differentiableOn_primePowerPart`: `primePowerPart` is holomorphic on
  `re s > 1 / 2`.
* `RokickiConstant.exists_norm_primePowerPart_le`: `primePowerPart` is bounded on `re s ≥ 1`.
* `RokickiConstant.tendsto_re_primePowerPart`: `re (primePowerPart σ) → +∞` as `σ → 1 / 2⁺`.

## Tags

Dirichlet character, L-function, Euler product
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Complex

namespace RokickiConstant

section LogTaylor

/-- For `‖z‖ < 1`, `1 - z` lies in the slit plane. -/
theorem one_sub_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ∈ slitPlane := by
  simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one (z := -z) (by rwa [norm_neg])

/-- For `‖z‖ ≤ 3 / 4`, the remainder of the Taylor series of `-log (1 - z)` after the term
`z ^ n / n` is at most `4 ‖z‖ ^ (n + 1) / (n + 1)`. -/
private theorem norm_neg_log_one_sub_add_logTaylor_le (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) :
    ‖-log (1 - z) + logTaylor (n + 1) (-z)‖ ≤ 4 * ‖z‖ ^ (n + 1) / (n + 1) := by
  rw [← log_inv _ (slitPlane_arg_ne_pi (one_sub_mem_slitPlane (by linarith)))]
  refine (norm_log_one_sub_inv_add_logTaylor_neg_le n (by linarith)).trans ?_
  have h4 : (1 - ‖z‖)⁻¹ ≤ 4 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  rw [mul_comm 4]
  gcongr

/-- For `‖z‖ ≤ 3 / 4`, `‖-log (1 - z) - z‖ ≤ 2 ‖z‖ ^ 2`. -/
theorem norm_neg_log_one_sub_sub_le {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) :
    ‖-log (1 - z) - z‖ ≤ 2 * ‖z‖ ^ 2 := by
  have h := norm_neg_log_one_sub_add_logTaylor_le 1 hz
  simp [logTaylor_succ, logTaylor_zero, ← sub_eq_add_neg] at h
  linarith

/-- For `‖z‖ ≤ 3 / 4`, `‖-log (1 - z) - z - z ^ 2 / 2‖ ≤ 2 ‖z‖ ^ 3`. -/
theorem norm_neg_log_one_sub_sub_sub_le {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) :
    ‖-log (1 - z) - z - z ^ 2 / 2‖ ≤ 2 * ‖z‖ ^ 3 := by
  have h := norm_neg_log_one_sub_add_logTaylor_le 2 hz
  have e : -log (1 - z) + logTaylor (2 + 1) (-z) = -log (1 - z) - z - z ^ 2 / 2 := by
    simp [logTaylor_succ, logTaylor_zero]
    ring
  rw [e] at h
  linarith [pow_nonneg (norm_nonneg z) 3]

end LogTaylor

/-- The prime part `∑ₖ χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)` of the logarithm of the Euler product of
`L(s, χ₄)`; absolutely convergent for `1 < re s`. -/
noncomputable def primePart (s : ℂ) : ℂ := ∑' k : ℕ, primeTerm k s

/-- The prime power part `∑ₖ (-log (1 - χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)) - χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s))` of the
logarithm of the Euler product of `L(s, χ₄)`, that is, the terms `χ₄ p ^ m · p ^ (-m s) / m` with
`m ≥ 2`; absolutely convergent for `1 / 2 < re s`. -/
noncomputable def primePowerPart (s : ℂ) : ℂ :=
  ∑' k : ℕ, (-log (1 - primeTerm k s) - primeTerm k s)

/-- For `1 / 2 < σ₀ ≤ re s`, the `k`-th term of `primePowerPart s` has norm at most
`2 pₖ₊₂ ^ (-2 σ₀)`. -/
theorem norm_primePowerPart_term_le (k : ℕ) {σ₀ : ℝ} {s : ℂ} (hσ₀ : 1 / 2 < σ₀) (hs : σ₀ ≤ s.re) :
    ‖-log (1 - primeTerm k s) - primeTerm k s‖ ≤ 2 * (oddPrime k : ℝ) ^ (-(2 * σ₀)) := by
  refine (norm_neg_log_one_sub_sub_le (norm_primeTerm_le k (by linarith))).trans ?_
  rw [norm_primeTerm, ← Real.rpow_mul_natCast (by positivity)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (Nat.one_le_cast.2 (oddPrime_pos k)) (by push_cast; linarith)) zero_le_two

/-- The series defining `primePart s` converges for `1 < re s`. -/
theorem summable_primePart {s : ℂ} (hs : 1 < s.re) : Summable fun k : ℕ ↦ primeTerm k s :=
  summable_mul_cpow_neg (C := 1) (fun k ↦ (norm_chi4_oddPrime k).le)
    (oddPrime_pos 0) oddPrime_strictMono hs

/-- The series defining `primePowerPart s` converges absolutely for `1 / 2 < re s`. -/
theorem summable_primePowerPart {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun k : ℕ ↦ -log (1 - primeTerm k s) - primeTerm k s :=
  .of_norm_bounded ((summable_oddPrime_rpow (by linarith)).mul_left 2)
    fun k ↦ norm_primePowerPart_term_le k hs le_rfl

/-- **Euler product** for `L(s, χ₄)` in exponential form, `1 < re s`. -/
theorem exp_primePart_add_primePowerPart {s : ℂ} (hs : 1 < s.re) :
    exp (primePart s + primePowerPart s) = DirichletCharacter.LFunction chi4 s := by
  have hsum : Summable fun p : Nat.Primes ↦ -log (1 - chi4 p * (p : ℂ) ^ (-s)) :=
    ((summable_dirichletSummand chi4 hs).of_norm.comp_injective
      Subtype.val_injective).clog_one_sub.neg
  rw [DirichletCharacter.LFunction_eq_LSeries chi4 hs,
    ← DirichletCharacter.LSeries_eulerProduct_exp_log chi4 hs,
    tsum_primes_eq_add_tsum_oddPrime hsum, primePart, primePowerPart,
    ← (summable_primePart hs).tsum_add (summable_primePowerPart (by linarith))]
  simp [chi4_two, primeTerm]

/-- `primePowerPart` is holomorphic on the half-plane `1 / 2 < re s`. -/
theorem differentiableOn_primePowerPart :
    DifferentiableOn ℂ primePowerPart {s : ℂ | 1 / 2 < s.re} := by
  intro s₀ (hs₀ : 1 / 2 < s₀.re)
  obtain ⟨σ₀, hσ₀, hσ₀s⟩ := exists_between hs₀
  have hU : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const continuous_re
  refine (DifferentiableOn.differentiableAt ?_ (hU.mem_nhds hσ₀s)).differentiableWithinAt
  refine differentiableOn_tsum_of_summable_norm
    ((summable_oddPrime_rpow (r := -(2 * σ₀)) (by linarith)).mul_left 2)
    (fun k s (hs : σ₀ < s.re) ↦ ?_) hU fun k s (hs : σ₀ < s.re) ↦
      norm_primePowerPart_term_le k hσ₀ hs.le
  have hd : DifferentiableAt ℂ (primeTerm k) s := ((differentiableAt_id.neg).const_cpow
    (Or.inl (Nat.cast_ne_zero.2 (oddPrime_pos k).ne'))).const_mul _
  exact (((hd.const_sub 1).clog (one_sub_mem_slitPlane (by
    linarith [norm_primeTerm_le k (s := s) (by linarith)]))).neg.sub hd).differentiableWithinAt

/-- `primePowerPart` is bounded on the closed half-plane `1 ≤ re s`. -/
theorem exists_norm_primePowerPart_le : ∃ M : ℝ, ∀ s : ℂ, 1 ≤ s.re → ‖primePowerPart s‖ ≤ M :=
  ⟨_, fun _ hs ↦ tsum_of_norm_bounded ((summable_oddPrime_rpow (r := -(2 * 1))
    (by norm_num)).mul_left 2).hasSum fun k ↦ norm_primePowerPart_term_le k (by norm_num) hs⟩

/-- For real `σ > 1 / 2`, the real part of `primePowerPart σ` is at least
`∑ₖ pₖ₊₂ ^ (-2σ) / 2` minus a constant, because `χ₄ p ^ 2 = 1`. -/
theorem le_re_primePowerPart {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' k : ℕ, (oddPrime k : ℝ) ^ (-(2 * σ))) / 2 -
      2 * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-3 / 2 : ℝ) ≤ (primePowerPart σ).re := by
  have hs : 1 / 2 < (σ : ℂ).re := by simpa using hσ
  refine hasSum_le (fun k ↦ ?_) (((summable_oddPrime_rpow (by linarith)).hasSum.div_const 2).sub
    ((summable_oddPrime_rpow (by norm_num)).hasSum.mul_left 2))
    (hasSum_re (summable_primePowerPart hs).hasSum)
  have hp : (1 : ℝ) ≤ oddPrime k := Nat.one_le_cast.2 (oddPrime_pos k)
  have hn : ‖primeTerm k σ‖ = (oddPrime k : ℝ) ^ (-σ) := by simp [norm_primeTerm]
  have hw : primeTerm k σ = chi4 (oddPrime k) * (((oddPrime k : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [primeTerm, ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  have h2 : (primeTerm k σ ^ 2 / 2).re = (oddPrime k : ℝ) ^ (-(2 * σ)) / 2 := by
    rw [hw, mul_pow, chi4_oddPrime_sq, one_mul, ← ofReal_pow, ← Real.rpow_mul_natCast
      (by positivity), div_ofNat_re, ofReal_re, Nat.cast_ofNat, mul_comm, mul_neg]
  have h3 : ‖primeTerm k σ‖ ^ 3 ≤ (oddPrime k : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [hn, ← Real.rpow_mul_natCast (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hp (by push_cast; linarith)
  have h := abs_le.1 ((abs_re_le_norm _).trans
    (norm_neg_log_one_sub_sub_sub_le (norm_primeTerm_le k hs)))
  simp only [sub_re] at h ⊢
  linarith

/-- The real part of `primePowerPart σ` tends to `+∞` as `σ → 1 / 2⁺`. -/
theorem tendsto_re_primePowerPart :
    Tendsto (fun σ : ℝ ↦ (primePowerPart σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop := by
  have h2 : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝[>] (1 / 2)) (𝓝[>] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const_mul 2).tendsto' _ _ (by norm_num)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun σ (hσ : 1 / 2 < σ) ↦
        show 1 < 2 * σ by linarith⟩
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _
    (-(2 * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-3 / 2 : ℝ)))
    ((tendsto_tsum_oddPrime_rpow_neg.comp h2).atTop_div_const two_pos))
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 / 2 < σ)
  have := le_re_primePowerPart hσ
  simp only [Function.comp_apply] at this ⊢
  linarith

end RokickiConstant
