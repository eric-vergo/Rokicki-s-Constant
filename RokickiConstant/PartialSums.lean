/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import RokickiConstant.BinaryExpansion

/-!
# Partial sums of eventually periodic sequences and summation by parts

This file collects the elementary real-variable input to the irrationality of Rokicki's constant.

* An eventually periodic sequence `a : ℕ → ℤ` has partial sums `∑_{k < n} a k = c · n + O(1)`,
  where `c` is the average of `a` over a period.
* **Summation by parts.** If `e : ℕ → ℝ` has bounded partial sums and `f : ℕ → ℝ` is nonnegative
  and antitone, then `|∑ₖ e k · f k| ≤ 2 C · f 0` (whenever the series converges).
* **Abel series.** For `a : ℕ → ℂ` with bounded partial sums `S k = ∑_{j ≤ k} a j` and a strictly
  increasing sequence `q : ℕ → ℕ` of positive integers, the series
  `∑ₖ S k · (q k ^ (-s) - q (k + 1) ^ (-s))` converges absolutely for `0 < re s`, defines a
  holomorphic function there, and agrees with `∑ₖ a k · q k ^ (-s)` for `1 < re s`.
  This is the analytic continuation of a Dirichlet series over primes with bounded coefficient
  sums to the half-plane `0 < re s`.

## Main definitions

* `abelSeries a q s`: the series `∑ₖ (∑_{j ≤ k} a j) · (q k ^ (-s) - q (k + 1) ^ (-s))`.

## Main statements

* `Function.EventuallyPeriodic.exists_abs_sum_sub_mul_le`: partial sums of an eventually
  periodic integer sequence are `c · n + O(1)`.
* `abs_tsum_mul_le_of_abs_sum_le`: the summation by parts bound.
* `differentiableOn_abelSeries`: `abelSeries a q` is holomorphic on `0 < re s`.
* `abelSeries_eq_tsum`: `abelSeries a q s = ∑ₖ a k · q k ^ (-s)` for `1 < re s`.

## Tags

summation by parts, Abel summation, eventually periodic, Dirichlet series
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset

namespace Function.EventuallyPeriodic

/-- A real sequence that is eventually periodic with positive period is bounded. -/
theorem exists_forall_abs_le {f : ℕ → ℝ} {p : ℕ} (hp : 0 < p) (h : EventuallyPeriodic f p) :
    ∃ C, ∀ n, |f n| ≤ C := by
  obtain ⟨N, hN⟩ := h.exists_forall_le
  refine ⟨∑ k ∈ range (N + p), |f k|, fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N + p
    · exact single_le_sum (fun k _ ↦ abs_nonneg (f k)) (mem_range.2 hn)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + p := ⟨n - p, by omega⟩
      rw [hN m (by omega)]
      exact ih m (by omega)

/-- The partial sums of an eventually periodic integer sequence are `c · n + O(1)`, where `c`
is the average of the sequence over one period. -/
theorem exists_abs_sum_sub_mul_le {a : ℕ → ℤ} {p : ℕ} (hp : 0 < p) (ha : EventuallyPeriodic a p) :
    ∃ c : ℚ, ∃ C : ℝ, ∀ n, |(∑ k ∈ range n, (a k : ℝ)) - c * n| ≤ C := by
  obtain ⟨N, hN⟩ := ha.exists_forall_le
  have hblock : ∀ n, N ≤ n → ∑ k ∈ range (n + p), (a k : ℝ) - ∑ k ∈ range n, (a k : ℝ) =
      ∑ k ∈ range (N + p), (a k : ℝ) - ∑ k ∈ range N, (a k : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih, Nat.add_right_comm n 1 p, sum_range_succ, sum_range_succ, hN n hn]
      ring
  set c : ℚ := ((∑ k ∈ range (N + p), a k - ∑ k ∈ range N, a k : ℤ) : ℚ) / p with hc
  have hp' : (p : ℝ) ≠ 0 := by positivity
  have hcp : (c : ℝ) * p = ∑ k ∈ range (N + p), (a k : ℝ) - ∑ k ∈ range N, (a k : ℝ) := by
    rw [hc]
    push_cast
    field_simp
  have hper : EventuallyPeriodic (fun n ↦ ∑ k ∈ range n, (a k : ℝ) - c * n) p := by
    refine eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    have := hblock n hn
    push_cast
    linear_combination this - hcp
  exact ⟨c, hper.exists_forall_abs_le hp⟩

end Function.EventuallyPeriodic

section SummationByParts

/-- **Summation by parts**: `∑ k ∈ range (n + 1), a k * w k` equals the boundary term
`(∑ j ∈ range (n + 1), a j) * w n` plus the sum
`∑ k ∈ range n, (∑ j ∈ range (k + 1), a j) * (w k - w (k + 1))`. -/
theorem sum_range_succ_mul_eq_sum_mul_sub {R : Type*} [CommRing R] (a w : ℕ → R) (n : ℕ) :
    ∑ k ∈ range (n + 1), a k * w k = (∑ j ∈ range (n + 1), a j) * w n +
      ∑ k ∈ range n, (∑ j ∈ range (k + 1), a j) * (w k - w (k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ (fun k ↦ a k * w k), ih,
      sum_range_succ (fun k ↦ (∑ j ∈ range (k + 1), a j) * (w k - w (k + 1))) n,
      sum_range_succ a (n + 1)]
    ring

/-- **Summation by parts bound.** If the partial sums of `e` are bounded by `C` and `f` is
nonnegative and antitone, then every partial sum of `∑ₖ e k * f k` is bounded by `2 C f 0`. -/
theorem abs_sum_range_mul_le_of_abs_sum_le {e f : ℕ → ℝ} {C : ℝ}
    (he : ∀ n, |∑ k ∈ range n, e k| ≤ C) (hf₀ : ∀ k, 0 ≤ f k) (hf : Antitone f) (n : ℕ) :
    |∑ k ∈ range n, e k * f k| ≤ 2 * C * f 0 := by
  have hC : 0 ≤ C := by simpa using he 0
  rcases n with _ | n
  · simpa using mul_nonneg (mul_nonneg zero_le_two hC) (hf₀ 0)
  rw [sum_range_succ_mul_eq_sum_mul_sub]
  have hd : ∀ k, 0 ≤ f k - f (k + 1) := fun k ↦ sub_nonneg.2 (hf k.le_succ)
  calc _ ≤ |(∑ j ∈ range (n + 1), e j) * f n| +
        |∑ k ∈ range n, (∑ j ∈ range (k + 1), e j) * (f k - f (k + 1))| := abs_add_le _ _
    _ ≤ C * f n + ∑ k ∈ range n, C * (f k - f (k + 1)) := by
      gcongr
      · rw [abs_mul, abs_of_nonneg (hf₀ n)]
        exact mul_le_mul_of_nonneg_right (he _) (hf₀ n)
      · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ ?_)
        rw [abs_mul, abs_of_nonneg (hd k)]
        exact mul_le_mul_of_nonneg_right (he _) (hd k)
    _ = C * f 0 := by rw [← mul_sum, sum_range_sub']; ring
    _ ≤ 2 * C * f 0 := by nlinarith [mul_nonneg hC (hf₀ 0)]

/-- **Summation by parts bound** for the sum of a convergent series. -/
theorem abs_tsum_mul_le_of_abs_sum_le {e f : ℕ → ℝ} {C : ℝ}
    (he : ∀ n, |∑ k ∈ range n, e k| ≤ C) (hf₀ : ∀ k, 0 ≤ f k) (hf : Antitone f)
    (hs : Summable fun k ↦ e k * f k) : |∑' k, e k * f k| ≤ 2 * C * f 0 :=
  le_of_tendsto' hs.hasSum.tendsto_sum_nat.abs fun n ↦
    abs_sum_range_mul_le_of_abs_sum_le he hf₀ hf n

end SummationByParts

section AbelSeries

variable (a : ℕ → ℂ) (q : ℕ → ℕ)

/-- The **Abel series** `∑ₖ (∑_{j ≤ k} a j) · (q k ^ (-s) - q (k + 1) ^ (-s))` obtained from the
Dirichlet series `∑ₖ a k · q k ^ (-s)` by summation by parts. When the partial sums of `a` are
bounded and `q` is strictly increasing, it converges absolutely for `0 < re s` and continues the
Dirichlet series analytically from `1 < re s`. -/
noncomputable def abelSeries (s : ℂ) : ℂ :=
  ∑' k : ℕ, (∑ j ∈ range (k + 1), a j) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s))

variable {a q}

/-- A variant of `norm_cpow_neg_sub_cpow_neg_le` for real bases `1 ≤ x ≤ y`, with any exponent
`0 < δ ≤ re s` on the right-hand side. -/
theorem norm_ofReal_cpow_neg_sub_cpow_neg_le {x y δ : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) {s : ℂ}
    (hδ : 0 < δ) (hδs : δ ≤ s.re) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤ ‖s‖ / δ * (x ^ (-δ) - y ^ (-δ)) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc x y := by
    rw [Set.uIcc_of_le hxy]
    exact fun h ↦ by linarith [h.1]
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hδs; linarith
  have hint : ∫ t in x..y, (t : ℂ) ^ (-s - 1) = ((y : ℂ) ^ (-s) - (x : ℂ) ^ (-s)) / (-s) := by
    rw [integral_cpow (Or.inr ⟨fun h ↦ hs0 (by linear_combination -h), h0⟩), sub_add_cancel]
  have hint' : ∫ t in x..y, t ^ (-δ - 1) = (y ^ (-δ) - x ^ (-δ)) / (-δ) := by
    rw [integral_rpow (Or.inr ⟨(by linarith : -δ - 1 < -1).ne, h0⟩), sub_add_cancel]
  have heq : (x : ℂ) ^ (-s) - (y : ℂ) ^ (-s) = s * ∫ t in x..y, (t : ℂ) ^ (-s - 1) := by
    rw [hint]
    field_simp
    ring
  have hle : ‖∫ t in x..y, (t : ℂ) ^ (-s - 1)‖ ≤ ∫ t in x..y, t ^ (-δ - 1) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hxy
      (Filter.Eventually.of_forall fun t ht ↦ ?_)
      (intervalIntegral.intervalIntegrable_rpow (Or.inr h0))
    have ht1 : 1 ≤ t := hx.trans ht.1.le
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le ht1
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [heq, norm_mul]
  calc ‖s‖ * ‖∫ t in x..y, (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * ∫ t in x..y, t ^ (-δ - 1) := by gcongr
    _ = _ := by
      rw [hint']
      field_simp
      ring

/-- The key estimate `‖q ^ (-s) - q' ^ (-s)‖ ≤ ‖s‖ / re s · (q ^ (-re s) - q' ^ (-re s))` for
`0 < q ≤ q'` and `0 < re s`. -/
theorem norm_cpow_neg_sub_cpow_neg_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {s : ℂ}
    (hs : 0 < s.re) :
    ‖(m : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ ‖s‖ / s.re * ((m : ℝ) ^ (-s.re) - (n : ℝ) ^ (-s.re)) := by
  have h := norm_ofReal_cpow_neg_sub_cpow_neg_le (Nat.one_le_cast.2 hm) (Nat.cast_le.2 hmn) hs
    le_rfl
  simpa only [Complex.ofReal_natCast] using h

/-- For a strictly increasing sequence `q` of positive integers and `0 ≤ δ`, the sequence
`q k ^ (-δ)` is antitone. -/
theorem antitone_natCast_rpow_neg (hq₀ : 0 < q 0) (hq : StrictMono q) {δ : ℝ} (hδ : 0 ≤ δ) :
    Antitone fun k ↦ (q k : ℝ) ^ (-δ) := fun _ _ hkl ↦
  Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hq₀.trans_le (hq.monotone (Nat.zero_le _)))
    (by exact_mod_cast hq.monotone hkl) (by linarith)

/-- The telescoping series of a nonnegative antitone sequence is summable. -/
theorem summable_sub_of_antitone {u : ℕ → ℝ} (hu : Antitone u) (h0 : ∀ k, 0 ≤ u k) :
    Summable fun k ↦ u k - u (k + 1) :=
  summable_of_sum_range_le (c := u 0) (fun k ↦ sub_nonneg.2 (hu k.le_succ)) fun n ↦ by
    rw [sum_range_sub']
    linarith [h0 n]

/-- Termwise bound for the Abel series, with any exponent `0 < δ ≤ re s`. -/
theorem norm_abelSeries_term_le {C : ℝ} (ha : ∀ n, ‖∑ j ∈ range n, a j‖ ≤ C) (hq₀ : 0 < q 0)
    (hq : StrictMono q) {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδs : δ ≤ s.re) (k : ℕ) :
    ‖(∑ j ∈ range (k + 1), a j) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s))‖ ≤
      C * (‖s‖ / δ) * ((q k : ℝ) ^ (-δ) - (q (k + 1) : ℝ) ^ (-δ)) := by
  have hqk : (1 : ℝ) ≤ q k := Nat.one_le_cast.2 (hq₀.trans_le (hq.monotone (Nat.zero_le k)))
  have h := norm_ofReal_cpow_neg_sub_cpow_neg_le hqk (Nat.cast_le.2 (hq.monotone k.le_succ)) hδ hδs
  simp only [Complex.ofReal_natCast] at h
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (ha _) h (norm_nonneg _) ((norm_nonneg _).trans (ha 0))

theorem summable_abelSeries {C : ℝ} (ha : ∀ n, ‖∑ j ∈ range n, a j‖ ≤ C) (hq₀ : 0 < q 0)
    (hq : StrictMono q) {s : ℂ} (hs : 0 < s.re) :
    Summable fun k : ℕ ↦
      (∑ j ∈ range (k + 1), a j) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s)) :=
  Summable.of_norm_bounded ((summable_sub_of_antitone (antitone_natCast_rpow_neg hq₀ hq hs.le)
    fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).mul_left (C * (‖s‖ / s.re)))
    fun k ↦ norm_abelSeries_term_le ha hq₀ hq hs le_rfl k

theorem differentiableOn_abelSeries {C : ℝ} (ha : ∀ n, ‖∑ j ∈ range n, a j‖ ≤ C) (hq₀ : 0 < q 0)
    (hq : StrictMono q) : DifferentiableOn ℂ (abelSeries a q) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  have hδ : 0 < s₀.re / 2 := by linarith
  set U : Set ℂ := {s | s₀.re / 2 < s.re} ∩ Metric.ball 0 (‖s₀‖ + 1)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := ⟨show s₀.re / 2 < s₀.re by linarith, by simp⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (ha 0)
  have hne : ∀ k, (q k : ℂ) ≠ 0 := fun k ↦
    Nat.cast_ne_zero.2 (hq₀.trans_le (hq.monotone (Nat.zero_le k))).ne'
  have hd : DifferentiableOn ℂ (fun s ↦ ∑' k : ℕ,
      (∑ j ∈ range (k + 1), a j) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s))) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_sub_of_antitone (antitone_natCast_rpow_neg hq₀ hq hδ.le)
        fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).mul_left
        (C * ((‖s₀‖ + 1) / (s₀.re / 2)))) (fun k ↦ ?_) hU fun k s hs ↦ ?_
    · exact (((differentiable_neg.const_cpow (Or.inl (hne k))).sub
        (differentiable_neg.const_cpow (Or.inl (hne (k + 1))))).const_mul _).differentiableOn
    · refine (norm_abelSeries_term_le ha hq₀ hq hδ hs.1.le k).trans ?_
      have hs' : ‖s‖ < ‖s₀‖ + 1 := by simpa using hs.2
      have hk : 0 ≤ (q k : ℝ) ^ (-(s₀.re / 2)) - (q (k + 1) : ℝ) ^ (-(s₀.re / 2)) :=
        sub_nonneg.2 (antitone_natCast_rpow_neg hq₀ hq hδ.le k.le_succ)
      gcongr
  exact (hd.differentiableAt (hU.mem_nhds hs₀U)).differentiableWithinAt

/-- A Dirichlet series `∑ₖ a k · q k ^ (-s)` with bounded coefficients over a strictly increasing
sequence of positive integers converges absolutely for `1 < re s`. -/
theorem summable_mul_cpow_neg {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C) (hq₀ : 0 < q 0) (hq : StrictMono q)
    {s : ℂ} (hs : 1 < s.re) : Summable fun k : ℕ ↦ a k * (q k : ℂ) ^ (-s) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (ha 0)
  have hqk : ∀ k, k + 1 ≤ q k := fun k ↦ by
    induction k with
    | zero => omega
    | succ k ih =>
      have : q k < q (k + 1) := hq (by omega)
      omega
  have hsum : Summable fun k : ℕ ↦ C * ((k + 1 : ℕ) : ℝ) ^ (-s.re) :=
    ((summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ (-s.re)) 1).2
      (Real.summable_nat_rpow.2 (by linarith))).mul_left C
  refine Summable.of_norm_bounded hsum fun k ↦ ?_
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by have := hqk k; omega), Complex.neg_re]
  exact mul_le_mul (ha k) (Real.rpow_le_rpow_of_nonpos (by positivity)
    (by exact_mod_cast hqk k) (by linarith)) (by positivity) hC

/-- For `1 < re s` the Abel series agrees with the Dirichlet series it came from. -/
theorem abelSeries_eq_tsum {C : ℝ} (ha : ∀ n, ‖∑ j ∈ range n, a j‖ ≤ C) (hq₀ : 0 < q 0)
    (hq : StrictMono q) {s : ℂ} (hs : 1 < s.re) :
    abelSeries a q s = ∑' k : ℕ, a k * (q k : ℂ) ^ (-s) := by
  have hσ : 0 < s.re := by linarith
  have ha' : ∀ k, ‖a k‖ ≤ 2 * C := fun k ↦ by
    have : a k = ∑ j ∈ range (k + 1), a j - ∑ j ∈ range k, a j := by
      rw [sum_range_succ]
      ring
    rw [this]
    linarith [norm_sub_le (∑ j ∈ range (k + 1), a j) (∑ j ∈ range k, a j), ha (k + 1), ha k]
  have h1 := ((summable_mul_cpow_neg ha' hq₀ hq hs).hasSum.tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have h0 : Tendsto (fun n ↦ (∑ j ∈ range (n + 1), a j) * (q n : ℂ) ^ (-s)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n ↦ C * (q n : ℝ) ^ (-s.re)) (fun n ↦ ?_) ?_
    · have hqn : 0 < q n := hq₀.trans_le (hq.monotone (Nat.zero_le n))
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hqn, Complex.neg_re]
      exact mul_le_mul_of_nonneg_right (ha _) (by positivity)
    · simpa using ((tendsto_rpow_neg_atTop hσ).comp
        (tendsto_natCast_atTop_atTop.comp hq.tendsto_atTop)).const_mul C
  have h2 := h0.add (summable_abelSeries ha hq₀ hq hσ).hasSum.tendsto_sum_nat
  rw [zero_add] at h2
  refine tendsto_nhds_unique (h2.congr fun n ↦ ?_) h1
  exact (sum_range_succ_mul_eq_sum_mul_sub a (fun k ↦ (q k : ℂ) ^ (-s)) n).symm

end AbelSeries
