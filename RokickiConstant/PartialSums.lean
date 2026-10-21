/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
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

/-- The partial sums of an eventually periodic integer sequence are `c · n + O(1)`, where `c`
is the average of the sequence over one period. -/
theorem exists_abs_sum_sub_mul_le {a : ℕ → ℤ} {p : ℕ} (hp : 0 < p) (ha : EventuallyPeriodic a p) :
    ∃ c : ℚ, ∃ C : ℝ, ∀ n, |(∑ k ∈ range n, (a k : ℝ)) - c * n| ≤ C := by
  sorry

end Function.EventuallyPeriodic

section SummationByParts

/-- **Summation by parts bound.** If the partial sums of `e` are bounded by `C` and `f` is
nonnegative and antitone, then every partial sum of `∑ₖ e k * f k` is bounded by `2 C f 0`. -/
theorem abs_sum_range_mul_le_of_abs_sum_le {e f : ℕ → ℝ} {C : ℝ}
    (he : ∀ n, |∑ k ∈ range n, e k| ≤ C) (hf₀ : ∀ k, 0 ≤ f k) (hf : Antitone f) (n : ℕ) :
    |∑ k ∈ range n, e k * f k| ≤ 2 * C * f 0 := by
  sorry

/-- **Summation by parts bound** for the sum of a convergent series. -/
theorem abs_tsum_mul_le_of_abs_sum_le {e f : ℕ → ℝ} {C : ℝ}
    (he : ∀ n, |∑ k ∈ range n, e k| ≤ C) (hf₀ : ∀ k, 0 ≤ f k) (hf : Antitone f)
    (hs : Summable fun k ↦ e k * f k) : |∑' k, e k * f k| ≤ 2 * C * f 0 := by
  sorry

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

/-- The key estimate `‖q ^ (-s) - q' ^ (-s)‖ ≤ ‖s‖ / re s · (q ^ (-re s) - q' ^ (-re s))` for
`0 < q ≤ q'` and `0 < re s`. -/
theorem norm_cpow_neg_sub_cpow_neg_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {s : ℂ}
    (hs : 0 < s.re) :
    ‖(m : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ ‖s‖ / s.re * ((m : ℝ) ^ (-s.re) - (n : ℝ) ^ (-s.re)) := by
  sorry

theorem summable_abelSeries {C : ℝ} (ha : ∀ n, ‖∑ j ∈ range n, a j‖ ≤ C) (hq₀ : 0 < q 0)
    (hq : StrictMono q) {s : ℂ} (hs : 0 < s.re) :
    Summable fun k : ℕ ↦
      (∑ j ∈ range (k + 1), a j) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s)) := by
  sorry

theorem differentiableOn_abelSeries {C : ℝ} (ha : ∀ n, ‖∑ j ∈ range n, a j‖ ≤ C) (hq₀ : 0 < q 0)
    (hq : StrictMono q) : DifferentiableOn ℂ (abelSeries a q) {s : ℂ | 0 < s.re} := by
  sorry

/-- A Dirichlet series `∑ₖ a k · q k ^ (-s)` with bounded coefficients over a strictly increasing
sequence of positive integers converges absolutely for `1 < re s`. -/
theorem summable_mul_cpow_neg {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C) (hq₀ : 0 < q 0) (hq : StrictMono q)
    {s : ℂ} (hs : 1 < s.re) : Summable fun k : ℕ ↦ a k * (q k : ℂ) ^ (-s) := by
  sorry

/-- For `1 < re s` the Abel series agrees with the Dirichlet series it came from. -/
theorem abelSeries_eq_tsum {C : ℝ} (ha : ∀ n, ‖∑ j ∈ range n, a j‖ ≤ C) (hq₀ : 0 < q 0)
    (hq : StrictMono q) {s : ℂ} (hs : 1 < s.re) :
    abelSeries a q s = ∑' k : ℕ, a k * (q k : ℂ) ^ (-s) := by
  sorry

end AbelSeries
