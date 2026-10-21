/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import RokickiConstant.BinaryExpansion

/-!
# Rational numbers have eventually periodic expansions in every base

This is the base-`b` version of `RokickiConstant.BinaryExpansion`: if `d : ℕ → ℕ` is a digit
sequence with `d k < b` whose value `∑ₖ d k / b ^ (k + 1)` is rational, then `d` is eventually
periodic. The proof is the same tail argument. Writing `T n = ∑ₖ d (n + k) / b ^ (k + 1)`, the
tails satisfy `T (n + 1) = b · T n - d n` and lie in `[0, 1]`; rationality forces them to take
finitely many values, so two tails agree, and two equal tails must start with the same digit:
otherwise the difference of the next tails would be a nonzero integer in `[-1, 1]`, forcing one
of them to be `1` (all later digits `b - 1`) and the other `0` (all later digits `0`), which is
absurd.

## Main statements

* `eventuallyPeriodic_of_tsum_div_pow_mem_range_ratCast`: a base-`b` digit sequence with
  rational value is eventually periodic.
* `irrational_tsum_div_pow`: a base-`b` digit sequence that is not eventually periodic has
  irrational value.

## Tags

base b expansion, eventually periodic, irrational
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology

section Tail

variable (b : ℕ) (d : ℕ → ℕ)

/-- The tail `∑ₖ d (n + k) / b ^ (k + 1)` of the base-`b` expansion with digits `d`. -/
noncomputable def expansionTail (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / b ^ (k + 1)

variable {b d}

/-- The tail series converges for digits `d k < b`. -/
theorem summable_expansionTail (hb : 2 ≤ b) (hd : ∀ k, d k < b) (n : ℕ) :
    Summable fun k : ℕ ↦ (d (n + k) : ℝ) / b ^ (k + 1) := by
  sorry

/-- The tail at position `0` is the value of the expansion. -/
theorem expansionTail_zero : expansionTail b d 0 = ∑' k : ℕ, (d k : ℝ) / b ^ (k + 1) := by
  sorry

/-- The tail recursion `T (n + 1) = b · T n - d n`. -/
theorem expansionTail_succ (hb : 2 ≤ b) (hd : ∀ k, d k < b) (n : ℕ) :
    expansionTail b d (n + 1) = b * expansionTail b d n - d n := by
  sorry

/-- Tails lie in `[0, 1]`. -/
theorem expansionTail_mem_Icc (hb : 2 ≤ b) (hd : ∀ k, d k < b) (n : ℕ) :
    expansionTail b d n ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- A tail equals `1` exactly when all later digits are `b - 1`. -/
theorem expansionTail_eq_one_iff (hb : 2 ≤ b) (hd : ∀ k, d k < b) {n : ℕ} :
    expansionTail b d n = 1 ↔ ∀ k, d (n + k) = b - 1 := by
  sorry

/-- A tail equals `0` exactly when all later digits are `0`. -/
theorem expansionTail_eq_zero_iff (hb : 2 ≤ b) (hd : ∀ k, d k < b) {n : ℕ} :
    expansionTail b d n = 0 ↔ ∀ k, d (n + k) = 0 := by
  sorry

/-- Two equal tails starting at different positions start with the same digit. -/
theorem apply_eq_of_expansionTail_eq (hb : 2 ≤ b) (hd : ∀ k, d k < b) {i j : ℕ} (hij : i < j)
    (h : expansionTail b d i = expansionTail b d j) : d i = d j := by
  sorry

/-- Two equal tails starting at different positions stay equal when shifted. -/
theorem expansionTail_succ_eq_of_expansionTail_eq (hb : 2 ≤ b) (hd : ∀ k, d k < b) {i j : ℕ}
    (hij : i < j) (h : expansionTail b d i = expansionTail b d j) :
    expansionTail b d (i + 1) = expansionTail b d (j + 1) := by
  sorry

/-- `b ^ n · x - T n` is the integer with base-`b` digits `d 0, …, d (n - 1)`. -/
theorem pow_mul_tsum_sub_expansionTail (hb : 2 ≤ b) (hd : ∀ k, d k < b) (n : ℕ) :
    b ^ n * (∑' k : ℕ, (d k : ℝ) / b ^ (k + 1)) - expansionTail b d n =
      ∑ k ∈ Finset.range n, (d k : ℝ) * b ^ (n - 1 - k) := by
  sorry

/-- If the value of the expansion is rational, the tails take only finitely many values. -/
theorem finite_range_expansionTail (hb : 2 ≤ b) (hd : ∀ k, d k < b)
    (hq : (∑' k : ℕ, (d k : ℝ) / b ^ (k + 1)) ∈ Set.range ((↑) : ℚ → ℝ)) :
    (Set.range (expansionTail b d)).Finite := by
  sorry

end Tail

/-- A base-`b` digit sequence whose value is rational is eventually periodic. -/
theorem eventuallyPeriodic_of_tsum_div_pow_mem_range_ratCast {b : ℕ} {d : ℕ → ℕ} (hb : 2 ≤ b)
    (hd : ∀ k, d k < b) (hq : (∑' k : ℕ, (d k : ℝ) / b ^ (k + 1)) ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ p, 0 < p ∧ Function.EventuallyPeriodic d p := by
  sorry

/-- A base-`b` digit sequence that is not eventually periodic has irrational value. -/
theorem irrational_tsum_div_pow {b : ℕ} {d : ℕ → ℕ} (hb : 2 ≤ b) (hd : ∀ k, d k < b)
    (h : ∀ p, 0 < p → ¬ Function.EventuallyPeriodic d p) :
    Irrational (∑' k : ℕ, (d k : ℝ) / b ^ (k + 1)) := by
  sorry
