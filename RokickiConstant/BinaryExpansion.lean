/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Rational numbers have eventually periodic binary expansions

We prove that if `d : ℕ → ℕ` is a sequence of binary digits (`d k ≤ 1`) whose value
`∑ₖ d k / 2 ^ (k + 1)` is rational, then `d` is eventually periodic. Contrapositively, a binary
digit sequence that is not eventually periodic defines an irrational number.

The proof avoids the usual discussion of non-unique binary expansions. Writing
`T n = ∑ₖ d (n + k) / 2 ^ (k + 1) ∈ [0, 1]` for the tails, rationality of the value forces the
tails to take only finitely many values, so `T i = T j` for some `i < j`. Since
`T (n + 1) = 2 T n - d n`, two tails that agree and continue with different digits force
`T i = 1 / 2` and then one continuation to be `1` and the other `0`, which is absurd because a
tail equal to `1` means all later digits are `1`. Hence `d i = d j`, and inductively
`d (i + k) = d (j + k)` for all `k`.

## Main definitions

* `Function.EventuallyPeriodic f p`: `f (n + p) = f n` for all sufficiently large `n`.
* `binaryTail d n`: the tail `∑ₖ d (n + k) / 2 ^ (k + 1)` of a binary expansion.

## Main statements

* `eventuallyPeriodic_of_tsum_div_two_pow_mem_range_ratCast`: a binary digit sequence with
  rational value is eventually periodic.
* `irrational_tsum_div_two_pow`: a binary digit sequence that is not eventually periodic (with
  any positive period) has irrational value.

## Tags

binary expansion, eventually periodic, irrational
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology

namespace Function

/-- A function `f : ℕ → α` is *eventually periodic* with period `p` if `f (n + p) = f n` for all
sufficiently large `n`. Compare `Function.Periodic`, which demands this for all `n`. -/
def EventuallyPeriodic {α : Type*} (f : ℕ → α) (p : ℕ) : Prop :=
  ∀ᶠ n in atTop, f (n + p) = f n

theorem Periodic.eventuallyPeriodic {α : Type*} {f : ℕ → α} {p : ℕ} (h : Periodic f p) :
    EventuallyPeriodic f p := by
  sorry

theorem EventuallyPeriodic.comp {α β : Type*} {f : ℕ → α} {p : ℕ} (h : EventuallyPeriodic f p)
    (g : α → β) : EventuallyPeriodic (g ∘ f) p := by
  sorry

/-- An eventually periodic function with period `p` agrees with its shift by `p` from some
index `N` on. -/
theorem EventuallyPeriodic.exists_forall_le {α : Type*} {f : ℕ → α} {p : ℕ}
    (h : EventuallyPeriodic f p) : ∃ N, ∀ n, N ≤ n → f (n + p) = f n := by
  sorry

end Function

section BinaryTail

variable (d : ℕ → ℕ)

/-- The tail `∑ₖ d (n + k) / 2 ^ (k + 1)` of the binary expansion with digits `d`. -/
noncomputable def binaryTail (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1)

variable {d}

theorem summable_binaryTail (hd : ∀ k, d k ≤ 1) (n : ℕ) :
    Summable fun k : ℕ ↦ (d (n + k) : ℝ) / 2 ^ (k + 1) := by
  sorry

theorem binaryTail_zero : binaryTail d 0 = ∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1) := by
  sorry

theorem binaryTail_succ (hd : ∀ k, d k ≤ 1) (n : ℕ) :
    binaryTail d (n + 1) = 2 * binaryTail d n - d n := by
  sorry

theorem binaryTail_mem_Icc (hd : ∀ k, d k ≤ 1) (n : ℕ) : binaryTail d n ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

theorem binaryTail_eq_one_iff (hd : ∀ k, d k ≤ 1) {n : ℕ} :
    binaryTail d n = 1 ↔ ∀ k, d (n + k) = 1 := by
  sorry

theorem binaryTail_eq_zero_iff (hd : ∀ k, d k ≤ 1) {n : ℕ} :
    binaryTail d n = 0 ↔ ∀ k, d (n + k) = 0 := by
  sorry

/-- Two tails starting at different positions that are equal must start with the same digit. -/
theorem apply_eq_of_binaryTail_eq (hd : ∀ k, d k ≤ 1) {i j : ℕ} (hij : i < j)
    (h : binaryTail d i = binaryTail d j) : d i = d j := by
  sorry

/-- Two tails starting at different positions that are equal stay equal when shifted. -/
theorem binaryTail_succ_eq_of_binaryTail_eq (hd : ∀ k, d k ≤ 1) {i j : ℕ} (hij : i < j)
    (h : binaryTail d i = binaryTail d j) : binaryTail d (i + 1) = binaryTail d (j + 1) := by
  sorry

/-- `2 ^ n · x - T n` is the integer with binary digits `d 0, …, d (n - 1)`. -/
theorem two_pow_mul_tsum_sub_binaryTail (hd : ∀ k, d k ≤ 1) (n : ℕ) :
    2 ^ n * (∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1)) - binaryTail d n =
      ∑ k ∈ Finset.range n, (d k : ℝ) * 2 ^ (n - 1 - k) := by
  sorry

/-- If the value of a binary expansion is rational, its tails take only finitely many values. -/
theorem finite_range_binaryTail (hd : ∀ k, d k ≤ 1)
    (hq : (∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1)) ∈ Set.range ((↑) : ℚ → ℝ)) :
    (Set.range (binaryTail d)).Finite := by
  sorry

end BinaryTail

/-- A binary digit sequence whose value is rational is eventually periodic. -/
theorem eventuallyPeriodic_of_tsum_div_two_pow_mem_range_ratCast {d : ℕ → ℕ} (hd : ∀ k, d k ≤ 1)
    (hq : (∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1)) ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ p, 0 < p ∧ Function.EventuallyPeriodic d p := by
  sorry

/-- A binary digit sequence that is not eventually periodic has irrational value. -/
theorem irrational_tsum_div_two_pow {d : ℕ → ℕ} (hd : ∀ k, d k ≤ 1)
    (h : ∀ p, 0 < p → ¬ Function.EventuallyPeriodic d p) :
    Irrational (∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1)) := by
  sorry
