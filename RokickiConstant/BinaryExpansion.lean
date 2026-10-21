/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational

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

open Filter

namespace Function

/-- A function `f : ℕ → α` is *eventually periodic* with period `p` if `f (n + p) = f n` for all
sufficiently large `n`. Compare `Function.Periodic`, which demands this for all `n`. -/
def EventuallyPeriodic {α : Type*} (f : ℕ → α) (p : ℕ) : Prop :=
  ∀ᶠ n in atTop, f (n + p) = f n

/-- An eventually periodic function with period `p` agrees with its shift by `p` from some
index `N` on. -/
theorem EventuallyPeriodic.exists_forall_le {α : Type*} {f : ℕ → α} {p : ℕ}
    (h : EventuallyPeriodic f p) : ∃ N, ∀ n, N ≤ n → f (n + p) = f n :=
  eventually_atTop.mp h

end Function

section BinaryTail

variable (d : ℕ → ℕ)

/-- The tail `∑ₖ d (n + k) / 2 ^ (k + 1)` of the binary expansion with digits `d`. -/
noncomputable def binaryTail (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1)

variable {d}

/-- Each term `d n / 2 ^ (k + 1)` of a binary expansion is at most the term `1 / 2 / 2 ^ k` of
the geometric series `hasSum_geometric_two' 1`. -/
private theorem div_two_pow_le (hd : ∀ k, d k ≤ 1) (n k : ℕ) :
    (d n : ℝ) / 2 ^ (k + 1) ≤ 1 / 2 / 2 ^ k := by
  rw [div_div, ← pow_succ']
  gcongr
  exact_mod_cast hd n

/-- The series defining `binaryTail d n` converges. -/
theorem summable_binaryTail (hd : ∀ k, d k ≤ 1) (n : ℕ) :
    Summable fun k : ℕ ↦ (d (n + k) : ℝ) / 2 ^ (k + 1) :=
  .of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ div_two_pow_le hd (n + k) k)
    (hasSum_geometric_two' 1).summable

/-- The tail at `0` is the value of the whole binary expansion. -/
theorem binaryTail_zero : binaryTail d 0 = ∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1) := by
  simp only [binaryTail, zero_add]

/-- Shifting a binary expansion by one digit: `T (n + 1) = 2 T n - d n`. -/
theorem binaryTail_succ (hd : ∀ k, d k ≤ 1) (n : ℕ) :
    binaryTail d (n + 1) = 2 * binaryTail d n - d n := by
  have h : binaryTail d n = d n / 2 + binaryTail d (n + 1) / 2 := by
    simp only [binaryTail]
    rw [(summable_binaryTail hd n).tsum_eq_zero_add, ← tsum_div_const]
    congr 1
    · simp
    · refine tsum_congr fun k ↦ ?_
      rw [show n + (k + 1) = n + 1 + k by omega]
      ring
  linarith

/-- Every tail of a binary expansion lies in `[0, 1]`. -/
theorem binaryTail_mem_Icc (hd : ∀ k, d k ≤ 1) (n : ℕ) : binaryTail d n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨tsum_nonneg fun _ ↦ by positivity, ((summable_binaryTail hd n).tsum_le_tsum
    (fun k ↦ div_two_pow_le hd (n + k) k) (hasSum_geometric_two' 1).summable).trans_eq
    (tsum_geometric_two' 1)⟩

/-- A tail equals `1` if and only if all of its digits are `1`. -/
theorem binaryTail_eq_one_iff (hd : ∀ k, d k ≤ 1) {n : ℕ} :
    binaryTail d n = 1 ↔ ∀ k, d (n + k) = 1 := by
  refine ⟨fun h k ↦ ?_, fun h ↦ ?_⟩
  · by_contra hk
    have h0 : d (n + k) = 0 := by have := hd (n + k); omega
    refine h.not_lt (((summable_binaryTail hd n).tsum_lt_tsum (fun k ↦ div_two_pow_le hd (n + k) k)
      (i := k) ?_ (hasSum_geometric_two' 1).summable).trans_eq (tsum_geometric_two' 1))
    rw [h0, Nat.cast_zero, zero_div]
    positivity
  · simpa only [binaryTail, h, Nat.cast_one, pow_succ', div_div] using tsum_geometric_two' 1

/-- A tail equals `0` if and only if all of its digits are `0`. -/
theorem binaryTail_eq_zero_iff (hd : ∀ k, d k ≤ 1) {n : ℕ} :
    binaryTail d n = 0 ↔ ∀ k, d (n + k) = 0 := by
  refine ⟨fun h k ↦ ?_, fun h ↦ by simp [binaryTail, h]⟩
  by_contra hk
  have h1 : d (n + k) = 1 := by have := hd (n + k); omega
  refine h.not_gt ((summable_binaryTail hd n).tsum_pos (fun _ ↦ by positivity) k ?_)
  rw [h1, Nat.cast_one]
  positivity

/-- Two tails starting at different positions that are equal must start with the same digit. -/
theorem apply_eq_of_binaryTail_eq (hd : ∀ k, d k ≤ 1) {i j : ℕ} (hij : i < j)
    (h : binaryTail d i = binaryTail d j) : d i = d j := by
  have hi := binaryTail_succ hd i
  have hj := binaryTail_succ hd j
  rw [← h] at hj
  have hi' := binaryTail_mem_Icc hd (i + 1)
  have hj' := binaryTail_mem_Icc hd (j + 1)
  have hk : i + 1 + (j - i) = j + 1 := by omega
  by_contra hne
  rcases (by have := hd i; have := hd j; omega : d i = 0 ∧ d j = 1 ∨ d i = 1 ∧ d j = 0) with
    ⟨h0, h1⟩ | ⟨h1, h0⟩
  · rw [h0, Nat.cast_zero] at hi
    rw [h1, Nat.cast_one] at hj
    have e1 := (binaryTail_eq_one_iff hd (n := i + 1)).mp (by linarith [hi'.2, hj'.1]) (j - i)
    have e0 := (binaryTail_eq_zero_iff hd (n := j + 1)).mp (by linarith [hi'.2, hj'.1]) 0
    rw [hk] at e1
    rw [add_zero, e1] at e0
    exact one_ne_zero e0
  · rw [h1, Nat.cast_one] at hi
    rw [h0, Nat.cast_zero] at hj
    have e1 := (binaryTail_eq_one_iff hd (n := j + 1)).mp (by linarith [hi'.1, hj'.2]) 0
    have e0 := (binaryTail_eq_zero_iff hd (n := i + 1)).mp (by linarith [hi'.1, hj'.2]) (j - i)
    rw [hk] at e0
    rw [add_zero, e0] at e1
    exact zero_ne_one e1

/-- Two tails starting at different positions that are equal stay equal when shifted. -/
theorem binaryTail_succ_eq_of_binaryTail_eq (hd : ∀ k, d k ≤ 1) {i j : ℕ} (hij : i < j)
    (h : binaryTail d i = binaryTail d j) : binaryTail d (i + 1) = binaryTail d (j + 1) := by
  rw [binaryTail_succ hd, binaryTail_succ hd, h, apply_eq_of_binaryTail_eq hd hij h]

/-- `2 ^ n · x - T n` is the integer with binary digits `d 0, …, d (n - 1)`. -/
theorem two_pow_mul_tsum_sub_binaryTail (hd : ∀ k, d k ≤ 1) (n : ℕ) :
    2 ^ n * (∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1)) - binaryTail d n =
      ∑ k ∈ Finset.range n, (d k : ℝ) * 2 ^ (n - 1 - k) := by
  induction n with
  | zero => simp [binaryTail_zero]
  | succ n ih =>
    rw [binaryTail_succ hd, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    have : ∑ k ∈ Finset.range n, (d k : ℝ) * 2 ^ (n - k) =
        2 * ∑ k ∈ Finset.range n, (d k : ℝ) * 2 ^ (n - 1 - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      rw [show n - k = n - 1 - k + 1 by omega, pow_succ]
      ring
    rw [this, ← ih, pow_succ]
    ring

/-- If the value of a binary expansion is rational, its tails take only finitely many values. -/
theorem finite_range_binaryTail (hd : ∀ k, d k ≤ 1)
    (hq : (∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1)) ∈ Set.range ((↑) : ℚ → ℝ)) :
    (Set.range (binaryTail d)).Finite := by
  obtain ⟨q, hq⟩ := hq
  refine (Set.finite_range fun m : Fin (q.den + 1) ↦ (m : ℝ) / q.den).subset ?_
  rintro _ ⟨n, rfl⟩
  have hD : (0 : ℝ) < q.den := by positivity
  have hT := binaryTail_mem_Icc hd n
  have hqD : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (q.den : ℝ) * binaryTail d n = z := by
    refine ⟨2 ^ n * q.num - q.den * ∑ k ∈ Finset.range n, (d k : ℤ) * 2 ^ (n - 1 - k), ?_⟩
    push_cast
    rw [← two_pow_mul_tsum_sub_binaryTail hd n, ← hq, ← hqD]
    ring
  have hz0 : (0 : ℝ) ≤ z := hz ▸ mul_nonneg hD.le hT.1
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by exact_mod_cast hz0)
  push_cast at hz
  have hm : (m : ℝ) ≤ q.den := hz ▸ mul_le_of_le_one_right hD.le hT.2
  refine ⟨⟨m, by exact_mod_cast Nat.lt_succ_of_le (by exact_mod_cast hm)⟩, ?_⟩
  change (m : ℝ) / q.den = _
  rw [div_eq_iff hD.ne', ← hz, mul_comm]

end BinaryTail

/-- A binary digit sequence whose value is rational is eventually periodic. -/
theorem eventuallyPeriodic_of_tsum_div_two_pow_mem_range_ratCast {d : ℕ → ℕ} (hd : ∀ k, d k ≤ 1)
    (hq : (∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1)) ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ p, 0 < p ∧ Function.EventuallyPeriodic d p := by
  obtain ⟨i, j, hij, h⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem (f := binaryTail d)
    Set.mem_range_self (finite_range_binaryTail hd hq)
  have key (k : ℕ) : binaryTail d (i + k) = binaryTail d (j + k) := by
    induction k with
    | zero => exact h
    | succ k ih =>
      exact binaryTail_succ_eq_of_binaryTail_eq hd (i := i + k) (j := j + k) (by omega) ih
  refine ⟨j - i, by omega, eventually_atTop.mpr ⟨i, fun n hn ↦ ?_⟩⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show i + k + (j - i) = j + k by omega]
  exact (apply_eq_of_binaryTail_eq hd (by omega) (key k)).symm

/-- A binary digit sequence that is not eventually periodic has irrational value. -/
theorem irrational_tsum_div_two_pow {d : ℕ → ℕ} (hd : ∀ k, d k ≤ 1)
    (h : ∀ p, 0 < p → ¬ Function.EventuallyPeriodic d p) :
    Irrational (∑' k : ℕ, (d k : ℝ) / 2 ^ (k + 1)) := fun hq ↦ by
  obtain ⟨p, hp, hper⟩ := eventuallyPeriodic_of_tsum_div_two_pow_mem_range_ratCast hd hq
  exact h p hp hper
