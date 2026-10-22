/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import RokickiConstant.Defs

/-!
# Lacunary placement of Rokicki's digits: a Liouville number

Rokicki's constant places the digit `bₖ = [pₖ₊₂ ≡ 3 (mod 4)]` at binary position `k + 1`. Its
transcendence is open. If the same digits are placed at the factorial positions `(k + 1)!`
instead,
$$`\rho_{\mathrm{lac}} = \sum_{k \geq 0} \frac{b_k}{2^{(k+1)!}},`
the result is a Liouville number, hence transcendental (`Real.transcendental_rokickiLacunary`).
What blocks a transcendence proof for `ρ` is the dense placement of the digits, not the digits.

The argument is Liouville's, as in Mathlib's `liouville_liouvilleNumber`, for any `0/1` digit
sequence `d` with infinitely many ones and any base `m ≥ 2`: the partial sum
`∑_{k ≤ n} d k / m ^ k!` is a fraction with denominator `m ^ n!`, and the tail is at most the
tail `LiouvilleNumber.remainder m n < 1 / (m ^ n!) ^ n` of Liouville's constant. The only new
point is that the tail must be *positive*, so that the approximation is not an equality; this is
exactly where infinitely many ones are needed. For Rokicki's digits that is the infinitude of
primes `≡ 3 (mod 4)`, taken here from Mathlib's Dirichlet theorem
(`Nat.forall_exists_prime_gt_and_modEq`); the character-sum results of this project are not
needed, and neither is any information about the *distribution* of the digits.

## Main statements

* `liouville_tsum_div_pow_factorial`: `∑ₖ d k / m ^ k!` is a Liouville number for `0/1` digits
  with infinitely many ones and `m ≥ 2`.
* `liouville_tsum_div_two_pow_factorial`: the case `m = 2`.
* `liouville_tsum_div_pow_succ_factorial`: the shifted placement `∑ₖ d k / m ^ (k + 1)!`, in which
  distinct digits occupy distinct positions.
* `Real.liouville_rokickiLacunary`, `Real.transcendental_rokickiLacunary`: the lacunary Rokicki
  constant is a Liouville number, hence transcendental.

## Tags

Liouville number, transcendental, lacunary series, Rokicki's constant
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Finset

open scoped Nat

section General

variable {m : ℕ} {d : ℕ → ℕ}

/-- A `0/1` digit series at factorial positions converges in every base `m ≥ 2`. -/
theorem summable_div_pow_factorial (hm : 2 ≤ m) (hd : ∀ k, d k ≤ 1) :
    Summable fun k : ℕ ↦ (d k : ℝ) / m ^ k ! := by
  refine .of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_)
    (LiouvilleNumber.summable (m := m) (by exact_mod_cast hm))
  gcongr
  exact_mod_cast hd k

/-- The partial sum `∑_{k ≤ n} d k / m ^ k!` is a fraction with denominator `m ^ n!`. -/
theorem exists_sum_range_div_pow_factorial_eq (hm : 2 ≤ m) (d : ℕ → ℕ) (n : ℕ) :
    ∃ p : ℕ, ∑ k ∈ range (n + 1), (d k : ℝ) / m ^ k ! = p / (m : ℝ) ^ n ! := by
  refine ⟨∑ k ∈ range (n + 1), d k * m ^ (n.factorial - k.factorial), ?_⟩
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sum, sum_div]
  refine sum_congr rfl fun k hk ↦ ?_
  have hkn : k ! ≤ n ! := Nat.factorial_le (Nat.lt_succ_iff.mp (mem_range.mp hk))
  rw [div_eq_div_iff (by positivity) (by positivity)]
  push_cast
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkn]

/-- The tail `∑_{k > n} d k / m ^ k!` of a `0/1` digit series at factorial positions is smaller
than `1 / (m ^ n!) ^ n`. It is dominated by the tail of Liouville's constant. -/
theorem tsum_div_pow_factorial_nat_add_lt (hm : 2 ≤ m) (hd : ∀ k, d k ≤ 1) (n : ℕ) :
    ∑' k : ℕ, (d (k + (n + 1)) : ℝ) / m ^ (k + (n + 1))! < 1 / ((m : ℝ) ^ n !) ^ n := by
  refine lt_of_le_of_lt ?_ (LiouvilleNumber.remainder_lt n (m := (m : ℝ)) (by exact_mod_cast hm))
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  rw [LiouvilleNumber.remainder]
  refine Summable.tsum_le_tsum (fun k ↦ ?_)
    ((summable_nat_add_iff (f := fun k : ℕ ↦ (d k : ℝ) / m ^ k !) (n + 1)).mpr
      (summable_div_pow_factorial hm hd))
    (LiouvilleNumber.remainder_summable hm1 n)
  gcongr
  exact_mod_cast hd _

/-- The tail `∑_{k > n} d k / m ^ k!` is positive when infinitely many digits are `1`. -/
theorem tsum_div_pow_factorial_nat_add_pos (hm : 2 ≤ m) (hd : ∀ k, d k ≤ 1)
    (h : ∃ᶠ k in atTop, d k = 1) (n : ℕ) :
    0 < ∑' k : ℕ, (d (k + (n + 1)) : ℝ) / m ^ (k + (n + 1))! := by
  obtain ⟨k, hk, hk1⟩ := frequently_atTop.mp h (n + 1)
  refine ((summable_nat_add_iff (f := fun k : ℕ ↦ (d k : ℝ) / m ^ k !) (n + 1)).mpr
    (summable_div_pow_factorial hm hd)).tsum_pos
    (fun _ ↦ by positivity) (k - (n + 1)) ?_
  have hm0 : (0 : ℝ) < m := by positivity
  rw [Nat.sub_add_cancel hk, hk1, Nat.cast_one]
  positivity

/-- **Lacunary `0/1` series are Liouville numbers.** If `d k ≤ 1` for all `k`, infinitely many
`d k` equal `1`, and `m ≥ 2`, then `∑ₖ d k / m ^ k!` is a Liouville number. For `d = 1` this is
Mathlib's `liouville_liouvilleNumber`. -/
theorem liouville_tsum_div_pow_factorial (hm : 2 ≤ m) (hd : ∀ k, d k ≤ 1)
    (h : ∃ᶠ k in atTop, d k = 1) : Liouville (∑' k : ℕ, (d k : ℝ) / m ^ k !) := by
  intro n
  obtain ⟨p, hp⟩ := exists_sum_range_div_pow_factorial_eq hm d n
  have hT0 := tsum_div_pow_factorial_nat_add_pos hm hd h n
  have hT1 := tsum_div_pow_factorial_nat_add_lt hm hd n
  refine ⟨p, m ^ n !, by exact_mod_cast Nat.one_lt_pow n.factorial_ne_zero hm, ?_⟩
  push_cast
  rw [← (summable_div_pow_factorial hm hd).sum_add_tsum_nat_add (n + 1), hp]
  simp only [ne_eq, add_sub_cancel_left, abs_of_pos hT0, hT1, and_true]
  intro h0
  linarith

/-- **Lacunary binary `0/1` series are Liouville numbers**: `∑ₖ d k / 2 ^ k!` for `0/1` digits
with infinitely many ones. -/
theorem liouville_tsum_div_two_pow_factorial (hd : ∀ k, d k ≤ 1)
    (h : ∃ᶠ k in atTop, d k = 1) : Liouville (∑' k : ℕ, (d k : ℝ) / 2 ^ k !) := by
  exact_mod_cast liouville_tsum_div_pow_factorial le_rfl hd h

/-- The shifted placement `∑ₖ d k / m ^ (k + 1)!`, in which the digits sit at the distinct
positions `1, 2, 6, 24, …`, is a Liouville number for `0/1` digits with infinitely many ones. -/
theorem liouville_tsum_div_pow_succ_factorial (hm : 2 ≤ m) (hd : ∀ k, d k ≤ 1)
    (h : ∃ᶠ k in atTop, d k = 1) : Liouville (∑' k : ℕ, (d k : ℝ) / m ^ (k + 1)!) := by
  let e : ℕ → ℕ := fun n ↦ if n = 0 then 0 else d (n - 1)
  have he (k : ℕ) : e k ≤ 1 := by
    simp only [e]
    split_ifs
    exacts [zero_le_one, hd _]
  have hfe : ∃ᶠ k in atTop, e k = 1 := by
    rw [frequently_atTop] at h ⊢
    intro N
    obtain ⟨k, hk, hk1⟩ := h N
    exact ⟨k + 1, by omega, by simpa [e] using hk1⟩
  have hl := liouville_tsum_div_pow_factorial hm he hfe
  rw [(summable_div_pow_factorial hm he).tsum_eq_zero_add] at hl
  simpa [e] using hl

/-- Lacunary binary `0/1` series with infinitely many ones are transcendental. -/
theorem transcendental_tsum_div_two_pow_factorial (hd : ∀ k, d k ≤ 1)
    (h : ∃ᶠ k in atTop, d k = 1) : Transcendental ℤ (∑' k : ℕ, (d k : ℝ) / 2 ^ k !) :=
  (liouville_tsum_div_two_pow_factorial hd h).transcendental

end General

namespace Real

/-- Infinitely many digits of Rokicki's constant are `1`: there are infinitely many primes
`≡ 3 (mod 4)`. The proof uses Mathlib's Dirichlet theorem. -/
theorem frequently_rokickiDigit_eq_one : ∃ᶠ k in atTop, rokickiDigit k = 1 := by
  rw [frequently_atTop]
  intro N
  obtain ⟨p, hpN, hp, hp3⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (Nat.nth Nat.Prime (N + 1)) (q := 4) (a := 3)
      (by norm_num) (by norm_num)
  have hj : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  have hlt : N + 1 < Nat.count Nat.Prime p := by
    rw [← Nat.nth_lt_nth Nat.infinite_setOfPred_prime, hj]
    exact hpN
  refine ⟨Nat.count Nat.Prime p - 1, by omega, ?_⟩
  rw [rokickiDigit_eq_one_iff, Nat.sub_add_cancel (by omega), hj]
  exact hp3

/-- The **lacunary Rokicki constant** `∑ₖ rokickiDigit k / 2 ^ (k + 1)!`: Rokicki's digit
`[pₖ₊₂ ≡ 3 (mod 4)]` is placed at binary position `(k + 1)!` instead of `k + 1`, all other
binary digits being `0`. Its binary expansion begins `0.100001`, followed by zeros up to
position `24`. -/
noncomputable def rokickiLacunary : ℝ := ∑' k : ℕ, (rokickiDigit k : ℝ) / 2 ^ (k + 1)!

/-- **The lacunary Rokicki constant is a Liouville number.** -/
theorem liouville_rokickiLacunary : Liouville rokickiLacunary := by
  have h := liouville_tsum_div_pow_succ_factorial le_rfl rokickiDigit_le_one
    frequently_rokickiDigit_eq_one
  unfold rokickiLacunary
  exact_mod_cast h

/-- **The lacunary Rokicki constant is transcendental**, by Liouville's theorem. -/
theorem transcendental_rokickiLacunary : Transcendental ℤ rokickiLacunary :=
  liouville_rokickiLacunary.transcendental

/-- The lacunary Rokicki constant is irrational. -/
theorem irrational_rokickiLacunary : Irrational rokickiLacunary :=
  liouville_rokickiLacunary.irrational

end Real
