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

/-- The geometric series `∑ₖ (b - 1) / b ^ (k + 1)` sums to `1`. -/
private theorem hasSum_sub_one_div_pow (hb : 2 ≤ b) :
    HasSum (fun k : ℕ ↦ ((b : ℝ) - 1) / b ^ (k + 1)) 1 := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb0 : (0 : ℝ) < b := by linarith
  have h := (hasSum_geometric_of_lt_one (r := 1 / (b : ℝ)) (by positivity)
    ((div_lt_one hb0).mpr hb1)).mul_left (((b : ℝ) - 1) / b)
  have hb1' : (b : ℝ) - 1 ≠ 0 := by linarith
  convert h using 1
  · ext k
    rw [one_div_pow, pow_succ]
    field_simp
  · field_simp

/-- Each term `d n / b ^ (k + 1)` is at most the term `(b - 1) / b ^ (k + 1)` of the geometric
series `hasSum_sub_one_div_pow`. -/
private theorem div_pow_le (hd : ∀ k, d k < b) (n k : ℕ) :
    (d n : ℝ) / b ^ (k + 1) ≤ ((b : ℝ) - 1) / b ^ (k + 1) := by
  have : (d n : ℝ) + 1 ≤ b := by exact_mod_cast Nat.succ_le_of_lt (hd n)
  gcongr
  linarith

/-- The tail series converges for digits `d k < b`. -/
theorem summable_expansionTail (hb : 2 ≤ b) (hd : ∀ k, d k < b) (n : ℕ) :
    Summable fun k : ℕ ↦ (d (n + k) : ℝ) / b ^ (k + 1) :=
  .of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ div_pow_le hd (n + k) k)
    (hasSum_sub_one_div_pow hb).summable

/-- The tail at position `0` is the value of the expansion. -/
theorem expansionTail_zero : expansionTail b d 0 = ∑' k : ℕ, (d k : ℝ) / b ^ (k + 1) := by
  simp only [expansionTail, zero_add]

/-- The tail recursion `T (n + 1) = b · T n - d n`. -/
theorem expansionTail_succ (hb : 2 ≤ b) (hd : ∀ k, d k < b) (n : ℕ) :
    expansionTail b d (n + 1) = b * expansionTail b d n - d n := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have h : expansionTail b d n = d n / b + expansionTail b d (n + 1) / b := by
    simp only [expansionTail]
    rw [(summable_expansionTail hb hd n).tsum_eq_zero_add, ← tsum_div_const]
    congr 1
    · simp
    · refine tsum_congr fun k ↦ ?_
      rw [show n + (k + 1) = n + 1 + k by omega, pow_succ _ (k + 1)]
      field_simp
  rw [h]
  field_simp
  ring

/-- Tails lie in `[0, 1]`. -/
theorem expansionTail_mem_Icc (hb : 2 ≤ b) (hd : ∀ k, d k < b) (n : ℕ) :
    expansionTail b d n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨tsum_nonneg fun _ ↦ by positivity, ((summable_expansionTail hb hd n).tsum_le_tsum
    (fun k ↦ div_pow_le hd (n + k) k) (hasSum_sub_one_div_pow hb).summable).trans_eq
    (hasSum_sub_one_div_pow hb).tsum_eq⟩

/-- A tail equals `1` exactly when all later digits are `b - 1`. -/
theorem expansionTail_eq_one_iff (hb : 2 ≤ b) (hd : ∀ k, d k < b) {n : ℕ} :
    expansionTail b d n = 1 ↔ ∀ k, d (n + k) = b - 1 := by
  refine ⟨fun h k ↦ ?_, fun h ↦ ?_⟩
  · by_contra hk
    have hlt : (d (n + k) : ℝ) + 1 < b := by
      exact_mod_cast (show d (n + k) + 1 < b by have := hd (n + k); omega)
    refine h.not_lt (((summable_expansionTail hb hd n).tsum_lt_tsum
      (fun k ↦ div_pow_le hd (n + k) k) (i := k) ?_
      (hasSum_sub_one_div_pow hb).summable).trans_eq (hasSum_sub_one_div_pow hb).tsum_eq)
    gcongr
    linarith
  · have hb1 : ((b - 1 : ℕ) : ℝ) = b - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    simpa only [expansionTail, h, hb1] using (hasSum_sub_one_div_pow hb).tsum_eq

/-- A tail equals `0` exactly when all later digits are `0`. -/
theorem expansionTail_eq_zero_iff (hb : 2 ≤ b) (hd : ∀ k, d k < b) {n : ℕ} :
    expansionTail b d n = 0 ↔ ∀ k, d (n + k) = 0 := by
  refine ⟨fun h k ↦ ?_, fun h ↦ by simp [expansionTail, h]⟩
  by_contra hk
  refine h.not_gt ((summable_expansionTail hb hd n).tsum_pos (fun _ ↦ by positivity) k ?_)
  have : (0 : ℝ) < d (n + k) := by exact_mod_cast Nat.pos_of_ne_zero hk
  positivity

/-- Two equal tails starting at different positions start with the same digit. -/
theorem apply_eq_of_expansionTail_eq (hb : 2 ≤ b) (hd : ∀ k, d k < b) {i j : ℕ} (hij : i < j)
    (h : expansionTail b d i = expansionTail b d j) : d i = d j := by
  have hi := expansionTail_succ hb hd i
  have hj := expansionTail_succ hb hd j
  rw [← h] at hj
  have hi' := expansionTail_mem_Icc hb hd (i + 1)
  have hj' := expansionTail_mem_Icc hb hd (j + 1)
  have hk : i + 1 + (j - i) = j + 1 := by omega
  rcases lt_trichotomy (d i) (d j) with hlt | heq | hlt
  · have hc : (d i : ℝ) + 1 ≤ d j := by exact_mod_cast hlt
    have e1 := (expansionTail_eq_one_iff hb hd (n := i + 1)).mp (by linarith [hi'.2, hj'.1])
      (j - i)
    have e0 := (expansionTail_eq_zero_iff hb hd (n := j + 1)).mp (by linarith [hi'.2, hj'.1]) 0
    rw [hk] at e1
    rw [add_zero, e1] at e0
    omega
  · exact heq
  · have hc : (d j : ℝ) + 1 ≤ d i := by exact_mod_cast hlt
    have e1 := (expansionTail_eq_one_iff hb hd (n := j + 1)).mp (by linarith [hi'.1, hj'.2]) 0
    have e0 := (expansionTail_eq_zero_iff hb hd (n := i + 1)).mp (by linarith [hi'.1, hj'.2])
      (j - i)
    rw [hk] at e0
    rw [add_zero, e0] at e1
    omega

/-- Two equal tails starting at different positions stay equal when shifted. -/
theorem expansionTail_succ_eq_of_expansionTail_eq (hb : 2 ≤ b) (hd : ∀ k, d k < b) {i j : ℕ}
    (hij : i < j) (h : expansionTail b d i = expansionTail b d j) :
    expansionTail b d (i + 1) = expansionTail b d (j + 1) := by
  rw [expansionTail_succ hb hd, expansionTail_succ hb hd, h,
    apply_eq_of_expansionTail_eq hb hd hij h]

/-- `b ^ n · x - T n` is the integer with base-`b` digits `d 0, …, d (n - 1)`. -/
theorem pow_mul_tsum_sub_expansionTail (hb : 2 ≤ b) (hd : ∀ k, d k < b) (n : ℕ) :
    b ^ n * (∑' k : ℕ, (d k : ℝ) / b ^ (k + 1)) - expansionTail b d n =
      ∑ k ∈ Finset.range n, (d k : ℝ) * b ^ (n - 1 - k) := by
  induction n with
  | zero => simp [expansionTail_zero]
  | succ n ih =>
    rw [expansionTail_succ hb hd, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    have : ∑ k ∈ Finset.range n, (d k : ℝ) * b ^ (n - k) =
        b * ∑ k ∈ Finset.range n, (d k : ℝ) * b ^ (n - 1 - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      rw [show n - k = n - 1 - k + 1 by omega, pow_succ]
      ring
    rw [this, ← ih, pow_succ]
    ring

/-- If the value of the expansion is rational, the tails take only finitely many values. -/
theorem finite_range_expansionTail (hb : 2 ≤ b) (hd : ∀ k, d k < b)
    (hq : (∑' k : ℕ, (d k : ℝ) / b ^ (k + 1)) ∈ Set.range ((↑) : ℚ → ℝ)) :
    (Set.range (expansionTail b d)).Finite := by
  obtain ⟨q, hq⟩ := hq
  refine (Set.finite_range fun m : Fin (q.den + 1) ↦ (m : ℝ) / q.den).subset ?_
  rintro _ ⟨n, rfl⟩
  have hD : (0 : ℝ) < q.den := by positivity
  have hT := expansionTail_mem_Icc hb hd n
  have hqD : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (q.den : ℝ) * expansionTail b d n = z := by
    refine ⟨b ^ n * q.num - q.den * ∑ k ∈ Finset.range n, (d k : ℤ) * b ^ (n - 1 - k), ?_⟩
    push_cast
    rw [← pow_mul_tsum_sub_expansionTail hb hd n, ← hq, ← hqD]
    ring
  have hz0 : (0 : ℝ) ≤ z := hz ▸ mul_nonneg hD.le hT.1
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by exact_mod_cast hz0)
  push_cast at hz
  have hm : (m : ℝ) ≤ q.den := hz ▸ mul_le_of_le_one_right hD.le hT.2
  refine ⟨⟨m, by exact_mod_cast Nat.lt_succ_of_le (by exact_mod_cast hm)⟩, ?_⟩
  change (m : ℝ) / q.den = _
  rw [div_eq_iff hD.ne', ← hz, mul_comm]

end Tail

/-- A base-`b` digit sequence whose value is rational is eventually periodic. -/
theorem eventuallyPeriodic_of_tsum_div_pow_mem_range_ratCast {b : ℕ} {d : ℕ → ℕ} (hb : 2 ≤ b)
    (hd : ∀ k, d k < b) (hq : (∑' k : ℕ, (d k : ℝ) / b ^ (k + 1)) ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ p, 0 < p ∧ Function.EventuallyPeriodic d p := by
  obtain ⟨i, j, hij, h⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem (f := expansionTail b d)
    Set.mem_range_self (finite_range_expansionTail hb hd hq)
  have key (k : ℕ) : expansionTail b d (i + k) = expansionTail b d (j + k) := by
    induction k with
    | zero => exact h
    | succ k ih =>
      exact expansionTail_succ_eq_of_expansionTail_eq hb hd (i := i + k) (j := j + k)
        (by omega) ih
  refine ⟨j - i, by omega, eventually_atTop.mpr ⟨i, fun n hn ↦ ?_⟩⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show i + k + (j - i) = j + k by omega]
  exact (apply_eq_of_expansionTail_eq hb hd (by omega) (key k)).symm

/-- A base-`b` digit sequence that is not eventually periodic has irrational value. -/
theorem irrational_tsum_div_pow {b : ℕ} {d : ℕ → ℕ} (hb : 2 ≤ b) (hd : ∀ k, d k < b)
    (h : ∀ p, 0 < p → ¬ Function.EventuallyPeriodic d p) :
    Irrational (∑' k : ℕ, (d k : ℝ) / b ^ (k + 1)) := fun hq ↦ by
  obtain ⟨p, hp, hper⟩ := eventuallyPeriodic_of_tsum_div_pow_mem_range_ratCast hb hd hq
  exact h p hp hper
