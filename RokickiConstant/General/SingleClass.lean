/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import RokickiConstant.General.HigherOrder

/-!
# A single residue class of primes

Let `q ≥ 3`, let `a` be coprime to `q` and let `p₀ = 2 < p₁ < ⋯` be the primes. We prove that the
indicator `k ↦ [pₖ ≡ a (mod q)]` is not eventually periodic, so that
`∑ₖ [pₖ ≡ a (mod q)] / b ^ (k + 1)` is irrational in every base `b ≥ 2`. One indicator does not
determine the values `χ(pₖ)` of any character, so the character-by-character arguments of
`RokickiConstant.General.Irrational` and `RokickiConstant.General.HigherOrder` do not apply; the
proof combines all nonprincipal characters at once. No prime number theorem is used.

Write `φ = φ(q)`, `u` for the unit `a`, and `e(n) = [n = u] - 1(n) / φ` (`classWeight`), where
`1(n)` is the principal character. By orthogonality `φ e(n) = ∑_{χ ≠ 1} χ(u⁻¹) χ(n)`.

1. *Linear sums.* If the indicator were eventually periodic, `∑_{k < n} e(pₖ) = c' n + O(1)`.
   Since `∑ₖ e(pₖ) pₖ ^ (-σ) = φ⁻¹ ∑_{χ ≠ 1} χ(u⁻¹) primePart χ σ` stays bounded as `σ → 1⁺`,
   summation by parts forces `c' = 0`: the partial sums of `e(pₖ)` are bounded.
2. *Continuation.* Then the Abel series `A` of `e(pₖ)` is holomorphic on `re s > 0`, and
   `Φ = φ A + ∑_{χ ≠ 1} χ(u⁻¹) primePowerPart χ` (`classLog`) is holomorphic on `re s > 1 / 2`
   and equals `∑_{χ ≠ 1} χ(u⁻¹) log L(s, χ)` on `re s > 1`. By the identity theorem
   `(∏ L(s, χ)) Φ' = ∑_χ χ(u⁻¹) L'(s, χ) ∏_{ψ ≠ χ} L(s, ψ)` on `re s > 1 / 2`.
3. *The `L` side at `1 / 2`.* With `m_χ` the order of vanishing of `L(·, χ)` at `1 / 2`,
   `Φ(σ) = x log (σ - 1 / 2) + O(1)` as `σ → 1 / 2⁺`, where `x = ∑_{χ ≠ 1} χ(u⁻¹) m_χ`.
4. *The prime-square side at `1 / 2`.* The `p²` terms of the prime-power parts and Dirichlet
   density in the `ν` classes `r` with `r² = u` give
   `Φ(σ) = -((ν - 1) / 2) log (σ - 1 / 2) + O(1)`, using `∑_{p ∤ q} p ^ (-t) = -log (t - 1) + O(1)`
   (the pole of `L(s, 1)`).
5. *Integrality.* Hence `x = (1 - ν) / 2`. But `x` is an algebraic integer (the `χ(u⁻¹)` are roots
   of unity), and `ν` is even for `q ≥ 3` (`r ↦ -r` pairs the square roots of `u`), so `(1 - ν) / 2`
   is a half-integer: contradiction. Zeros of the `L(·, χ)` at `1 / 2` could cancel the
   prime-square singularity only by an algebraic integer.

## Main statements

* `DirichletCharacter.exists_norm_classSeries_sub_primePart_one_le`: Dirichlet density,
  `φ ∑_{p ≡ r} p ^ (-σ) - ∑_{p ∤ q} p ^ (-σ) = O(1)` as `σ → 1⁺`.
* `DirichletCharacter.exists_norm_primePart_one_add_log_le`:
  `∑_{p ∤ q} p ^ (-σ) = log (1 / (σ - 1)) + O(1)`.
* `Complex.exists_norm_sub_mul_log_le_of_prod_mul_deriv_eq`: the logarithmic singularity of a
  combination of logarithmic derivatives at a real point.
* `DirichletCharacter.not_exists_norm_sum_classWeight_le`: the partial sums of `e(pₖ)` are
  unbounded.
* `Nat.not_eventuallyPeriodic_nthPrime_modEq`: **the single-class theorem**.
* `Real.irrational_classConstant`; `Real.classConstant_four_three_two` (Rokicki's constant is
  `2 · classConstant 4 3 2`).

## Tags

Dirichlet character, residue class, orthogonality, order of vanishing, algebraic integer
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

open Classical in
/-- The nonprincipal Dirichlet characters modulo `q`, with values in `ℂ`. -/
noncomputable abbrev nonprincipal (q : ℕ) : Finset (DirichletCharacter ℂ q) := univ.erase 1

omit [NeZero q] in
/-- Membership in `nonprincipal q`. -/
theorem mem_nonprincipal {χ : DirichletCharacter ℂ q} : χ ∈ nonprincipal q ↔ χ ≠ 1 := by
  simp [nonprincipal]

section Orthogonality

/-- **Orthogonality of Dirichlet characters**, in the form used here: for a unit `u` and any
`n`, `∑_χ χ(u⁻¹) χ(n)` is `φ(q)` if `n = u` and `0` otherwise. -/
theorem sum_apply_inv_mul_apply (u : (ZMod q)ˣ) (n : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ ↑u⁻¹ * χ n = if n = u then (q.totient : ℂ) else 0 := by
  rw [← ZMod.inv_coe_unit, sum_char_inv_mul_char_eq ℂ u.isUnit n]
  by_cases h : n = u <;> simp [h, eq_comm]

/-- Orthogonality over the nonprincipal characters:
`∑_{χ ≠ 1} χ(u⁻¹) χ(n) = φ(q) [n = u] - 1(n)`, where `1(n)` is `1` on units and `0` otherwise. -/
theorem sum_nonprincipal_apply_inv_mul_apply (u : (ZMod q)ˣ) (n : ZMod q) :
    ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * χ n =
      (if n = u then (q.totient : ℂ) else 0) - (1 : DirichletCharacter ℂ q) n := by
  classical
  rw [← sum_apply_inv_mul_apply u n, ← add_sum_erase _ _ (mem_univ 1), MulChar.one_apply_coe,
    one_mul, add_sub_cancel_left]

end Orthogonality

section ClassSeries

/-- The Dirichlet series `∑ₖ [pₖ ≡ r (mod q)] pₖ ^ (-σ)` of the primes in the residue class `r`,
for real `σ`. -/
noncomputable def classSeries (r : ZMod q) (σ : ℝ) : ℝ :=
  ∑' k : ℕ, if (nthPrime k : ZMod q) = r then (nthPrime k : ℝ) ^ (-σ) else 0

omit [NeZero q] in
/-- The series defining `classSeries r σ` converges for `σ > 1`. -/
theorem summable_classSeries (r : ZMod q) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun k : ℕ ↦ if (nthPrime k : ZMod q) = r then (nthPrime k : ℝ) ^ (-σ) else 0 :=
  (summable_nthPrime_rpow (by linarith : -σ < -1)).of_nonneg_of_le
    (fun k ↦ by split_ifs <;> positivity) fun k ↦ by split_ifs <;> [exact le_rfl; positivity]

/-- A Dirichlet series over the primes whose coefficients depend only on `pₖ mod q` is a finite
combination of the class series: `∑ₖ F(pₖ) pₖ ^ (-σ) = ∑_r F(r) classSeries r σ` for `σ > 1`. -/
theorem tsum_apply_mul_cpow_eq_sum (F : ZMod q → ℂ) {σ : ℝ} (hσ : 1 < σ) :
    ∑' k : ℕ, F (nthPrime k) * (nthPrime k : ℂ) ^ (-(σ : ℂ)) =
      ∑ r : ZMod q, F r * classSeries r σ := by
  have hterm : ∀ k : ℕ, F (nthPrime k) * (nthPrime k : ℂ) ^ (-(σ : ℂ)) =
      ∑ r : ZMod q, F r *
        ((if (nthPrime k : ZMod q) = r then (nthPrime k : ℝ) ^ (-σ) else 0 : ℝ) : ℂ) := by
    intro k
    rw [Finset.sum_eq_single (nthPrime k : ZMod q) (fun r _ hr ↦ by simp [Ne.symm hr])
      (fun h ↦ absurd (mem_univ _) h), ite_eq_left rfl, ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [tsum_congr hterm, Summable.tsum_finsetSum fun r _ ↦
    (summable_ofReal.2 (summable_classSeries r hσ)).mul_left _]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [tsum_mul_left, classSeries, ofReal_tsum]

/-- `primePart χ σ = ∑_r χ(r) classSeries r σ` for real `σ > 1`. -/
theorem primePart_ofReal_eq_sum (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    χ.primePart σ = ∑ r : ZMod q, χ r * classSeries r σ :=
  tsum_apply_mul_cpow_eq_sum (fun r ↦ χ r) hσ

/-- For real `σ > 1`, `∑_{p ∤ q} p ^ (-σ) = primePart 1 σ` is real. -/
theorem im_primePart_one {σ : ℝ} (hσ : 1 < σ) :
    ((1 : DirichletCharacter ℂ q).primePart σ).im = 0 := by
  rw [primePart_ofReal_eq_sum _ hσ, im_sum]
  refine sum_eq_zero fun r _ ↦ ?_
  by_cases hr : IsUnit r
  · simp [MulChar.one_apply hr]
  · simp [MulChar.map_nonunit _ hr]

/-- For real `σ > 1` and `h : ZMod q → ZMod q`, orthogonality turns the combination
`∑_{χ ≠ 1} χ(u⁻¹) ∑ₖ χ(h(pₖ)) pₖ ^ (-σ)` into `∑_r (φ(q) [h r = u] - 1(h r)) classSeries r σ`. -/
theorem sum_nonprincipal_mul_tsum_eq (u : (ZMod q)ˣ) (h : ZMod q → ZMod q) {σ : ℝ}
    (hσ : 1 < σ) :
    ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * ∑' k : ℕ, χ (h (nthPrime k)) * (nthPrime k : ℂ) ^ (-(σ : ℂ)) =
      ∑ r : ZMod q, ((if h r = u then (q.totient : ℂ) else 0) -
        (1 : DirichletCharacter ℂ q) (h r)) * classSeries r σ := by
  have e : ∀ χ : DirichletCharacter ℂ q,
      ∑' k : ℕ, χ (h (nthPrime k)) * (nthPrime k : ℂ) ^ (-(σ : ℂ)) =
        ∑ r : ZMod q, χ (h r) * classSeries r σ :=
    fun χ ↦ tsum_apply_mul_cpow_eq_sum (fun r ↦ χ (h r)) hσ
  simp_rw [e, mul_sum, ← mul_assoc]
  rw [sum_comm]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [← sum_mul, sum_nonprincipal_apply_inv_mul_apply]

/-- A combination `∑_{χ ≠ 1} c(χ) primePart χ σ` with `‖c(χ)‖ ≤ 1` is bounded on `1 < σ ≤ 2`, by
`exists_norm_primePart_le` for each of the finitely many nonprincipal `χ`. -/
theorem exists_norm_sum_nonprincipal_mul_primePart_le (c : DirichletCharacter ℂ q → ℂ)
    (hc : ∀ χ, ‖c χ‖ ≤ 1) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      ‖∑ χ ∈ nonprincipal q, c χ * χ.primePart σ‖ ≤ M := by
  have hM : ∀ χ ∈ nonprincipal q, ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖χ.primePart σ‖ ≤ M :=
    fun χ hχ ↦ χ.exists_norm_primePart_le (mem_nonprincipal.1 hχ)
  choose! M hM using hM
  refine ⟨∑ χ ∈ nonprincipal q, M χ, fun σ hσ hσ2 ↦ (norm_sum_le _ _).trans
    (sum_le_sum fun χ hχ ↦ ?_)⟩
  rw [norm_mul]
  calc _ ≤ 1 * M χ := mul_le_mul (hc χ) (hM χ hχ σ hσ hσ2) (norm_nonneg _) zero_le_one
    _ = M χ := one_mul _

/-- **Dirichlet density, without the prime number theorem.** For a unit `r` modulo `q`,
`φ(q) ∑_{p ≡ r} p ^ (-σ) - ∑_{p ∤ q} p ^ (-σ)` is bounded on `1 < σ ≤ 2`: by orthogonality it is
`∑_{χ ≠ 1} χ(r⁻¹) primePart χ σ`. -/
theorem exists_norm_classSeries_sub_primePart_one_le {r : ZMod q} (hr : IsUnit r) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      ‖(q.totient : ℂ) * classSeries r σ - (1 : DirichletCharacter ℂ q).primePart σ‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_norm_sum_nonprincipal_mul_primePart_le
    (fun χ ↦ χ ((hr.unit⁻¹ : (ZMod q)ˣ) : ZMod q)) fun χ ↦ χ.norm_le_one _
  refine ⟨M, fun σ hσ hσ2 ↦ ?_⟩
  have e := sum_nonprincipal_mul_tsum_eq hr.unit id hσ
  simp only [id, IsUnit.unit_spec] at e
  have e1 : ∑ r' : ZMod q, ((if r' = r then (q.totient : ℂ) else 0) -
      (1 : DirichletCharacter ℂ q) r') * classSeries r' σ =
      (q.totient : ℂ) * classSeries r σ - (1 : DirichletCharacter ℂ q).primePart σ := by
    rw [primePart_ofReal_eq_sum _ hσ]
    simp [sub_mul, sum_sub_distrib, ite_mul]
  rw [← e1]
  convert hM σ hσ hσ2 using 2
  exact e.symm

/-- **The pole of `L(s, 1)` at `s = 1` in logarithmic form**:
`∑_{p ∤ q} p ^ (-σ) = log (1 / (σ - 1)) + O(1)` as `σ → 1⁺`. Here `exp (primePart 1 σ +
primePowerPart 1 σ) = L(σ, 1)`, the prime-power part is bounded, and `(σ - 1) L(σ, 1)` tends to
`∏_{p ∣ q} (1 - p⁻¹) ≠ 0` (Mathlib's `LFunctionTrivChar_residue_one`). -/
theorem exists_norm_primePart_one_add_log_le :
    ∃ C : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] 1,
      ‖(1 : DirichletCharacter ℂ q).primePart σ + Real.log (σ - 1)‖ ≤ C := by
  set c : ℂ := ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)
  have hc : c ≠ 0 := by
    refine prod_ne_zero_iff.2 fun p hp ↦ sub_ne_zero.2 fun h ↦ ?_
    have h1 : (p : ℂ) = 1 := by rw [← inv_inv (p : ℂ), ← h, inv_one]
    exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (by exact_mod_cast h1)
  have hto : Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_ofReal.tendsto' 1 1 ofReal_one).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun σ (hσ : 1 < σ) ↦ by
        simpa [← ofReal_one, ofReal_inj] using hσ.ne'⟩
  have hlim : Tendsto (fun σ : ℝ ↦
      Real.log ‖((σ : ℂ) - 1) * LFunction (1 : DirichletCharacter ℂ q) σ‖) (𝓝[>] 1)
      (𝓝 (Real.log ‖c‖)) :=
    (Real.continuousAt_log (norm_ne_zero_iff.2 hc)).tendsto.comp
      (LFunctionTrivChar_residue_one.comp hto).norm
  obtain ⟨M, hM⟩ := (1 : DirichletCharacter ℂ q).exists_norm_primePowerPart_le
  refine ⟨|Real.log ‖c‖| + 1 + M, ?_⟩
  filter_upwards [hlim.eventually (Metric.ball_mem_nhds _ one_pos), self_mem_nhdsWithin]
    with σ hσ (hσ1 : 1 < σ)
  have hs : 1 < (σ : ℂ).re := by simpa using hσ1
  have hexp := (1 : DirichletCharacter ℂ q).exp_primePart_add_primePowerPart hs
  have e1 : Real.log ‖((σ : ℂ) - 1) * LFunction (1 : DirichletCharacter ℂ q) σ‖ =
      Real.log (σ - 1) + ((1 : DirichletCharacter ℂ q).primePart σ).re +
        ((1 : DirichletCharacter ℂ q).primePowerPart σ).re := by
    rw [norm_mul, ← hexp, norm_exp, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
      norm_real, Real.norm_of_nonneg (by linarith),
      Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, add_re]
    ring
  have hP := abs_le.1 ((abs_re_le_norm _).trans (hM σ (by simpa using hσ1.le)))
  rw [Real.dist_eq, e1, abs_lt] at hσ
  rw [← abs_re_eq_norm.2 (by simp [im_primePart_one hσ1]), add_re, ofReal_re, abs_le]
  constructor <;> linarith [le_abs_self (Real.log ‖c‖), neg_abs_le (Real.log ‖c‖)]

omit [NeZero q] in
/-- Split of the prime-power part at the squares: for `re s > 1 / 2`,
`primePowerPart χ s = primePart (χ ^ 2) (2 s) / 2 + tailPart χ 3 s`. -/
theorem primePowerPart_eq_primePart_sq_add_tailPart (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    χ.primePowerPart s = (χ ^ 2).primePart (2 * s) / 2 + χ.tailPart 3 s := by
  have h2 : 1 < (2 * s).re := by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have h3 : 1 / ((3 : ℕ) : ℝ) < s.re := by push_cast; linarith
  have hterm : ∀ k, (χ ^ 2).primeTerm k (2 * s) / 2 = χ.primeTerm k s ^ 2 / 2 := by
    intro k
    rw [primeTerm, primeTerm, MulChar.pow_apply' χ two_ne_zero, mul_pow, ← cpow_nat_mul,
      mul_neg]
    push_cast
    rfl
  rw [primePowerPart, primePart, tailPart, ← tsum_div_const, ← Summable.tsum_add
    (((χ ^ 2).summable_primeTerm h2).div_const 2) (χ.summable_tailPart_term (by norm_num) h3)]
  refine tsum_congr fun k ↦ ?_
  rw [hterm, logTail]
  simp [sum_range_succ]
  ring

end ClassSeries

section Algebra

/-- For `q ≥ 3` the number of square roots modulo `q` of a unit `u` is even: `r ↦ -r` permutes
them without fixed points, as `2 r ≠ 0` for a unit `r`. -/
theorem even_card_sq_eq (hq : 3 ≤ q) (u : (ZMod q)ˣ) :
    _root_.Even #{r : ZMod q | r ^ 2 = u} := by
  rw [← ZMod.natCast_eq_zero_iff_even, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine sum_involution (fun r _ ↦ -r) (fun _ _ ↦ by decide) (fun r hr _ h ↦ ?_)
    (fun r hr ↦ by simpa [neg_sq] using hr) (fun r _ ↦ neg_neg r)
  have hr' : r ^ 2 = u := (mem_filter.1 hr).2
  have hu : IsUnit r := (isUnit_pow_iff two_ne_zero).1 (hr' ▸ u.isUnit)
  have h2 : (2 : ZMod q) * r = 0 := by linear_combination -h
  have h2' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast hu.mul_left_eq_zero.1 h2
  have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 q).1 h2')
  omega

omit [NeZero q] in
/-- The value of a Dirichlet character at a unit is a root of unity, hence an algebraic
integer. -/
theorem isIntegral_apply_unit [NeZero q] (χ : DirichletCharacter ℂ q) (v : (ZMod q)ˣ) :
    IsIntegral ℤ (χ v) := by
  have h : χ v ^ Fintype.card (ZMod q)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have hfin : IsOfFinOrder (χ v) := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Fintype.card_pos, h⟩
  exact (IsPrimitiveRoot.orderOf (χ v)).isIntegral hfin.orderOf_pos

end Algebra

end DirichletCharacter

/-- Half an odd integer is not an algebraic integer: a rational algebraic integer is an
integer. -/
theorem Complex.not_isIntegral_intCast_div_two {n : ℤ} (hn : Odd n) :
    ¬ IsIntegral ℤ ((n : ℂ) / 2) := by
  intro h
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ ((n : ℚ) / 2)) := by simpa using h
  rw [isIntegral_algebraMap_iff] at h'
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h'
  have h2 : ((2 * z : ℤ) : ℚ) = n := by
    rw [Int.cast_mul, show ((z : ℤ) : ℚ) = algebraMap ℤ ℚ z from rfl, hz]
    push_cast
    ring
  have h3 : 2 * z = n := by exact_mod_cast h2
  obtain ⟨k, rfl⟩ := hn
  omega

/-- **No linear growth against a bounded Dirichlet series over the primes.** Let `a` be a bounded
real sequence such that `∑ₖ aₖ pₖ ^ (-σ)` is bounded on `1 < σ ≤ 2`. Then the partial sums
`∑_{k < n} aₖ` are not of the form `c n + O(1)` with `c ≠ 0`: summation by parts would give
`∑ₖ aₖ pₖ ^ (-σ) = c ∑ₖ pₖ ^ (-σ) + O(1)`, which is unbounded as `σ → 1⁺`. -/
theorem not_exists_abs_sum_sub_mul_le_of_abs_tsum_le {a : ℕ → ℝ} {B : ℝ} (ha : ∀ k, |a k| ≤ B)
    {M : ℝ} (hM : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → |∑' k, a k * (nthPrime k : ℝ) ^ (-σ)| ≤ M) :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n, |∑ k ∈ range n, a k - c * n| ≤ C := by
  rintro ⟨c, hc, C, h⟩
  have hle : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      |c| * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ) ≤ M + 2 * C := by
    intro σ hσ hσ2
    have hfs : Summable fun k ↦ (nthPrime k : ℝ) ^ (-σ) := summable_nthPrime_rpow (by linarith)
    have has : Summable fun k ↦ a k * (nthPrime k : ℝ) ^ (-σ) :=
      .of_norm_bounded (hfs.mul_left B) fun k ↦ by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (ha k) (by positivity)
    have hs : HasSum (fun k ↦ (a k - c) * (nthPrime k : ℝ) ^ (-σ))
        (∑' k, a k * (nthPrime k : ℝ) ^ (-σ) - c * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ)) := by
      convert has.hasSum.sub (hfs.hasSum.mul_left c) using 1
      funext k
      ring
    have he : ∀ n, |∑ k ∈ range n, (a k - c)| ≤ C := fun n ↦ by
      simpa [sum_sub_distrib, mul_comm] using h n
    have hC : 0 ≤ C := (abs_nonneg _).trans (h 0)
    have hf0 : (nthPrime 0 : ℝ) ^ (-σ) ≤ 1 := by
      rw [Nat.nth_prime_zero_eq_two]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h1 : |∑' k, a k * (nthPrime k : ℝ) ^ (-σ) - c * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ)| ≤
        2 * C := by
      rw [← hs.tsum_eq]
      calc _ ≤ 2 * C * (nthPrime 0 : ℝ) ^ (-σ) :=
            abs_tsum_mul_le_of_abs_sum_le he (fun _ ↦ by positivity)
              (antitone_natCast_rpow_neg (Nat.prime_nth_prime 0).pos nthPrime_strictMono
                (by linarith)) hs.summable
        _ ≤ 2 * C := mul_le_of_le_one_right (by linarith) hf0
    have h2 := hM σ hσ hσ2
    have hT : 0 ≤ ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ) := tsum_nonneg fun _ ↦ by positivity
    rw [abs_le] at h1 h2
    rcases abs_cases c with ⟨hc', -⟩ | ⟨hc', -⟩ <;> rw [hc'] <;> nlinarith
  have hT := (tendsto_tsum_nthPrime_rpow_neg.const_mul_atTop (abs_pos.2 hc)).eventually
    (eventually_gt_atTop (M + 2 * C))
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := (hT.and (Ioc_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num))).exists
  exact absurd (hle σ hσ1 hσ2) (not_le.2 hσ)

/-- If `‖y log (σ - s₀)‖` stays bounded as `σ → s₀⁺`, then `y = 0`. -/
theorem Complex.eq_zero_of_eventually_norm_mul_log_le {y : ℂ} {s₀ C : ℝ}
    (h : ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖y * Real.log (σ - s₀)‖ ≤ C) : y = 0 := by
  by_contra hy
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hsub : Tendsto (fun σ : ℝ ↦ σ - s₀) (𝓝[>] s₀) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_sub_right s₀).tendsto' s₀ 0 (sub_self s₀)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun σ (hσ : s₀ < σ) ↦
        show 0 < σ - s₀ by linarith⟩
  have hlog := (Real.tendsto_log_nhdsGT_zero.comp hsub).eventually
    (eventually_lt_atBot (-(C / ‖y‖)))
  obtain ⟨σ, h1, h2⟩ := (h.and hlog).exists
  rw [norm_mul, norm_real, Real.norm_eq_abs] at h1
  simp only [Function.comp_apply] at h2
  have h3 : C / ‖y‖ < |Real.log (σ - s₀)| := by linarith [neg_le_abs (Real.log (σ - s₀))]
  rw [div_lt_iff₀ hy'] at h3
  linarith [mul_comm ‖y‖ |Real.log (σ - s₀)|]


/-- **Logarithmic derivatives at a real point.** Let `f i`, `i ∈ X`, be analytic at the real
point `s₀` and not identically zero near it, let `c i ∈ ℂ`, and let `Φ` be holomorphic at the
points `σ > s₀` close to `s₀` with `(∏ᵢ f i) Φ' = ∑ᵢ c i f i' ∏_{j ≠ i} f j` there. Then, with
`m i` the order of vanishing of `f i` at `s₀`, `Φ(σ) = (∑ᵢ c i m i) log (σ - s₀) + O(1)` as
`σ → s₀⁺`: near `s₀`, `f i = (s - s₀) ^ (m i) g i` with `g i (s₀) ≠ 0`, so
`Φ' = ∑ᵢ c i f i' / f i = (∑ᵢ c i m i) / (s - s₀) + (bounded)`. -/
theorem Complex.exists_norm_sub_mul_log_le_of_prod_mul_deriv_eq {ι : Type*} [DecidableEq ι]
    (X : Finset ι) (f : ι → ℂ → ℂ) (c : ι → ℂ) {s₀ : ℝ} {Φ : ℂ → ℂ}
    (hf : ∀ i ∈ X, AnalyticAt ℂ (f i) s₀) (hf0 : ∀ i ∈ X, ¬ ∀ᶠ z in 𝓝 (s₀ : ℂ), f i z = 0)
    (hΦ : ∀ᶠ σ : ℝ in 𝓝[>] s₀, DifferentiableAt ℂ Φ σ ∧
      (∏ i ∈ X, f i σ) * deriv Φ σ = ∑ i ∈ X, c i * deriv (f i) σ * ∏ j ∈ X.erase i, f j σ) :
    ∃ m : ι → ℕ, ∃ C : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
      ‖Φ σ - (∑ i ∈ X, c i * m i) * Real.log (σ - s₀)‖ ≤ C := by
  have hfac : ∀ i ∈ X, ∃ m : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g s₀ ∧ g s₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 (s₀ : ℂ), f i z = (z - s₀) ^ m • g z :=
    fun i hi ↦ (hf i hi).exists_eventuallyEq_pow_smul_nonzero_iff.2 (hf0 i hi)
  choose! m g hg hg0 hfg using hfac
  refine ⟨m, ?_⟩
  set x : ℂ := ∑ i ∈ X, c i * m i
  set B : ℂ → ℂ := fun z ↦ ∑ i ∈ X, c i * (deriv (g i) z / g i z)
  have hB : ContinuousAt B s₀ :=
    tendsto_finsetSum X fun i hi ↦ continuousAt_const.mul
      ((hg i hi).deriv.continuousAt.div (hg i hi).continuousAt (hg0 i hi))
  have hloc : ∀ᶠ z in 𝓝 (s₀ : ℂ), ‖B z‖ ≤ ‖B s₀‖ + 1 ∧ ∀ i ∈ X, AnalyticAt ℂ (g i) z ∧
      g i z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, f i w = (w - s₀) ^ m i * g i w := by
    refine (hB.norm.eventually (eventually_le_nhds (lt_add_one _))).and
      ((eventually_all_finset X).2 fun i hi ↦ (hg i hi).eventually_analyticAt.and
        (((hg i hi).continuousAt.eventually_ne (hg0 i hi)).and ?_))
    simpa only [smul_eq_mul] using (hfg i hi).eventually_nhds
  have hreal := (continuous_ofReal.tendsto s₀).eventually hloc
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    ((hreal.filter_mono nhdsWithin_le_nhds).and hΦ)
  have hu' : s₀ < u := hu
  have hderiv : ∀ σ ∈ Set.Ioo s₀ u, deriv Φ σ = x / ((σ : ℂ) - s₀) + B σ := by
    intro σ hσ
    obtain ⟨⟨-, hP⟩, -, hid⟩ := hsub hσ
    have hne : (σ : ℂ) - s₀ ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hσ.1.ne')
    have hfi : ∀ i ∈ X, f i σ ≠ 0 ∧
        deriv (f i) σ = f i σ * (m i / ((σ : ℂ) - s₀) + deriv (g i) σ / g i σ) := by
      intro i hi
      obtain ⟨hga, hg0', hfe⟩ := hP i hi
      have hfσ : f i σ = ((σ : ℂ) - s₀) ^ m i * g i σ := hfe.self_of_nhds
      have hd := (((hasDerivAt_id (σ : ℂ)).sub_const (s₀ : ℂ)).pow (m i)).mul
        hga.differentiableAt.hasDerivAt
      have hd' := (hd.congr_of_eventuallyEq hfe).deriv
      refine ⟨by rw [hfσ]; exact mul_ne_zero (pow_ne_zero _ hne) hg0', ?_⟩
      rw [hd', hfσ]
      simp only [id, Pi.pow_apply, mul_one]
      rcases Nat.eq_zero_or_pos (m i) with h0 | hpos
      · rw [h0]
        field_simp
        simp
      · obtain ⟨k, hk⟩ : ∃ k, m i = k + 1 := ⟨m i - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]
        field_simp
        push_cast
        ring
    have hPr : ∏ i ∈ X, f i σ ≠ 0 := prod_ne_zero_iff.2 fun i hi ↦ (hfi i hi).1
    have hN : ∑ i ∈ X, c i * deriv (f i) σ * ∏ j ∈ X.erase i, f j σ =
        (∏ i ∈ X, f i σ) * (x / ((σ : ℂ) - s₀) + B σ) := by
      simp only [x, B, sum_div, mul_add, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i hi ↦ ?_
      rw [(hfi i hi).2, ← mul_prod_erase X (fun j ↦ f j σ) hi]
      ring
    exact mul_left_cancel₀ hPr (hid.trans hN)
  set F : ℝ → ℂ := fun t ↦ Φ t - x * Real.log (t - s₀)
  have hF : ∀ t ∈ Set.Ioo s₀ u, HasDerivAt F (B t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ ↦ Φ t) (deriv Φ t) t :=
      (hsub ht).2.1.hasDerivAt.comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ ↦ ((Real.log (t - s₀) : ℝ) : ℂ)) ((1 / (t - s₀) : ℝ) : ℂ) t :=
      (((hasDerivAt_id t).sub_const s₀).log (by simp only [id]; linarith [ht.1])).ofReal_comp
    convert h1.sub (h2.const_mul x) using 1
    rw [hderiv t ht]
    push_cast
    ring
  set t₀ : ℝ := (s₀ + u) / 2
  have ht₀ : t₀ ∈ Set.Ioo s₀ u := ⟨by simp only [t₀]; linarith, by simp only [t₀]; linarith⟩
  refine ⟨‖F t₀‖ + (‖B s₀‖ + 1) * (u - s₀), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hu'] with σ hσ
  have hmvt := (convex_Ioo s₀ u).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := F) (f' := fun t ↦ B t) (fun t ht ↦ (hF t ht).hasDerivWithinAt)
    (fun t ht ↦ (hsub ht).1.1) ht₀ hσ
  have hd : ‖σ - t₀‖ ≤ u - s₀ := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2, ht₀.1, ht₀.2]
  change ‖F σ‖ ≤ _
  calc ‖F σ‖ = ‖(F σ - F t₀) + F t₀‖ := by rw [sub_add_cancel]
    _ ≤ ‖F σ - F t₀‖ + ‖F t₀‖ := norm_add_le _ _
    _ ≤ (‖B s₀‖ + 1) * (u - s₀) + ‖F t₀‖ := by
        gcongr
        exact hmvt.trans (mul_le_mul_of_nonneg_left hd (by positivity))
    _ = _ := add_comm _ _

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

section SingleClass

variable (u : (ZMod q)ˣ)

omit [NeZero q] in
/-- `φ(q) ≠ 0`. -/
theorem totient_ne_zero [NeZero q] : (q.totient : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.totient_pos.2 (NeZero.pos q)).ne'

/-- The weight `e(n) = [n = u] - φ(q)⁻¹ 1(n)` of the residue class `u`, centred by its expected
density `1 / φ(q)` among the units. -/
noncomputable def classWeight (n : ZMod q) : ℂ :=
  (if n = u then 1 else 0) - (q.totient : ℂ)⁻¹ * (1 : DirichletCharacter ℂ q) n

/-- **Orthogonality for the weight**: `φ(q) e(n) = ∑_{χ ≠ 1} χ(u⁻¹) χ(n)`. -/
theorem totient_mul_classWeight (n : ZMod q) :
    (q.totient : ℂ) * classWeight u n = ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * χ n := by
  rw [sum_nonprincipal_apply_inv_mul_apply, classWeight, mul_sub, ← mul_assoc,
    mul_inv_cancel₀ totient_ne_zero, one_mul]
  split_ifs <;> simp

/-- The weight is real. -/
theorem ofReal_re_classWeight (n : ZMod q) : ((classWeight u n).re : ℂ) = classWeight u n := by
  refine Complex.ext (by simp) ?_
  by_cases hn : IsUnit n
  · simp only [classWeight, MulChar.one_apply hn, ofReal_im]
    split_ifs <;> simp
  · simp only [classWeight, MulChar.map_nonunit _ hn, ofReal_im]
    split_ifs <;> simp

/-- `‖e(n)‖ ≤ 2`. -/
theorem norm_classWeight_le (n : ZMod q) : ‖classWeight u n‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(if n = (u : ZMod q) then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
  have h2 : ‖(q.totient : ℂ)⁻¹ * (1 : DirichletCharacter ℂ q) n‖ ≤ 1 := by
    rw [norm_mul, norm_inv, norm_natCast]
    calc _ ≤ 1 * 1 := mul_le_mul (inv_le_one_of_one_le₀ (Nat.one_le_cast.2 (Nat.totient_pos.2
          (NeZero.pos q)))) ((1 : DirichletCharacter ℂ q).norm_le_one n) (norm_nonneg _)
          zero_le_one
      _ = 1 := one_mul 1
  linarith

/-- For `re s > 1`, `φ(q) ∑ₖ e(pₖ) pₖ ^ (-s) = ∑_{χ ≠ 1} χ(u⁻¹) primePart χ s`. -/
theorem totient_mul_tsum_classWeight {s : ℂ} (hs : 1 < s.re) :
    (q.totient : ℂ) * ∑' k : ℕ, classWeight u (nthPrime k) * (nthPrime k : ℂ) ^ (-s) =
      ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * χ.primePart s := by
  rw [← tsum_mul_left]
  have e : ∀ k : ℕ, (q.totient : ℂ) * (classWeight u (nthPrime k) * (nthPrime k : ℂ) ^ (-s)) =
      ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * χ.primeTerm k s := by
    intro k
    rw [← mul_assoc, totient_mul_classWeight, sum_mul]
    refine sum_congr rfl fun χ _ ↦ ?_
    rw [primeTerm]
    ring
  rw [tsum_congr e, Summable.tsum_finsetSum fun χ _ ↦ (χ.summable_primeTerm hs).mul_left _]
  refine sum_congr rfl fun χ _ ↦ ?_
  rw [primePart, tsum_mul_left]

/-- The Abel series `A(s)` of `k ↦ e(pₖ)`. When the partial sums `∑_{k < n} e(pₖ)` are bounded,
it is holomorphic on `re s > 0` and equals `∑ₖ e(pₖ) pₖ ^ (-s)` on `re s > 1`. -/
noncomputable def classAbel : ℂ → ℂ := abelSeries (fun k ↦ classWeight u (nthPrime k)) nthPrime

/-- The combination `Φ(s) = φ(q) A(s) + ∑_{χ ≠ 1} χ(u⁻¹) primePowerPart χ s`. On `re s > 1` it is
`∑_{χ ≠ 1} χ(u⁻¹) log L(s, χ)` (`classLog_eq`), with the branch of the logarithm given by the
Euler product; under bounded partial sums it is holomorphic on `re s > 1 / 2`. -/
noncomputable def classLog (s : ℂ) : ℂ :=
  q.totient * classAbel u s + ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * χ.primePowerPart s

variable {u} {C : ℝ} (hC : ∀ n, ‖∑ k ∈ range n, classWeight u (nthPrime k)‖ ≤ C)
include hC

omit [NeZero q] in
/-- Under bounded partial sums, `A` is holomorphic on `re s > 0`. -/
theorem differentiableOn_classAbel : DifferentiableOn ℂ (classAbel u) {s : ℂ | 0 < s.re} :=
  differentiableOn_abelSeries hC (Nat.prime_nth_prime 0).pos nthPrime_strictMono

/-- Under bounded partial sums, `Φ(s) = ∑_{χ ≠ 1} χ(u⁻¹) (primePart χ s + primePowerPart χ s)`
for `re s > 1`. -/
theorem classLog_eq {s : ℂ} (hs : 1 < s.re) :
    classLog u s = ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * (χ.primePart s + χ.primePowerPart s) := by
  rw [classLog, classAbel, abelSeries_eq_tsum hC (Nat.prime_nth_prime 0).pos nthPrime_strictMono
    hs, totient_mul_tsum_classWeight u hs, ← sum_add_distrib]
  simp only [mul_add]

omit [NeZero q] in
/-- Under bounded partial sums, `Φ` is holomorphic on `re s > 1 / 2`. -/
theorem differentiableOn_classLog : DifferentiableOn ℂ (classLog u) {s : ℂ | 1 / 2 < s.re} :=
  (((differentiableOn_classAbel hC).mono fun s (hs : 1 / 2 < s.re) ↦
    show 0 < s.re by linarith).const_mul _).add
    (DifferentiableOn.fun_sum fun χ _ ↦ χ.differentiableOn_primePowerPart.const_mul _)

/-- Under bounded partial sums, `Φ' = ∑_{χ ≠ 1} χ(u⁻¹) L'(s, χ) / L(s, χ)` on `re s > 1`. -/
theorem hasDerivAt_classLog {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (classLog u)
      (∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * (deriv (LFunction χ) s / LFunction χ s)) s := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have h : HasDerivAt (fun s ↦ ∑ χ ∈ nonprincipal q,
      χ ↑u⁻¹ * (χ.primePart s + χ.primePowerPart s)) _ s :=
    HasDerivAt.fun_sum fun χ _ ↦ (χ.hasDerivAt_primePart_add_primePowerPart hs).const_mul _
  exact h.congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hs) fun s hs ↦
    classLog_eq hC hs)

open Classical in
/-- **Continuation of the logarithmic derivative identity.** Under bounded partial sums, on
`re s > 1 / 2`,
`(∏_{χ ≠ 1} L(s, χ)) Φ'(s) = ∑_{χ ≠ 1} χ(u⁻¹) L'(s, χ) ∏_{ψ ≠ 1, ψ ≠ χ} L(s, ψ)`:
both sides are holomorphic there and agree on `re s > 1`. -/
theorem prod_mul_deriv_classLog {s : ℂ} (hs : 1 / 2 < s.re) :
    (∏ χ ∈ nonprincipal q, LFunction χ s) * deriv (classLog u) s =
      ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * deriv (LFunction χ) s *
        ∏ ψ ∈ (nonprincipal q).erase χ, LFunction ψ s := by
  set U : Set ℂ := {s | 1 / 2 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hL : ∀ χ ∈ nonprincipal q, Differentiable ℂ (LFunction χ) :=
    fun χ hχ ↦ differentiable_LFunction (mem_nonprincipal.1 hχ)
  have hL' : ∀ χ ∈ nonprincipal q, DifferentiableOn ℂ (deriv (LFunction χ)) U :=
    fun χ hχ ↦ ((hL χ hχ).differentiableOn.deriv isOpen_univ).mono (Set.subset_univ _)
  have hPr : ∀ Y ⊆ nonprincipal q, Differentiable ℂ fun s ↦ ∏ ψ ∈ Y, LFunction ψ s := by
    intro Y hY
    convert Differentiable.finsetProd (u := Y) (f := fun ψ ↦ LFunction ψ)
      fun ψ hψ ↦ hL ψ (hY hψ) using 1
    ext s
    simp
  have hlhs : AnalyticOnNhd ℂ
      (fun s ↦ (∏ χ ∈ nonprincipal q, LFunction χ s) * deriv (classLog u) s) U :=
    (((hPr _ subset_rfl).differentiableOn).mul
      ((differentiableOn_classLog hC).deriv hUo)).analyticOnNhd hUo
  have hrhs : AnalyticOnNhd ℂ (fun s ↦ ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ *
      deriv (LFunction χ) s * ∏ ψ ∈ (nonprincipal q).erase χ, LFunction ψ s) U :=
    (DifferentiableOn.fun_sum fun χ hχ ↦ ((hL' χ hχ).const_mul _).mul
      (hPr _ (erase_subset _ _)).differentiableOn).analyticOnNhd hUo
  have h2 : (2 : ℂ) ∈ U := by
    change (1 : ℝ) / 2 < (2 : ℂ).re
    norm_num
  refine hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs (convex_halfSpace_re_gt _).isPreconnected
    h2 ?_ hs
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
  have hne : ∀ χ ∈ nonprincipal q, LFunction χ s ≠ 0 := fun χ hχ ↦
    LFunction_ne_zero_of_one_le_re χ (.inl (mem_nonprincipal.1 hχ)) hs.le
  rw [(hasDerivAt_classLog hC hs).deriv, mul_sum]
  refine sum_congr rfl fun χ hχ ↦ ?_
  rw [← mul_prod_erase _ (fun ψ ↦ LFunction ψ s) hχ]
  field_simp [hne χ hχ]

/-- **The prime-square side at `1 / 2`.** Under bounded partial sums, with
`ν = #{r mod q | r ^ 2 = u}`, `Φ(σ) = ((ν - 1) / 2) log (1 / (σ - 1 / 2)) + O(1)` as
`σ → 1 / 2⁺`. The `m = 2` terms of the prime-power parts give
`½ ∑_{χ ≠ 1} χ(u⁻¹) ∑ₖ χ(pₖ²) pₖ ^ (-2σ) = ½ ∑ₚ (φ(q) [p² ≡ u] - [p ∤ q]) p ^ (-2σ)`; by
Dirichlet density in each of the `ν` classes `r` with `r² = u` this is
`((ν - 1) / 2) ∑_{p ∤ q} p ^ (-2σ) + O(1)`, and `∑_{p ∤ q} p ^ (-t) = log (1 / (t - 1)) + O(1)`.
The terms with `m ≥ 3` and `φ(q) A(σ)` are continuous at `1 / 2`. -/
theorem exists_norm_classLog_add_mul_log_le :
    ∃ C' : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖classLog u σ +
      (((#{r : ZMod q | r ^ 2 = u} : ℕ) : ℂ) - 1) / 2 * Real.log (σ - 1 / 2)‖ ≤ C' := by
  set S : Finset (ZMod q) := {r : ZMod q | r ^ 2 = u}
  set ν : ℂ := ((#S : ℕ) : ℂ)
  set G1 : ℂ → ℂ := (1 : DirichletCharacter ℂ q).primePart
  set R : ℂ → ℂ := fun s ↦
    q.totient * classAbel u s + ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * χ.tailPart 3 s
  have hR : ContinuousAt R ((1 / 2 : ℝ) : ℂ) := by
    have hA := (differentiableOn_classAbel hC).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show (0 : ℝ) < ((1 / 2 : ℝ) : ℂ).re by norm_num))
    have hT : ∀ χ : DirichletCharacter ℂ q, DifferentiableAt ℂ (χ.tailPart 3) ((1 / 2 : ℝ) : ℂ) :=
      fun χ ↦ (χ.differentiableOn_tailPart (m := 3) (by norm_num)).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (show 1 / ((3 : ℕ) : ℝ) < ((1 / 2 : ℝ) : ℂ).re by norm_num))
    exact ((hA.const_mul _).add (DifferentiableAt.fun_sum fun χ _ ↦
      (hT χ).const_mul _)).continuousAt
  have hRe : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖R σ‖ ≤ ‖R ((1 / 2 : ℝ) : ℂ)‖ + 1 :=
    ((continuous_ofReal.tendsto _).eventually
      (hR.norm.eventually (eventually_le_nhds (lt_add_one _)))).filter_mono nhdsWithin_le_nhds
  have hSu : ∀ r ∈ S, IsUnit r := fun r hr ↦
    (isUnit_pow_iff two_ne_zero).1 ((mem_filter.1 hr).2 ▸ u.isUnit)
  have hD : ∀ r ∈ S, ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      ‖(q.totient : ℂ) * classSeries r σ - G1 σ‖ ≤ M :=
    fun r hr ↦ exists_norm_classSeries_sub_primePart_one_le (hSu r hr)
  choose! M hM using hD
  obtain ⟨C₁, hC₁⟩ := exists_norm_primePart_one_add_log_le (q := q)
  have h2 : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝[>] (1 / 2)) (𝓝[>] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const_mul 2).tendsto' _ _ (by norm_num)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun σ (hσ : 1 / 2 < σ) ↦
        show 1 < 2 * σ by linarith⟩
  refine ⟨(‖R ((1 / 2 : ℝ) : ℂ)‖ + 1) + (∑ r ∈ S, M r) / 2 +
    ‖(ν - 1) / 2‖ * C₁ + ‖(ν - 1) / 2‖ * Real.log 2, ?_⟩
  filter_upwards [hRe, h2.eventually hC₁, Ioc_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)]
    with σ hRσ hlog hσ
  have hσ' : 1 / 2 < (σ : ℂ).re := by simpa using hσ.1
  have hσ2 : 1 < 2 * σ := by linarith [hσ.1]
  have hσ2' : 2 * σ ≤ 2 := by linarith [hσ.2]
  -- the prime-power parts, split at the squares
  have hA : classLog u σ = R σ +
      (∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * (χ ^ 2).primePart ((2 * σ : ℝ) : ℂ)) / 2 := by
    have e : ∀ χ : DirichletCharacter ℂ q, χ.primePowerPart σ =
        (χ ^ 2).primePart ((2 * σ : ℝ) : ℂ) / 2 + χ.tailPart 3 σ := fun χ ↦ by
      rw [primePowerPart_eq_primePart_sq_add_tailPart χ hσ', ofReal_mul, ofReal_ofNat]
    simp only [classLog, R, e, mul_add, sum_add_distrib, sum_div, mul_div_assoc]
    ring
  -- orthogonality and the square roots of `u`
  have hB : ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * (χ ^ 2).primePart ((2 * σ : ℝ) : ℂ) =
      ∑ r ∈ S, ((q.totient : ℂ) * classSeries r (2 * σ) - G1 ((2 * σ : ℝ) : ℂ)) +
        (ν - 1) * G1 ((2 * σ : ℝ) : ℂ) := by
    have e2 : ∀ χ : DirichletCharacter ℂ q, (χ ^ 2).primePart ((2 * σ : ℝ) : ℂ) =
        ∑' k : ℕ, χ ((nthPrime k : ZMod q) ^ 2) * (nthPrime k : ℂ) ^ (-((2 * σ : ℝ) : ℂ)) :=
      fun χ ↦ tsum_congr fun k ↦ by rw [primeTerm, MulChar.pow_apply' χ two_ne_zero, map_pow]
    have h := sum_nonprincipal_mul_tsum_eq u (fun r ↦ r ^ 2) hσ2
    have h1sq : ∀ r : ZMod q, (1 : DirichletCharacter ℂ q) (r ^ 2) =
        (1 : DirichletCharacter ℂ q) r := fun r ↦ by
      by_cases hr : IsUnit r
      · rw [MulChar.one_apply hr, MulChar.one_apply (hr.pow 2)]
      · rw [MulChar.map_nonunit _ hr,
          MulChar.map_nonunit _ (mt (isUnit_pow_iff two_ne_zero).1 hr)]
    have hG : G1 ((2 * σ : ℝ) : ℂ) =
        ∑ r : ZMod q, (1 : DirichletCharacter ℂ q) r * classSeries r (2 * σ) :=
      primePart_ofReal_eq_sum _ hσ2
    rw [sum_congr rfl fun χ _ ↦ by rw [e2 χ], h, hG]
    simp only [h1sq, sub_mul, sum_sub_distrib, ite_mul, zero_mul, ← sum_filter]
    rw [sum_const, nsmul_eq_mul, mul_sum]
    ring
  have hlog2 : ((Real.log (2 * σ - 1) : ℝ) : ℂ) = Real.log 2 + Real.log (σ - 1 / 2) := by
    rw [show 2 * σ - 1 = 2 * (σ - 1 / 2) by ring,
      Real.log_mul two_ne_zero (sub_ne_zero.2 hσ.1.ne'), ofReal_add]
  have key : classLog u σ + (ν - 1) / 2 * Real.log (σ - 1 / 2) = R σ +
      (∑ r ∈ S, ((q.totient : ℂ) * classSeries r (2 * σ) - G1 ((2 * σ : ℝ) : ℂ))) / 2 +
      (ν - 1) / 2 * (G1 ((2 * σ : ℝ) : ℂ) + Real.log (2 * σ - 1)) -
      (ν - 1) / 2 * Real.log 2 := by
    linear_combination hA + hB / 2 - (ν - 1) / 2 * hlog2
  have hS : ‖∑ r ∈ S, ((q.totient : ℂ) * classSeries r (2 * σ) - G1 ((2 * σ : ℝ) : ℂ))‖ ≤
      ∑ r ∈ S, M r :=
    (norm_sum_le _ _).trans (sum_le_sum fun r hr ↦ hM r hr _ hσ2 hσ2')
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul (_ / 2), norm_real, Real.norm_of_nonneg (Real.log_nonneg one_le_two)]
  refine add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add hRσ ?_)) ?_)) le_rfl
  · rw [norm_div, RCLike.norm_ofNat]
    exact div_le_div_of_nonneg_right hS zero_le_two
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hlog (norm_nonneg _)

end SingleClass

section Main

/-- `L(·, χ)` does not vanish identically near any point, for `χ ≠ 1`: it is entire and
`L(2, χ) ≠ 0`. -/
theorem not_eventually_LFunction_eq_zero {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (z : ℂ) : ¬ ∀ᶠ s in 𝓝 z, LFunction χ s = 0 := by
  intro h
  have h2 := ((differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
    ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) h
    (Set.mem_univ 2)
  exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by norm_num) h2

/-- **The single-class theorem, analytic form.** For `q ≥ 3` and a unit `u` modulo `q`, the
partial sums `∑_{k < n} ([pₖ ≡ u] - [pₖ ∤ q] / φ(q))` are unbounded.

Otherwise `Φ = classLog u` is holomorphic on `re s > 1 / 2`. On the one hand
(`exists_norm_classLog_add_mul_log_le`) `Φ(σ) = -((ν - 1) / 2) log (σ - 1 / 2) + O(1)` as
`σ → 1 / 2⁺`, with `ν` the number of square roots of `u`; on the other hand
(`Complex.exists_norm_sub_mul_log_le_of_prod_mul_deriv_eq`) `Φ(σ) = x log (σ - 1 / 2) + O(1)` with
`x = ∑_{χ ≠ 1} χ(u⁻¹) m_χ`, `m_χ` the order of vanishing of `L(·, χ)` at `1 / 2`. Hence
`x = (1 - ν) / 2`. But `x` is an algebraic integer and `ν` is even (`even_card_sq_eq`), so
`(1 - ν) / 2` is not: zeros of `L(·, χ)` at `1 / 2` can shift `x` only by algebraic integers. -/
theorem not_exists_norm_sum_classWeight_le (hq : 3 ≤ q) (u : (ZMod q)ˣ) :
    ¬ ∃ C : ℝ, ∀ n, ‖∑ k ∈ range n, classWeight u (nthPrime k)‖ ≤ C := by
  classical
  rintro ⟨C, hC⟩
  obtain ⟨C₁, h₁⟩ := exists_norm_classLog_add_mul_log_le hC
  have hΦ : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), DifferentiableAt ℂ (classLog u) σ ∧
      (∏ χ ∈ nonprincipal q, LFunction χ σ) * deriv (classLog u) σ =
        ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * deriv (LFunction χ) σ *
          ∏ ψ ∈ (nonprincipal q).erase χ, LFunction ψ σ := by
    refine eventually_nhdsWithin_of_forall fun σ (hσ : 1 / 2 < σ) ↦ ?_
    have hσ' : 1 / 2 < (σ : ℂ).re := by simpa using hσ
    exact ⟨(differentiableOn_classLog hC).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hσ'), prod_mul_deriv_classLog hC hσ'⟩
  obtain ⟨m, C₂, h₂⟩ := Complex.exists_norm_sub_mul_log_le_of_prod_mul_deriv_eq (nonprincipal q)
    (fun χ ↦ LFunction χ) (fun χ ↦ χ ↑u⁻¹) (s₀ := 1 / 2)
    (fun χ hχ ↦ (differentiable_LFunction (mem_nonprincipal.1 hχ)).analyticAt _)
    (fun χ hχ ↦ not_eventually_LFunction_eq_zero (mem_nonprincipal.1 hχ) _) hΦ
  set x : ℂ := ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * (m χ : ℂ)
  set ν : ℕ := #{r : ZMod q | r ^ 2 = u}
  have hx : x + ((ν : ℂ) - 1) / 2 = 0 := by
    refine Complex.eq_zero_of_eventually_norm_mul_log_le (s₀ := 1 / 2) (C := C₁ + C₂) ?_
    filter_upwards [h₁, h₂] with σ h1 h2
    calc ‖(x + ((ν : ℂ) - 1) / 2) * Real.log (σ - 1 / 2)‖ =
        ‖(classLog u σ + ((ν : ℂ) - 1) / 2 * Real.log (σ - 1 / 2)) -
          (classLog u σ - x * Real.log (σ - 1 / 2))‖ := by ring_nf
      _ ≤ C₁ + C₂ := (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hx' : x = ((1 - ν : ℤ) : ℂ) / 2 := by
    push_cast
    linear_combination hx
  have hint : IsIntegral ℤ x :=
    IsIntegral.sum _ fun χ _ ↦ (isIntegral_apply_unit χ u⁻¹).mul (isIntegral_natCast _)
  obtain ⟨k, hk⟩ := even_card_sq_eq hq u
  refine Complex.not_isIntegral_intCast_div_two ⟨-(k : ℤ), ?_⟩ (hx' ▸ hint)
  change (1 : ℤ) - (ν : ℤ) = 2 * -(k : ℤ) + 1
  rw [show ν = k + k from hk]
  push_cast
  ring

omit [NeZero q] in
/-- For `a` coprime to `q` and a natural number `n`,
`re e(n) = [n ≡ a (mod q)] - φ(q)⁻¹ re 1(n)` for the unit `u = a`. -/
theorem re_classWeight_unitOfCoprime [NeZero q] {a : ℕ} (ha : a.Coprime q) (n : ℕ) :
    (classWeight (ZMod.unitOfCoprime a ha) n).re =
      (if n % q = a % q then 1 else 0) -
        (q.totient : ℝ)⁻¹ * ((1 : DirichletCharacter ℂ q) n).re := by
  have hφ : (q.totient : ℂ)⁻¹ = (((q.totient : ℝ))⁻¹ : ℝ) := by push_cast; rfl
  rw [classWeight, sub_re, hφ, re_ofReal_mul]
  congr 1
  by_cases h : n % q = a % q <;>
    simp [h, ZMod.coe_unitOfCoprime, ZMod.natCast_eq_natCast_iff']

/-- `|re 1(pₖ) - 1| ≤ [k < q]`: the prime `pₖ` is a unit modulo `q` as soon as `k ≥ q`. -/
theorem abs_re_one_apply_nthPrime_sub_one_le (k : ℕ) :
    |((1 : DirichletCharacter ℂ q) (nthPrime k)).re - 1| ≤ if k < q then 1 else 0 := by
  by_cases hu : IsUnit ((nthPrime k : ℕ) : ZMod q)
  · rw [MulChar.one_apply hu, one_re, sub_self, abs_zero]
    split_ifs <;> norm_num
  · have hk : k < q := by
      have hdvd : nthPrime k ∣ q := by
        by_contra h
        exact hu ((ZMod.isUnit_prime_iff_not_dvd (Nat.prime_nth_prime k)).2 h)
      have := Nat.le_of_dvd (NeZero.pos q) hdvd
      have := Nat.add_two_le_nth_prime k
      omega
    rw [MulChar.map_nonunit _ hu]
    simp [hk]

end Main

end DirichletCharacter

open DirichletCharacter in
/-- **The single-class theorem.** For `q ≥ 3` and `a` coprime to `q`, the indicator sequence
`k ↦ [pₖ ≡ a (mod q)]` of the primes in one residue class is not eventually periodic.

If it were, its partial sums would be `c n + O(1)`, hence so would those of
`e(pₖ) = [pₖ ≡ a] - [pₖ ∤ q] / φ(q)`, with slope `c - 1 / φ(q)`. The Dirichlet series
`∑ₖ e(pₖ) pₖ ^ (-σ)` is bounded as `σ → 1⁺` (orthogonality and `exists_norm_primePart_le`), so
the slope is `0` (`not_exists_abs_sum_sub_mul_le_of_abs_tsum_le`), and then the partial sums of `e`
are bounded, which `not_exists_norm_sum_classWeight_le` excludes. -/
theorem Nat.not_eventuallyPeriodic_nthPrime_modEq {q a : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q)
    {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic (fun k ↦ if Nat.nth Nat.Prime k % q = a % q then 1 else 0) P := by
  intro hper
  have : NeZero q := ⟨by omega⟩
  set u : (ZMod q)ˣ := ZMod.unitOfCoprime a ha
  set φ : ℝ := (q.totient : ℝ)
  set d : ℕ → ℝ := fun k ↦ if nthPrime k % q = a % q then 1 else 0
  set e : ℕ → ℝ := fun k ↦ (classWeight u (nthPrime k)).re
  have hd : Function.EventuallyPeriodic d P := by
    filter_upwards [hper] with k hk
    simp only [d]
    split_ifs at hk ⊢ <;> simp_all
  obtain ⟨c, C, hcC⟩ := hd.exists_abs_sum_real_sub_mul_le hP
  have hφ : 0 < φ := Nat.cast_pos.2 (Nat.totient_pos.2 (by omega))
  have hone : ∀ n : ℕ,
      |∑ k ∈ range n, ((1 : DirichletCharacter ℂ q) (nthPrime k)).re - n| ≤ q := by
    intro n
    calc _ = |∑ k ∈ range n, (((1 : DirichletCharacter ℂ q) (nthPrime k)).re - 1)| := by
          simp [sum_sub_distrib]
      _ ≤ ∑ k ∈ range n, (if k < q then (1 : ℝ) else 0) := (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun k _ ↦ abs_re_one_apply_nthPrime_sub_one_le k)
      _ ≤ q := by
          rw [sum_boole]
          exact_mod_cast (card_le_card fun k hk ↦ by
            simp only [mem_filter, mem_range] at hk ⊢; exact hk.2).trans (card_range q).le
  have hlin : ∀ n : ℕ, |∑ k ∈ range n, e k - (c - φ⁻¹) * n| ≤ C + φ⁻¹ * q := by
    intro n
    have he : ∑ k ∈ range n, e k = ∑ k ∈ range n, d k -
        φ⁻¹ * ∑ k ∈ range n, ((1 : DirichletCharacter ℂ q) (nthPrime k)).re := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ ↦ re_classWeight_unitOfCoprime ha _
    rw [he]
    calc _ = |(∑ k ∈ range n, d k - c * n) - φ⁻¹ *
          (∑ k ∈ range n, ((1 : DirichletCharacter ℂ q) (nthPrime k)).re - n)| := by ring_nf
      _ ≤ |∑ k ∈ range n, d k - c * n| + |φ⁻¹ *
          (∑ k ∈ range n, ((1 : DirichletCharacter ℂ q) (nthPrime k)).re - n)| := abs_sub _ _
      _ ≤ C + φ⁻¹ * q := by
          rw [abs_mul, abs_of_pos (inv_pos.2 hφ)]
          gcongr
          · exact hcC n
          · exact hone n
  by_cases hc : c - φ⁻¹ = 0
  · refine not_exists_norm_sum_classWeight_le hq u ⟨C + φ⁻¹ * q, fun n ↦ ?_⟩
    have h : ∑ k ∈ range n, classWeight u (nthPrime k) = ((∑ k ∈ range n, e k : ℝ) : ℂ) := by
      push_cast
      exact sum_congr rfl fun k _ ↦ (ofReal_re_classWeight u _).symm
    rw [h, norm_real, Real.norm_eq_abs]
    simpa [hc] using hlin n
  · obtain ⟨M, hM⟩ := exists_norm_sum_nonprincipal_mul_primePart_le (q := q)
      (fun χ ↦ χ ↑u⁻¹) fun χ ↦ χ.norm_le_one _
    refine not_exists_abs_sum_sub_mul_le_of_abs_tsum_le (a := e) (B := 2)
      (fun k ↦ (abs_re_le_norm _).trans (norm_classWeight_le u _)) (M := φ⁻¹ * M)
      (fun σ hσ hσ2 ↦ ?_) ⟨c - φ⁻¹, hc, _, hlin⟩
    have hs : 1 < (σ : ℂ).re := by simpa using hσ
    have e1 : ((∑' k, e k * (nthPrime k : ℝ) ^ (-σ) : ℝ) : ℂ) = (q.totient : ℂ)⁻¹ *
        ∑ χ ∈ nonprincipal q, χ ↑u⁻¹ * χ.primePart σ := by
      rw [← totient_mul_tsum_classWeight u hs, ← mul_assoc, inv_mul_cancel₀ totient_ne_zero,
        one_mul, ofReal_tsum]
      refine tsum_congr fun k ↦ ?_
      rw [ofReal_mul, ofReal_re_classWeight, ofReal_cpow (Nat.cast_nonneg _)]
      push_cast
      rfl
    rw [← Real.norm_eq_abs, ← norm_real, e1, norm_mul, norm_inv, norm_natCast]
    exact mul_le_mul_of_nonneg_left (hM σ hσ hσ2) (inv_nonneg.2 hφ.le)

namespace Real

/-- The **single-class constant** of modulus `q`, residue `a` and base `b`: the number whose
`k`-th base-`b` digit is `1` if the `k`-th prime `pₖ` (with `p₀ = 2`) is congruent to `a` modulo
`q`, and `0` otherwise. For `q = 4`, `a = 3`, `b = 2` it is half of Rokicki's constant
(`classConstant_four_three_two`). -/
noncomputable def classConstant (q a b : ℕ) : ℝ :=
  ∑' k : ℕ, (if Nat.nth Nat.Prime k % q = a % q then (1 : ℝ) else 0) / b ^ (k + 1)

/-- **Single-class constants are irrational**: for `q ≥ 3`, `a` coprime to `q` and every base
`b ≥ 2`, the number `∑ₖ [pₖ ≡ a (mod q)] / b ^ (k + 1)` is irrational. -/
theorem irrational_classConstant {q a b : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hb : 2 ≤ b) :
    Irrational (classConstant q a b) := by
  have h := irrational_tsum_div_pow hb
    (d := fun k ↦ if Nat.nth Nat.Prime k % q = a % q then 1 else 0)
    (fun k ↦ by split_ifs <;> omega) fun P hP ↦ Nat.not_eventuallyPeriodic_nthPrime_modEq hq ha hP
  convert h using 1
  refine tsum_congr fun k ↦ ?_
  split_ifs <;> simp

/-- **Rokicki's constant is twice a single-class constant**: `classConstant 4 3 2 = ρ / 2`. The
digit of `p₀ = 2` is `0`, and the remaining digits are Rokicki's, shifted by one place. -/
theorem classConstant_four_three_two : classConstant 4 3 2 = rokickiConstant / 2 := by
  have hs : Summable fun k : ℕ ↦
      (if Nat.nth Nat.Prime k % 4 = 3 % 4 then (1 : ℝ) else 0) / 2 ^ (k + 1) := by
    refine summable_geometric_two.of_nonneg_of_le (fun k ↦ by positivity) fun k ↦ ?_
    calc _ ≤ 1 / (2 : ℝ) ^ (k + 1) :=
          div_le_div_of_nonneg_right (by split_ifs <;> norm_num) (by positivity)
      _ ≤ 1 / 2 ^ k := one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ one_le_two k.le_succ)
      _ = (1 / 2) ^ k := (one_div_pow 2 k).symm
  rw [classConstant, Nat.cast_ofNat, hs.tsum_eq_zero_add, rokickiConstant, ← tsum_div_const,
    Nat.nth_prime_zero_eq_two]
  norm_num
  refine tsum_congr fun k ↦ ?_
  simp only [rokickiDigit, pow_succ]
  split_ifs <;> norm_num
  ring

/-- A third proof that Rokicki's constant is irrational, from the single-class theorem. -/
theorem irrational_rokickiConstant'' : Irrational rokickiConstant := by
  have h := irrational_classConstant (q := 4) (a := 3) (b := 2) (by norm_num) (by norm_num)
    le_rfl
  rw [classConstant_four_three_two] at h
  simpa using h.mul_ratCast (q := 2) two_ne_zero

end Real
