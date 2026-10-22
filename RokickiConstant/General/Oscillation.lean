/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import RokickiConstant.General.CharacterSums

/-!
# Quantitative oscillation of quadratic characters over the primes

Let `χ` be a nonprincipal quadratic Dirichlet character, `p₀ = 2 < p₁ < ⋯` the primes and
`S n = ∑_{k < n} χ(pₖ)`. `RokickiConstant.General.CharacterSums` shows that `S` is unbounded. Here
we show that `S n` is not `O(n ^ θ)` for any `θ < 1 / 2`, and likewise that `∑_{p < x} χ(p)` is
not `O(x ^ θ)`: in Landau's notation, `∑_{p < x} χ(p) = Ω(x ^ (1 / 2 - ε))` for every `ε > 0`.

The proof is the one of the bounded case with a quantitative Abel series. If
`‖∑_{j ≤ k} a j‖ ≤ C · q k ^ θ` with `0 ≤ θ`, then the Abel series
`∑ₖ (∑_{j ≤ k} a j) · (q k ^ (-s) - q (k + 1) ^ (-s))` converges absolutely and is holomorphic on
`re s > θ`. The termwise bound rests on the elementary inequality
`x ^ θ (x ^ (-δ) - y ^ (-δ)) ≤ δ / (δ - θ) · (x ^ (θ - δ) - y ^ (θ - δ))` for `0 < x ≤ y`,
`0 ≤ θ < δ` (weighted AM-GM), after which the right side telescopes. For `θ < 1 / 2` the identity
`L(s, χ) = exp (abelSeries s + primePowerPart χ s)` holds on `re s > 1 / 2`, the Abel series is
continuous at `s = 1 / 2`, and the blow-up of the prime-power part at `1 / 2⁺` contradicts the
continuity of the entire function `L(·, χ)`.

For Rokicki's constant `ρ` (`χ = χ₄`) this says that the number of digits `0` minus the number of
digits `1` among the first `n` binary digits of `ρ` is not `O(n ^ θ)` for any `θ < 1 / 2`.

No prime number theorem is used. The exponent `1 / 2` is the limit of the method: it is the
abscissa of absolute convergence of the prime-power part, where `∑ₚ p ^ (-2σ)` diverges.

**Log-power refinement.** The same argument works at the exponent `1 / 2` itself, up to a power
of the logarithm: for `A > 1`, `∑_{p < x} χ(p)` is not `O(x ^ (1 / 2) / (log x) ^ A)`. Under such a
bound the Abel series converges uniformly on `σ ∈ [1 / 2, 2]`, because its terms are dominated by
the telescoping series of `(log pₖ) ^ (1 - A)` (`rpow_mul_rpow_neg_sub_div_log_rpow_le`, using
Bertrand's postulate `pₖ₊₁ ≤ 2 pₖ`); so it is continuous at `1 / 2` and the contradiction is the
same. At `A = 1` the dominating series `∑ (pₖ₊₁ - pₖ) / (pₖ log pₖ)` diverges and the method stops.
In the index scale (`n` primes, `pₙ ≍ n log n`) this becomes: `∑_{k < n} χ(pₖ)` is not
`O(n ^ (1 / 2) / (log n) ^ A)` for `A > 1 / 2`, via Chebyshev's bounds `k log pₖ ≤ 5 pₖ` and
`pₖ ≤ k ^ 2` (Mathlib's `Chebyshev.pi_le_log4_mul_div` and `Chebyshev.pi_ge`).

## Main statements

* `abelSeries_eq_tsum_of_le_rpow`, `differentiableOn_abelSeries_of_le_rpow`: the Abel series under
  polynomially bounded partial sums.
* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_le_rpow`: no bound `‖S n‖ ≤ C n ^ θ`.
* `DirichletCharacter.IsQuadratic.not_isBigO_rpow`, `not_isBigO_rpow_one_half_sub`: Landau form.
* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_primesBelow_le_rpow`,
  `not_isBigO_primesBelow_rpow`: the same for `∑_{p < x} χ(p)` against `x ^ θ`.
* `RokickiConstant.not_exists_abs_sum_rokickiDigit_le_rpow`,
  `RokickiConstant.not_isBigO_card_rokickiDigit_rpow`: the digits of `ρ`.
* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_primesBelow_le_rpow_div_log_rpow`,
  `not_isBigO_primesBelow_rpow_div_log_rpow`: `∑_{p < x} χ(p)` is not
  `O(x ^ (1 / 2) / (log x) ^ A)` for `A > 1`.
* `DirichletCharacter.IsQuadratic.not_exists_norm_sum_le_rpow_div_log_rpow`,
  `not_isBigO_rpow_div_log_rpow`: `∑_{k < n} χ(pₖ)` is not `O(n ^ (1 / 2) / (log n) ^ A)` for
  `A > 1 / 2`.
* `RokickiConstant.not_exists_abs_sum_rokickiDigit_le_rpow_div_log_rpow`,
  `RokickiConstant.not_isBigO_card_rokickiDigit_rpow_div_log_rpow`: the digits of `ρ`
  (`A > 1 / 2`).

## Tags

Dirichlet character, quadratic character, oscillation, Omega theorem, Abel summation
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

section AbelSeries

variable {a : ℕ → ℂ} {q : ℕ → ℕ}

/-- For `0 < x ≤ y` and `0 ≤ θ < δ`,
`x ^ θ (x ^ (-δ) - y ^ (-δ)) ≤ δ / (δ - θ) · (x ^ (-(δ - θ)) - y ^ (-(δ - θ)))`. -/
theorem rpow_mul_rpow_neg_sub_rpow_neg_le {x y θ δ : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hθ : 0 ≤ θ) (hθδ : θ < δ) :
    x ^ θ * (x ^ (-δ) - y ^ (-δ)) ≤ δ / (δ - θ) * (x ^ (-(δ - θ)) - y ^ (-(δ - θ))) := by
  have hy : 0 < y := hx.trans_le hxy
  have hδ : 0 < δ := hθ.trans_lt hθδ
  have hu0 : 0 ≤ x / y := by positivity
  set r := (δ - θ) / δ with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hδ.le
  have hr1 : r ≤ 1 := (div_le_one hδ).2 (by linarith)
  have key := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.2 hr1) hr0 zero_le_one
    (Real.rpow_nonneg hu0 δ) (sub_add_cancel 1 r)
  rw [Real.one_rpow, one_mul, mul_one, ← Real.rpow_mul hu0, hr, mul_div_cancel₀ _ hδ.ne'] at key
  set X := x ^ (-(δ - θ)) with hX
  have hX0 : 0 < X := by positivity
  have e1 : x ^ θ * x ^ (-δ) = X := by rw [hX, ← Real.rpow_add hx]; ring_nf
  have e2 : x ^ θ * y ^ (-δ) = X * (x / y) ^ δ := by
    rw [Real.div_rpow hx.le hy.le, Real.rpow_neg hy.le, hX, mul_div_assoc', ← Real.rpow_add hx,
      div_eq_mul_inv]
    ring_nf
  have e3 : y ^ (-(δ - θ)) = X * (x / y) ^ (δ - θ) := by
    rw [Real.div_rpow hx.le hy.le, hX, Real.rpow_neg hx.le, Real.rpow_neg hy.le]
    field_simp
  rw [mul_sub, e1, e2, e3]
  have hδθ : 0 < δ - θ := by linarith
  have key' : δ * (x / y) ^ (δ - θ) ≤ θ + (δ - θ) * (x / y) ^ δ :=
    calc _ ≤ δ * (1 - (δ - θ) / δ + (δ - θ) / δ * (x / y) ^ δ) :=
          mul_le_mul_of_nonneg_left key hδ.le
      _ = _ := by field_simp; ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hδθ]
  nlinarith [mul_le_mul_of_nonneg_left key' hX0.le]

/-- If the partial sums of `a` satisfy `‖∑_{j ≤ k} a j‖ ≤ C · q k ^ θ`, then `0 ≤ C`. -/
theorem nonneg_of_norm_sum_le_rpow {C θ : ℝ}
    (ha : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤ C * (q k : ℝ) ^ θ) (hq₀ : 0 < q 0) : 0 ≤ C :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (ha 0)) (by positivity)

/-- Termwise bound for the Abel series under the polynomial bound
`‖∑_{j ≤ k} a j‖ ≤ C · q k ^ θ`, with any exponent `θ < δ ≤ re s`. -/
theorem norm_abelSeries_term_le_of_le_rpow {C θ : ℝ} (hθ₀ : 0 ≤ θ)
    (ha : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤ C * (q k : ℝ) ^ θ) (hq₀ : 0 < q 0)
    (hq : StrictMono q) {s : ℂ} {δ : ℝ} (hθδ : θ < δ) (hδs : δ ≤ s.re) (k : ℕ) :
    ‖(∑ j ∈ range (k + 1), a j) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s))‖ ≤
      C * (‖s‖ / (δ - θ)) * ((q k : ℝ) ^ (-(δ - θ)) - (q (k + 1) : ℝ) ^ (-(δ - θ))) := by
  have hC := nonneg_of_norm_sum_le_rpow ha hq₀
  have hqk : (1 : ℝ) ≤ q k := Nat.one_le_cast.2 (hq₀.trans_le (hq.monotone (Nat.zero_le k)))
  have hδ : 0 < δ := hθ₀.trans_lt hθδ
  have hxy : (q k : ℝ) ≤ q (k + 1) := Nat.cast_le.2 (hq.monotone k.le_succ)
  have h := norm_ofReal_cpow_neg_sub_cpow_neg_le hqk hxy hδ hδs
  simp only [Complex.ofReal_natCast] at h
  have h' := rpow_mul_rpow_neg_sub_rpow_neg_le (by linarith) hxy hθ₀ hθδ
  rw [norm_mul]
  calc _ ≤ C * (q k : ℝ) ^ θ * (‖s‖ / δ * ((q k : ℝ) ^ (-δ) - (q (k + 1) : ℝ) ^ (-δ))) :=
        mul_le_mul (ha k) h (norm_nonneg _) ((norm_nonneg _).trans (ha k))
    _ = C * (‖s‖ / δ) * ((q k : ℝ) ^ θ * ((q k : ℝ) ^ (-δ) - (q (k + 1) : ℝ) ^ (-δ))) := by
        ring
    _ ≤ C * (‖s‖ / δ) * (δ / (δ - θ) *
          ((q k : ℝ) ^ (-(δ - θ)) - (q (k + 1) : ℝ) ^ (-(δ - θ)))) := by gcongr
    _ = _ := by
        have : δ - θ ≠ 0 := by linarith
        field_simp

/-- Under the polynomial bound `‖∑_{j ≤ k} a j‖ ≤ C · q k ^ θ` with `0 ≤ θ`, the series
defining `abelSeries a q s` converges absolutely for `θ < re s`. -/
theorem summable_abelSeries_of_le_rpow {C θ : ℝ} (hθ₀ : 0 ≤ θ)
    (ha : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤ C * (q k : ℝ) ^ θ) (hq₀ : 0 < q 0)
    (hq : StrictMono q) {s : ℂ} (hs : θ < s.re) :
    Summable fun k : ℕ ↦
      (∑ j ∈ range (k + 1), a j) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s)) :=
  Summable.of_norm_bounded ((summable_sub_of_antitone
    (antitone_natCast_rpow_neg hq₀ hq (by linarith : 0 ≤ s.re - θ))
    fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).mul_left (C * (‖s‖ / (s.re - θ))))
    fun k ↦ norm_abelSeries_term_le_of_le_rpow hθ₀ ha hq₀ hq hs le_rfl k

/-- Under the polynomial bound `‖∑_{j ≤ k} a j‖ ≤ C · q k ^ θ` with `0 ≤ θ`, the Abel series
is holomorphic on the half-plane `θ < re s`. -/
theorem differentiableOn_abelSeries_of_le_rpow {C θ : ℝ} (hθ₀ : 0 ≤ θ)
    (ha : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤ C * (q k : ℝ) ^ θ) (hq₀ : 0 < q 0)
    (hq : StrictMono q) : DifferentiableOn ℂ (abelSeries a q) {s : ℂ | θ < s.re} := by
  intro s₀ hs₀
  have hs₀' : θ < s₀.re := hs₀
  set δ := (θ + s₀.re) / 2 with hδ
  have hθδ : θ < δ := by linarith
  set U : Set ℂ := {s | δ < s.re} ∩ Metric.ball 0 (‖s₀‖ + 1)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := ⟨show δ < s₀.re by linarith, by simp⟩
  have hC := nonneg_of_norm_sum_le_rpow ha hq₀
  have hne : ∀ k, (q k : ℂ) ≠ 0 := fun k ↦
    Nat.cast_ne_zero.2 (hq₀.trans_le (hq.monotone (Nat.zero_le k))).ne'
  have hd : DifferentiableOn ℂ (fun s ↦ ∑' k : ℕ,
      (∑ j ∈ range (k + 1), a j) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s))) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_sub_of_antitone (antitone_natCast_rpow_neg hq₀ hq (by linarith : 0 ≤ δ - θ))
        fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).mul_left
        (C * ((‖s₀‖ + 1) / (δ - θ)))) (fun k ↦ ?_) hU fun k s hs ↦ ?_
    · exact (((differentiable_neg.const_cpow (Or.inl (hne k))).sub
        (differentiable_neg.const_cpow (Or.inl (hne (k + 1))))).const_mul _).differentiableOn
    · refine (norm_abelSeries_term_le_of_le_rpow hθ₀ ha hq₀ hq hθδ hs.1.le k).trans ?_
      have hs' : ‖s‖ < ‖s₀‖ + 1 := by simpa using hs.2
      have hk : 0 ≤ (q k : ℝ) ^ (-(δ - θ)) - (q (k + 1) : ℝ) ^ (-(δ - θ)) :=
        sub_nonneg.2 (antitone_natCast_rpow_neg hq₀ hq (by linarith) k.le_succ)
      have : 0 < δ - θ := by linarith
      gcongr
  exact (hd.differentiableAt (hU.mem_nhds hs₀U)).differentiableWithinAt

/-- Under the polynomial bound `‖∑_{j ≤ k} a j‖ ≤ C · q k ^ θ` and bounded coefficients, the Abel
series agrees with the Dirichlet series `∑ₖ a k · q k ^ (-s)` for `1 < re s` and `θ < re s`. -/
theorem abelSeries_eq_tsum_of_le_rpow {B C θ : ℝ} (hθ₀ : 0 ≤ θ)
    (ha : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤ C * (q k : ℝ) ^ θ) (hb : ∀ k, ‖a k‖ ≤ B)
    (hq₀ : 0 < q 0) (hq : StrictMono q) {s : ℂ} (hs : 1 < s.re) (hθs : θ < s.re) :
    abelSeries a q s = ∑' k : ℕ, a k * (q k : ℂ) ^ (-s) := by
  have h1 := ((summable_mul_cpow_neg hb hq₀ hq hs).hasSum.tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have h0 : Tendsto (fun n ↦ (∑ j ∈ range (n + 1), a j) * (q n : ℂ) ^ (-s)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n ↦ C * (q n : ℝ) ^ (-(s.re - θ))) (fun n ↦ ?_) ?_
    · have hqn : 0 < q n := hq₀.trans_le (hq.monotone (Nat.zero_le n))
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hqn, Complex.neg_re,
        show -(s.re - θ) = θ + -s.re by ring, Real.rpow_add (by exact_mod_cast hqn), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (ha _) (by positivity)
    · simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < s.re - θ)).comp
        (tendsto_natCast_atTop_atTop.comp hq.tendsto_atTop)).const_mul C
  have h2 := h0.add (summable_abelSeries_of_le_rpow hθ₀ ha hq₀ hq hθs).hasSum.tendsto_sum_nat
  rw [zero_add] at h2
  refine tendsto_nhds_unique (h2.congr fun n ↦ ?_) h1
  exact (sum_range_succ_mul_eq_sum_mul_sub a (fun k ↦ (q k : ℂ) ^ (-s)) n).symm

end AbelSeries

section RealBounds

/-- For `1 ≤ x ≤ y`, `C · x ^ θ ≤ |C| · y ^ (max θ 0)`. This reduces polynomial bounds with a
negative exponent to bounds with exponent `0`. -/
theorem mul_rpow_le_abs_mul_rpow_max {C θ x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    C * x ^ θ ≤ |C| * y ^ max θ 0 :=
  calc C * x ^ θ ≤ |C| * x ^ θ :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C| * x ^ max θ 0 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _))
          (abs_nonneg C)
    _ ≤ |C| * y ^ max θ 0 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hxy (le_max_right _ _))
          (abs_nonneg C)

/-- A sequence vanishing at `0` that is `O(n ^ θ)` satisfies `‖f n‖ ≤ C · n ^ (max θ 0)` for
*all* `n`: the finitely many initial terms are absorbed into the constant. -/
theorem exists_forall_norm_le_rpow_of_isBigO {E : Type*} [SeminormedAddCommGroup E] {f : ℕ → E}
    {θ : ℝ} (h0 : f 0 = 0) (h : f =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ θ) :
    ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C * (n : ℝ) ^ max θ 0 := by
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  set M := ∑ n ∈ range N, ‖f n‖
  have hM : 0 ≤ M := sum_nonneg fun _ _ ↦ norm_nonneg _
  refine ⟨|c| + M, fun n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [h0, norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
  have hpow : 1 ≤ (n : ℝ) ^ max θ 0 := Real.one_le_rpow hn1 (le_max_right _ _)
  by_cases hnN : N ≤ n
  · have := hN n hnN
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at this
    nlinarith [mul_rpow_le_abs_mul_rpow_max (C := c) (θ := θ) hn1 le_rfl]
  · have : ‖f n‖ ≤ M := single_le_sum (fun k _ ↦ norm_nonneg (f k)) (mem_range.2 (by omega))
    nlinarith [abs_nonneg c]

end RealBounds

section LogPower

/-! ### The log-power refinement: real-variable bounds -/

/-- For `1 < x`, `x ^ θ / (log x) ^ A > 0`. -/
theorem rpow_div_log_rpow_pos {x : ℝ} (hx : 1 < x) (θ A : ℝ) : 0 < x ^ θ / Real.log x ^ A :=
  div_pos (Real.rpow_pos_of_pos (by linarith) θ) (Real.rpow_pos_of_pos (Real.log_pos hx) A)

/-- For `0 < x ≤ y`, `x ^ θ (x ^ (-θ) - y ^ (-θ)) = 1 - (x / y) ^ θ ≤ θ (log y - log x)`: this is
`1 - w⁻¹ ≤ log w` for `w = (y / x) ^ θ`. -/
theorem rpow_mul_rpow_neg_sub_rpow_neg_le_mul_log {x y θ : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x ^ θ * (x ^ (-θ) - y ^ (-θ)) ≤ θ * (Real.log y - Real.log x) := by
  have hy : 0 < y := hx.trans_le hxy
  have h1 := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < (y / x) ^ θ)
  rw [Real.log_rpow (by positivity), Real.log_div hy.ne' hx.ne', Real.div_rpow hy.le hx.le,
    inv_div] at h1
  rw [mul_sub, Real.rpow_neg hx.le, Real.rpow_neg hy.le, mul_inv_cancel₀ (by positivity),
    ← div_eq_mul_inv]
  linarith

/-- For `0 < a ≤ b` and `0 < δ`, `δ · (b - a) / b · b ^ (-δ) ≤ a ^ (-δ) - b ^ (-δ)`: a tangent-line
inequality for `t ↦ t ^ (-δ)`, proved from `(b / a) ^ δ = exp (δ log (b / a)) ≥ 1 + δ log (b / a)`
and `log (b / a) ≥ 1 - a / b`. -/
theorem mul_sub_div_mul_rpow_neg_le {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ) :
    δ * ((b - a) / b) * b ^ (-δ) ≤ a ^ (-δ) - b ^ (-δ) := by
  have hb : 0 < b := ha.trans_le hab
  have h1 : 1 - (b / a)⁻¹ ≤ Real.log (b / a) := Real.one_sub_inv_le_log_of_pos (by positivity)
  have h2 : 1 + δ * ((b - a) / b) ≤ (b / a) ^ δ := by
    rw [Real.rpow_def_of_pos (by positivity)]
    have : (b - a) / b = 1 - (b / a)⁻¹ := by field_simp
    nlinarith [Real.add_one_le_exp (Real.log (b / a) * δ)]
  have h3 : a ^ (-δ) = b ^ (-δ) * (b / a) ^ δ := by
    rw [Real.div_rpow hb.le ha.le, Real.rpow_neg hb.le, Real.rpow_neg ha.le]
    field_simp
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hb.le (-δ))]

/-- **The log-power telescoping bound.** For `2 ≤ x ≤ y ≤ 2 x` and `1 < A`,
`x ^ (1 / 2) (x ^ (-1 / 2) - y ^ (-1 / 2)) / (log x) ^ A`
`≤ 2 ^ A / (A - 1) · ((log x) ^ (-(A - 1)) - (log y) ^ (-(A - 1)))`.
With `a = log x ≤ b = log y ≤ 2 a`, the left side is at most
`(b - a) / a ^ A ≤ 2 ^ A (b - a) / b ^ A`, and
`(A - 1) (b - a) / b ^ A ≤ a ^ (1 - A) - b ^ (1 - A)`. No integrals are used. -/
theorem rpow_mul_rpow_neg_sub_div_log_rpow_le {x y A : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 2 * x) (hA : 1 < A) :
    x ^ (1 / 2 : ℝ) * (x ^ (-(1 / 2 : ℝ)) - y ^ (-(1 / 2 : ℝ))) / Real.log x ^ A ≤
      2 ^ A / (A - 1) * (Real.log x ^ (-(A - 1)) - Real.log y ^ (-(A - 1))) := by
  have ha : 0 < Real.log x := Real.log_pos (by linarith)
  have hab : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  have hb : 0 < Real.log y := ha.trans_le hab
  have hba : Real.log y ≤ 2 * Real.log x := by
    rw [two_mul, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have h1 := rpow_mul_rpow_neg_sub_rpow_neg_le_mul_log (θ := 1 / 2) (by linarith : 0 < x) hxy
  set a := Real.log x
  set b := Real.log y
  have h2 := mul_sub_div_mul_rpow_neg_le ha hab (by linarith : 0 < A - 1)
  have hbA : b ^ A ≤ 2 ^ A * a ^ A := by
    rw [← Real.mul_rpow (by norm_num) ha.le]
    exact Real.rpow_le_rpow hb.le hba (by linarith)
  have haA : 0 < a ^ A := by positivity
  have hbA0 : 0 < b ^ A := by positivity
  have hd : 0 ≤ a ^ (-(A - 1)) - b ^ (-(A - 1)) :=
    sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos ha hab (by linarith))
  have h2' : (A - 1) * (b - a) ≤ b ^ A * (a ^ (-(A - 1)) - b ^ (-(A - 1))) := by
    have e : (A - 1) * ((b - a) / b) * b ^ (-(A - 1)) = (A - 1) * (b - a) / b ^ A := by
      rw [show -(A - 1) = 1 + -A by ring, Real.rpow_add hb, Real.rpow_one, Real.rpow_neg hb.le]
      field_simp
    rw [e, div_le_iff₀ hbA0] at h2
    linarith
  rw [div_le_iff₀ haA, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hbA hd]

/-- A sequence that is `O(g)` for a positive `g` satisfies `‖f n‖ ≤ C · g n` for *all* `n`: the
finitely many initial terms are absorbed into the constant. -/
theorem exists_forall_norm_le_mul_of_isBigO {E : Type*} [SeminormedAddCommGroup E] {f : ℕ → E}
    {g : ℕ → ℝ} (hg : ∀ n, 0 < g n) (h : f =O[atTop] g) : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C * g n := by
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  set M := ∑ n ∈ range N, ‖f n‖ / g n
  refine ⟨|c| + M, fun n ↦ ?_⟩
  have hM : 0 ≤ M := sum_nonneg fun k _ ↦ div_nonneg (norm_nonneg _) (hg k).le
  by_cases hnN : N ≤ n
  · have := hN n hnN
    rw [Real.norm_of_nonneg (hg n).le] at this
    nlinarith [le_abs_self c, hg n]
  · have h1 : ‖f n‖ / g n ≤ M :=
      single_le_sum (fun k _ ↦ div_nonneg (norm_nonneg (f k)) (hg k).le) (mem_range.2 (by omega))
    rw [div_le_iff₀ (hg n)] at h1
    nlinarith [abs_nonneg c, hg n]

variable {a : ℕ → ℂ} {q : ℕ → ℕ}

/-- Termwise bound for the Abel series under the bound
`‖∑_{j ≤ k} a j‖ ≤ C · q k ^ (1 / 2) / (log (q k)) ^ A`, `1 < A`, for gaps `q (k + 1) ≤ 2 q k` and
any `s` with `1 / 2 ≤ re s`, *including the line `re s = 1 / 2`*: the term is at most
`2 ‖s‖ C · 2 ^ A / (A - 1) · (uₖ - uₖ₊₁)` with `uₖ = (log (q k)) ^ (-(A - 1))`. -/
theorem norm_abelSeries_term_le_of_le_rpow_div_log_rpow {C A : ℝ} (hA : 1 < A)
    (ha : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤ C * (q k : ℝ) ^ (1 / 2 : ℝ) / Real.log (q k) ^ A)
    (hq₀ : 2 ≤ q 0) (hq : StrictMono q) (hq2 : ∀ k, q (k + 1) ≤ 2 * q k) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (k : ℕ) :
    ‖(∑ j ∈ range (k + 1), a j) * ((q k : ℂ) ^ (-s) - (q (k + 1) : ℂ) ^ (-s))‖ ≤
      2 * ‖s‖ * C * (2 ^ A / (A - 1)) *
        (Real.log (q k) ^ (-(A - 1)) - Real.log (q (k + 1)) ^ (-(A - 1))) := by
  have hq2' : ∀ k, (2 : ℝ) ≤ q k := fun k ↦ by
    exact_mod_cast hq₀.trans (hq.monotone (Nat.zero_le k))
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left (by
    rw [← mul_div_assoc]; exact (norm_nonneg _).trans (ha 0))
    (rpow_div_log_rpow_pos (by linarith [hq2' 0]) _ _)
  have hxy : (q k : ℝ) ≤ q (k + 1) := Nat.cast_le.2 (hq.monotone k.le_succ)
  have h := norm_ofReal_cpow_neg_sub_cpow_neg_le (by linarith [hq2' k]) hxy
    (by norm_num : (0 : ℝ) < 1 / 2) hs
  simp only [Complex.ofReal_natCast] at h
  have h' := rpow_mul_rpow_neg_sub_div_log_rpow_le (hq2' k) hxy
    (by exact_mod_cast hq2 k) hA
  rw [norm_mul]
  calc _ ≤ C * (q k : ℝ) ^ (1 / 2 : ℝ) / Real.log (q k) ^ A *
        (‖s‖ / (1 / 2) * ((q k : ℝ) ^ (-(1 / 2 : ℝ)) - (q (k + 1) : ℝ) ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul (ha k) h (norm_nonneg _) ((norm_nonneg _).trans (ha k))
    _ = 2 * ‖s‖ * C * ((q k : ℝ) ^ (1 / 2 : ℝ) *
          ((q k : ℝ) ^ (-(1 / 2 : ℝ)) - (q (k + 1) : ℝ) ^ (-(1 / 2 : ℝ))) /
          Real.log (q k) ^ A) := by ring
    _ ≤ _ := by
        rw [mul_assoc (2 * ‖s‖ * C)]
        exact mul_le_mul_of_nonneg_left h' (by positivity)

/-- Under the bound `‖∑_{j ≤ k} a j‖ ≤ C · q k ^ (1 / 2) / (log (q k)) ^ A` with `1 < A` and
`q (k + 1) ≤ 2 q k`, the Abel series converges uniformly for real `σ ∈ [1 / 2, 2]`, hence
`σ ↦ abelSeries a q σ` is continuous there, up to and including `σ = 1 / 2`. -/
theorem continuousOn_abelSeries_of_le_rpow_div_log_rpow {C A : ℝ} (hA : 1 < A)
    (ha : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤ C * (q k : ℝ) ^ (1 / 2 : ℝ) / Real.log (q k) ^ A)
    (hq₀ : 2 ≤ q 0) (hq : StrictMono q) (hq2 : ∀ k, q (k + 1) ≤ 2 * q k) :
    ContinuousOn (fun σ : ℝ ↦ abelSeries a q σ) (Set.Icc (1 / 2) 2) := by
  have hq1 : ∀ k, (1 : ℝ) < q k := fun k ↦ by
    exact_mod_cast (by omega : 1 < 2).trans_le (hq₀.trans (hq.monotone (Nat.zero_le k)))
  have hanti : Antitone fun k ↦ Real.log (q k) ^ (-(A - 1)) := fun k l hkl ↦
    Real.rpow_le_rpow_of_nonpos (Real.log_pos (hq1 k))
      (Real.log_le_log (by linarith [hq1 k]) (by exact_mod_cast hq.monotone hkl)) (by linarith)
  have hne : ∀ k, (q k : ℂ) ≠ 0 := fun k ↦ by
    exact_mod_cast (show (0 : ℝ) < q k by linarith [hq1 k]).ne'
  refine continuousOn_tsum (fun k ↦ (((continuous_ofReal.neg.const_cpow (Or.inl (hne k))).sub
    (continuous_ofReal.neg.const_cpow (Or.inl (hne (k + 1))))).const_mul _).continuousOn)
    ((summable_sub_of_antitone hanti fun k ↦ Real.rpow_nonneg (Real.log_pos (hq1 k)).le _
      ).mul_left (2 * 2 * C * (2 ^ A / (A - 1)))) fun k σ hσ ↦ ?_
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left (by
    rw [← mul_div_assoc]; exact (norm_nonneg _).trans (ha 0))
    (rpow_div_log_rpow_pos (hq1 0) _ _)
  have hσ' : ‖(σ : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  refine (norm_abelSeries_term_le_of_le_rpow_div_log_rpow hA ha hq₀ hq hq2
    (by simpa using hσ.1) k).trans ?_
  have := hanti k.le_succ
  have : 0 ≤ 2 ^ A / (A - 1) := div_nonneg (by positivity) (by linarith)
  gcongr

end LogPower

namespace Nat

/-- **Bertrand's postulate** for consecutive primes: `pₖ₊₁ ≤ 2 pₖ`. -/
theorem nth_prime_succ_le_two_mul (k : ℕ) : nthPrime (k + 1) ≤ 2 * nthPrime k := by
  obtain ⟨r, hr, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (nthPrime k) (Nat.prime_nth_prime k).ne_zero
  by_contra h
  exact (Nat.le_nth_of_lt_nth_succ (by omega) hr).not_gt hlt

/-- `log pₖ ≤ 2 log k` for `k ≥ 4096`, i.e. `pₖ ≤ k ^ 2`: from Chebyshev's lower bound
`π(n) ≥ (n log 2 - log (n + 1)) / log n` (`Chebyshev.pi_ge`), which gives `π(n) ≥ √n + 1` for
`n ≥ 8 ^ 4`. -/
theorem log_nth_prime_le_two_mul_log {k : ℕ} (hk : 4096 ≤ k) :
    Real.log (nthPrime k) ≤ 2 * Real.log k := by
  set n := nthPrime k with hn
  have hn4 : (4096 : ℝ) ≤ n := by
    exact_mod_cast hk.trans ((Nat.add_two_le_nth_prime k).trans' (by omega))
  have hπ : Nat.primeCounting n = k + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k
  have hpi := Chebyshev.pi_ge n
  rw [hπ] at hpi
  set t := (n : ℝ) ^ (1 / 4 : ℝ) with ht
  have ht0 : 0 < t := by positivity
  have ht4 : t ^ 4 = n := by
    rw [ht, ← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have ht8 : 8 ≤ t := by
    by_contra h
    push Not at h
    nlinarith [pow_lt_pow_left₀ h ht0.le (by norm_num : (4 : ℕ) ≠ 0)]
  have hlogn : Real.log n = 4 * Real.log t := by rw [← ht4, Real.log_pow]; norm_num
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht0
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hlogn1 : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
    rw [two_mul, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have key : (t ^ 2 + 1) * Real.log n ≤ n * Real.log 2 - Real.log ((n : ℝ) + 1) := by
    have hn' : (n : ℝ) * Real.log 2 = t ^ 4 * Real.log 2 := by rw [ht4]
    rw [hlogn] at hlogn1 ⊢
    rw [hn']
    nlinarith [mul_le_mul_of_nonneg_left hlogt (by positivity : (0 : ℝ) ≤ t ^ 2 + 1),
      mul_le_mul_of_nonneg_left (by linarith : (0 : ℝ) ≤ t - 8) (by positivity : (0 : ℝ) ≤ t ^ 3),
      mul_le_mul_of_nonneg_left hl2.le (by positivity : (0 : ℝ) ≤ t ^ 4),
      mul_nonneg (mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ t - 8))
        (by linarith : (0 : ℝ) ≤ t + 8)]
  have hk' : t ^ 2 ≤ k := by
    rw [div_le_iff₀ hlogpos] at hpi
    push_cast at hpi
    nlinarith
  rw [hlogn, show (4 : ℝ) * Real.log t = 2 * Real.log (t ^ 2) by rw [Real.log_pow]; ring]
  gcongr

/-- `(k + 1) log pₖ ≤ 5 pₖ`, i.e. `pₖ ≥ (k + 1) log pₖ / 5`: from Chebyshev's upper bound
`π(x) ≤ log 4 · x / log √x + √x` (`Chebyshev.pi_le_log4_mul_div`) at `x = pₖ`, where
`π(pₖ) = k + 1`. -/
theorem succ_mul_log_nth_prime_le (k : ℕ) :
    (k + 1 : ℝ) * Real.log (nthPrime k) ≤ 5 * nthPrime k := by
  set n := nthPrime k with hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.prime_nth_prime k).two_le
  have hπ : Nat.primeCounting n = k + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k
  have hU := Chebyshev.pi_le_log4_mul_div (x := (n : ℝ)) (by linarith)
  rw [Nat.floor_natCast, Real.log_sqrt (by positivity), hπ] at hU
  push_cast at hU
  have hl : 0 < Real.log n := Real.log_pos (by linarith)
  have hs : √(n : ℝ) * Real.log n ≤ 2 * n := by
    have h1 : Real.log n = 2 * Real.log √(n : ℝ) := by
      rw [Real.log_sqrt (by positivity)]; ring
    have h2 : Real.log √(n : ℝ) ≤ √(n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
    have h3 : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hlog4 : Real.log 4 < 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have e : Real.log 4 * n / (Real.log n / 2) * Real.log n = 2 * Real.log 4 * n := by
    field_simp
  have h : (k + 1 : ℝ) * Real.log n ≤ 2 * Real.log 4 * n + √(n : ℝ) * Real.log n :=
    (mul_le_mul_of_nonneg_right hU hl.le).trans_eq (by rw [add_mul, e])
  nlinarith

end Nat

namespace DirichletCharacter.IsQuadratic

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Analytic continuation of the Euler product** under polynomially bounded partial sums: if
`‖∑_{j ≤ k} χ(pⱼ)‖ ≤ C pₖ ^ θ` with `0 ≤ θ ≤ 1 / 2`, then
`L(s, χ) = exp (abelSeries s + primePowerPart χ s)` for all `re s > 1 / 2`. -/
theorem exp_abelSeries_add_primePowerPart_of_le_rpow (hχ₁ : χ ≠ 1) {C θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ : θ ≤ 1 / 2)
    (hC : ∀ k, ‖∑ j ∈ range (k + 1), χ (nthPrime j)‖ ≤ C * (nthPrime k : ℝ) ^ θ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    exp (abelSeries (fun k ↦ χ (nthPrime k)) nthPrime s + χ.primePowerPart s) =
      LFunction χ s := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ
      (fun s ↦ exp (abelSeries (fun k ↦ χ (nthPrime k)) nthPrime s + χ.primePowerPart s))
      {s : ℂ | 1 / 2 < s.re} :=
    (((differentiableOn_abelSeries_of_le_rpow hθ₀ hC (Nat.prime_nth_prime 0).pos
      nthPrime_strictMono).mono fun s (hs : 1 / 2 < s.re) ↦
        show θ < s.re by linarith).add χ.differentiableOn_primePowerPart).cexp.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (LFunction χ) {s : ℂ | 1 / 2 < s.re} :=
    (differentiable_LFunction hχ₁).differentiableOn.analyticOnNhd hU
  have hfg : (fun s ↦ exp (abelSeries (fun k ↦ χ (nthPrime k)) nthPrime s +
      χ.primePowerPart s)) =ᶠ[𝓝 2] LFunction χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s (hs : 1 < s.re)
    rw [abelSeries_eq_tsum_of_le_rpow hθ₀ hC (fun _ ↦ χ.norm_le_one _)
      (Nat.prime_nth_prime 0).pos nthPrime_strictMono hs (by linarith)]
    exact χ.exp_primePart_add_primePowerPart hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num) hfg hs

/-- **Quantitative oscillation, prime-scale form.** For a nonprincipal quadratic character `χ`
and `θ < 1 / 2`, there is no constant `C` with `‖∑_{j ≤ k} χ(pⱼ)‖ ≤ C pₖ ^ θ` for all `k`. -/
theorem not_exists_norm_sum_succ_le_nthPrime_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {θ : ℝ}
    (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ k, ‖∑ j ∈ range (k + 1), χ (nthPrime j)‖ ≤ C * (nthPrime k : ℝ) ^ θ := by
  rintro ⟨C, hC⟩
  have hC' : ∀ k, ‖∑ j ∈ range (k + 1), χ (nthPrime j)‖ ≤
      |C| * (nthPrime k : ℝ) ^ max θ 0 := fun k ↦ (hC k).trans
    (mul_rpow_le_abs_mul_rpow_max (Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le) le_rfl)
  have hθ' : max θ 0 < 1 / 2 := max_lt hθ (by norm_num)
  set A := abelSeries (fun k ↦ χ (nthPrime k)) nthPrime
  -- `re (A σ)` is continuous at `σ = 1 / 2` (as `θ < 1 / 2`), while
  -- `re (primePowerPart χ σ) → ∞` as `σ → 1 / 2⁺`
  have hA : ContinuousAt (fun σ : ℝ ↦ (A σ).re) (1 / 2) :=
    continuous_re.continuousAt.comp (((differentiableOn_abelSeries_of_le_rpow (le_max_right θ 0)
      hC' (Nat.prime_nth_prime 0).pos nthPrime_strictMono).continuousOn.continuousAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (show max θ 0 < ((1 / 2 : ℝ) : ℂ).re by simpa using hθ'))).comp
      continuous_ofReal.continuousAt)
  exact not_tendsto_atTop_of_tendsto_nhds (χ.tendsto_exp_re_of_exp_eq_LFunction hχ₁
    (F := fun s ↦ A s + χ.primePowerPart s)
      fun σ (hσ : 1 / 2 < σ) ↦ exp_abelSeries_add_primePowerPart_of_le_rpow hχ₁
        (le_max_right _ _) hθ'.le hC' (by simpa using hσ))
    (Real.tendsto_exp_atTop.comp ((hA.tendsto.mono_left nhdsWithin_le_nhds).add_atTop
      (IsQuadratic.tendsto_re_primePowerPart χ hχ)))

/-- **Quantitative oscillation.** For a nonprincipal quadratic character `χ` and `θ < 1 / 2`,
the partial sums `∑_{k < n} χ(pₖ)` are not bounded by `C n ^ θ`. -/
theorem not_exists_norm_sum_le_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {θ : ℝ}
    (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ n, ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C * (n : ℝ) ^ θ := by
  rintro ⟨C, hC⟩
  refine not_exists_norm_sum_succ_le_nthPrime_rpow hχ hχ₁
    (max_lt hθ (by norm_num : (0 : ℝ) < 1 / 2))
    ⟨|C|, fun k ↦ (hC (k + 1)).trans (mul_rpow_le_abs_mul_rpow_max (by simp) ?_)⟩
  exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)

/-- **Quantitative oscillation, Landau form.** For a nonprincipal quadratic character `χ` and
`θ < 1 / 2`, `∑_{k < n} χ(pₖ)` is not `O(n ^ θ)`. -/
theorem not_isBigO_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ (fun n : ℕ ↦ ∑ k ∈ range n, χ (nthPrime k)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ θ :=
  fun h ↦ not_exists_norm_sum_le_rpow hχ hχ₁ (max_lt hθ (by norm_num))
    (exists_forall_norm_le_rpow_of_isBigO (by simp) h)

/-- For a nonprincipal quadratic character `χ` and every `ε > 0`, `∑_{k < n} χ(pₖ)` is not
`O(n ^ (1 / 2 - ε))`. -/
theorem not_isBigO_rpow_one_half_sub (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    ¬ (fun n : ℕ ↦ ∑ k ∈ range n, χ (nthPrime k)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 - ε) :=
  not_isBigO_rpow hχ hχ₁ (by linarith)

/-- **Quantitative oscillation over the primes below `x`.** For a nonprincipal quadratic
character `χ` and `θ < 1 / 2`, `∑_{p < x} χ(p)` is not bounded by `C x ^ θ`. -/
theorem not_exists_norm_sum_primesBelow_le_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {θ : ℝ}
    (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ x : ℕ, ‖∑ p ∈ Nat.primesBelow x, χ p‖ ≤ C * (x : ℝ) ^ θ := by
  rintro ⟨C, hC⟩
  refine not_exists_norm_sum_succ_le_nthPrime_rpow hχ hχ₁
    (max_lt hθ (by norm_num : (0 : ℝ) < 1 / 2)) ⟨|C| * 2 ^ max θ 0, fun k ↦ ?_⟩
  have hp : (1 : ℝ) ≤ nthPrime k := Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le
  have hcount : Nat.primeCounting' (nthPrime k + 1) = k + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k
  have h := hC (nthPrime k + 1)
  rw [χ.sum_primesBelow_eq, hcount] at h
  refine h.trans ((mul_rpow_le_abs_mul_rpow_max (by push_cast; linarith) le_rfl).trans ?_)
  rw [mul_assoc, ← Real.mul_rpow (by norm_num) (by positivity)]
  gcongr
  push_cast
  linarith

/-- For a nonprincipal quadratic character `χ` and `θ < 1 / 2`, `∑_{p < x} χ(p)` is not
`O(x ^ θ)`. -/
theorem not_isBigO_primesBelow_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {θ : ℝ}
    (hθ : θ < 1 / 2) :
    ¬ (fun x : ℕ ↦ ∑ p ∈ Nat.primesBelow x, χ p) =O[atTop] fun x : ℕ ↦ (x : ℝ) ^ θ :=
  fun h ↦ not_exists_norm_sum_primesBelow_le_rpow hχ hχ₁ (max_lt hθ (by norm_num))
    (exists_forall_norm_le_rpow_of_isBigO (by simp [Nat.primesBelow_zero]) h)

/-- For a nonprincipal quadratic character `χ` and `θ < 1 / 2`, `∑_{p < x} χ(p)` is not bounded
by `C π'(x) ^ θ`, where `π'(x)` is the number of primes below `x`. -/
theorem not_exists_norm_sum_primesBelow_le_primeCounting'_rpow (hχ : χ.IsQuadratic)
    (hχ₁ : χ ≠ 1) {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ x : ℕ,
      ‖∑ p ∈ Nat.primesBelow x, χ p‖ ≤ C * (Nat.primeCounting' x : ℝ) ^ θ := by
  rintro ⟨C, h⟩
  refine not_exists_norm_sum_le_rpow hχ hχ₁ hθ ⟨C, fun n ↦ ?_⟩
  simpa [sum_primesBelow_eq, Nat.primeCounting'_nth_eq] using h (nthPrime n)

/-- **Log-power refinement, prime-scale form.** For a nonprincipal quadratic character `χ` and
`A > 1`, there is no constant `C` with `‖∑_{j ≤ k} χ(pⱼ)‖ ≤ C pₖ ^ (1 / 2) / (log pₖ) ^ A` for all
`k`. Such a bound makes the Abel series converge uniformly up to the line `re s = 1 / 2`
(`continuousOn_abelSeries_of_le_rpow_div_log_rpow`), so it stays bounded as `σ → 1 / 2⁺` while the
prime-power part blows up. -/
theorem not_exists_norm_sum_succ_le_nthPrime_rpow_div_log_rpow (hχ : χ.IsQuadratic)
    (hχ₁ : χ ≠ 1) {A : ℝ} (hA : 1 < A) :
    ¬ ∃ C : ℝ, ∀ k, ‖∑ j ∈ range (k + 1), χ (nthPrime j)‖ ≤
      C * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ A := by
  rintro ⟨C, hC⟩
  have hq₀ : 2 ≤ nthPrime 0 := (Nat.prime_nth_prime 0).two_le
  -- the bound `‖S (k + 1)‖ ≤ C' pₖ ^ (1 / 2)`, enough for holomorphy on `re s > 1 / 2`
  have hC' : ∀ k, ‖∑ j ∈ range (k + 1), χ (nthPrime j)‖ ≤
      |C| / Real.log 2 ^ A * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) := fun k ↦ by
    have hp : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast (Nat.prime_nth_prime k).two_le
    have hl : Real.log 2 ^ A ≤ Real.log (nthPrime k) ^ A :=
      Real.rpow_le_rpow (Real.log_nonneg one_le_two) (Real.log_le_log two_pos hp) (by linarith)
    have hl0 : 0 < Real.log 2 ^ A := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) A
    refine (hC k).trans ?_
    calc C * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ A ≤
          |C| * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ A := by
          gcongr
          exact le_abs_self C
      _ ≤ |C| * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log 2 ^ A :=
          div_le_div_of_nonneg_left (by positivity) hl0 hl
      _ = _ := by ring
  set F := abelSeries (fun k ↦ χ (nthPrime k)) nthPrime
  -- `re (F σ) → re (F (1 / 2))` as `σ → 1 / 2⁺`, while `re (primePowerPart χ σ) → ∞`
  have hF : Tendsto (fun σ : ℝ ↦ (F σ).re) (𝓝[>] (1 / 2)) (𝓝 (F ((1 / 2 : ℝ) : ℂ)).re) :=
    continuous_re.continuousAt.tendsto.comp
      (((continuousOn_abelSeries_of_le_rpow_div_log_rpow hA hC hq₀ nthPrime_strictMono
        Nat.nth_prime_succ_le_two_mul) (1 / 2) ⟨le_rfl, by norm_num⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT (by norm_num))).tendsto
  exact not_tendsto_atTop_of_tendsto_nhds (χ.tendsto_exp_re_of_exp_eq_LFunction hχ₁
    (F := fun s ↦ F s + χ.primePowerPart s)
      fun σ (hσ : 1 / 2 < σ) ↦ exp_abelSeries_add_primePowerPart_of_le_rpow hχ₁
        (by norm_num) le_rfl hC' (by simpa using hσ))
    (Real.tendsto_exp_atTop.comp (hF.add_atTop (IsQuadratic.tendsto_re_primePowerPart χ hχ)))

/-- For a nonprincipal quadratic character `χ` and `A > 1`, `∑_{j ≤ k} χ(pⱼ)` is not
`O(pₖ ^ (1 / 2) / (log pₖ) ^ A)`. -/
theorem not_isBigO_sum_succ_nthPrime_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1)
    {A : ℝ} (hA : 1 < A) :
    ¬ (fun k ↦ ∑ j ∈ range (k + 1), χ (nthPrime j)) =O[atTop]
      fun k ↦ (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ A := by
  intro h
  obtain ⟨C, hC⟩ := exists_forall_norm_le_mul_of_isBigO (fun k ↦ rpow_div_log_rpow_pos
    (by exact_mod_cast (Nat.prime_nth_prime k).one_lt) _ _) h
  exact not_exists_norm_sum_succ_le_nthPrime_rpow_div_log_rpow hχ hχ₁ hA
    ⟨C, fun k ↦ (hC k).trans_eq (mul_div_assoc _ _ _).symm⟩

/-- For a nonprincipal quadratic character `χ` and `A > 1 / 2`, `∑_{j ≤ k} χ(pⱼ)` is not
`O(k ^ (1 / 2) / (log k) ^ A)`. This reduces to the prime-scale form with exponent `A + 1 / 2 > 1`
via `k log pₖ ≤ 5 pₖ` and `log pₖ ≤ 2 log k` for large `k` (Chebyshev's bounds). -/
theorem not_isBigO_sum_succ_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1)
    {A : ℝ} (hA : 1 / 2 < A) :
    ¬ (fun k ↦ ∑ j ∈ range (k + 1), χ (nthPrime j)) =O[atTop]
      fun k : ℕ ↦ (k : ℝ) ^ (1 / 2 : ℝ) / Real.log k ^ A := by
  refine fun h ↦ not_isBigO_sum_succ_nthPrime_rpow_div_log_rpow hχ hχ₁ (A := A + 1 / 2)
    (by linarith) (h.trans (.of_bound ((5 : ℝ) ^ (1 / 2 : ℝ) * 2 ^ A) ?_))
  filter_upwards [eventually_ge_atTop 4096] with k hk
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hkp : (k : ℝ) ≤ nthPrime k := by
    exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)
  have hlk := Real.log_pos hk1
  have hL := Real.log_pos (hk1.trans_le hkp)
  have hlog := Nat.log_nth_prime_le_two_mul_log hk
  have hU := Nat.succ_mul_log_nth_prime_le k
  rw [Real.norm_of_nonneg (rpow_div_log_rpow_pos hk1 _ _).le,
    Real.norm_of_nonneg (rpow_div_log_rpow_pos (hk1.trans_le hkp) _ _).le, mul_div_assoc',
    div_le_div_iff₀ (Real.rpow_pos_of_pos hlk A) (Real.rpow_pos_of_pos hL _),
    Real.rpow_add hL]
  have h1 : (k : ℝ) ^ (1 / 2 : ℝ) * Real.log (nthPrime k) ^ (1 / 2 : ℝ) ≤
      (5 : ℝ) ^ (1 / 2 : ℝ) * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) hL.le, ← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
  have h2 : Real.log (nthPrime k) ^ A ≤ 2 ^ A * Real.log k ^ A := by
    rw [← Real.mul_rpow (by norm_num) hlk.le]
    exact Real.rpow_le_rpow hL.le hlog (by linarith)
  calc (k : ℝ) ^ (1 / 2 : ℝ) * (Real.log (nthPrime k) ^ A * Real.log (nthPrime k) ^ (1 / 2 : ℝ))
      = (k : ℝ) ^ (1 / 2 : ℝ) * Real.log (nthPrime k) ^ (1 / 2 : ℝ) *
          Real.log (nthPrime k) ^ A := by ring
    _ ≤ (5 : ℝ) ^ (1 / 2 : ℝ) * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) * (2 ^ A * Real.log k ^ A) := by
        gcongr
    _ = _ := by ring

/-- **Log-power refinement, Landau form.** For a nonprincipal quadratic character `χ` and
`A > 1 / 2`, `∑_{k < n} χ(pₖ)` is not `O(n ^ (1 / 2) / (log n) ^ A)`. -/
theorem not_isBigO_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {A : ℝ}
    (hA : 1 / 2 < A) :
    ¬ (fun n ↦ ∑ k ∈ range n, χ (nthPrime k)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ A := by
  refine fun h ↦ not_isBigO_sum_succ_rpow_div_log_rpow hχ hχ₁ hA
    ((h.comp_tendsto (tendsto_add_atTop_nat 1)).trans (.of_bound (2 ^ (1 / 2 : ℝ)) ?_))
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [Real.norm_of_nonneg (rpow_div_log_rpow_pos (by linarith) _ _).le,
    Real.norm_of_nonneg (rpow_div_log_rpow_pos hk1 _ _).le, mul_div_assoc',
    ← Real.mul_rpow (by norm_num) (by positivity)]
  exact div_le_div₀ (by positivity) (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num))
    (Real.rpow_pos_of_pos (Real.log_pos hk1) A)
    (Real.rpow_le_rpow (Real.log_nonneg hk1.le) (Real.log_le_log (by linarith) (by linarith))
      (by linarith))

/-- **Log-power refinement.** For a nonprincipal quadratic character `χ` and `A > 1 / 2`, there is
no constant `C` with `‖∑_{k < n} χ(pₖ)‖ ≤ C n ^ (1 / 2) / (log n) ^ A` for all `n ≥ 2`. -/
theorem not_exists_norm_sum_le_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {A : ℝ}
    (hA : 1 / 2 < A) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C * (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ A := by
  rintro ⟨C, hC⟩
  refine not_isBigO_rpow_div_log_rpow hχ hχ₁ hA (.of_bound C ?_)
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [Real.norm_of_nonneg (rpow_div_log_rpow_pos (by exact_mod_cast hn) _ _).le, ← mul_div_assoc]
  exact hC n hn

/-- **Log-power refinement over the primes below `x`, Landau form.** For a nonprincipal quadratic
character `χ` and `A > 1`, `∑_{p < x} χ(p)` is not `O(x ^ (1 / 2) / (log x) ^ A)`. -/
theorem not_isBigO_primesBelow_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {A : ℝ}
    (hA : 1 < A) :
    ¬ (fun x : ℕ ↦ ∑ p ∈ Nat.primesBelow x, χ p) =O[atTop]
      fun x : ℕ ↦ (x : ℝ) ^ (1 / 2 : ℝ) / Real.log x ^ A := by
  intro h
  have h' := h.comp_tendsto ((tendsto_add_atTop_nat 1).comp nthPrime_strictMono.tendsto_atTop)
  refine not_isBigO_sum_succ_nthPrime_rpow_div_log_rpow hχ hχ₁ hA ?_
  have e : (fun k ↦ ∑ j ∈ range (k + 1), χ (nthPrime j)) =
      (fun x : ℕ ↦ ∑ p ∈ Nat.primesBelow x, χ p) ∘ fun k ↦ nthPrime k + 1 := by
    ext k
    rw [Function.comp_apply, χ.sum_primesBelow_eq, show Nat.primeCounting' (nthPrime k + 1) =
      k + 1 from Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k]
  rw [e]
  refine h'.trans (.of_bound (2 ^ (1 / 2 : ℝ)) (Eventually.of_forall fun k ↦ ?_))
  have hp : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast (Nat.prime_nth_prime k).two_le
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [Real.norm_of_nonneg (rpow_div_log_rpow_pos (by linarith) _ _).le,
    Real.norm_of_nonneg (rpow_div_log_rpow_pos (by linarith) _ _).le, mul_div_assoc',
    ← Real.mul_rpow (by norm_num) (by positivity)]
  exact div_le_div₀ (by positivity) (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num))
    (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A)
    (Real.rpow_le_rpow (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith)
      (by linarith)) (by linarith))

/-- **Log-power refinement over the primes below `x`.** For a nonprincipal quadratic character `χ`
and `A > 1`, there is no constant `C` with `‖∑_{p < x} χ(p)‖ ≤ C x ^ (1 / 2) / (log x) ^ A` for all
`x ≥ 2`. -/
theorem not_exists_norm_sum_primesBelow_le_rpow_div_log_rpow (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1)
    {A : ℝ} (hA : 1 < A) :
    ¬ ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      ‖∑ p ∈ Nat.primesBelow x, χ p‖ ≤ C * (x : ℝ) ^ (1 / 2 : ℝ) / Real.log x ^ A := by
  rintro ⟨C, hC⟩
  refine not_isBigO_primesBelow_rpow_div_log_rpow hχ hχ₁ hA (.of_bound C ?_)
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [Real.norm_of_nonneg (rpow_div_log_rpow_pos (by exact_mod_cast hx) _ _).le, ← mul_div_assoc]
  exact hC x hx

end DirichletCharacter.IsQuadratic

namespace RokickiConstant

open Real

/-- The digit sums of `ρ` are the partial sums of `χ₄` over the primes:
`∑_{k ≤ n} χ₄(pₖ) = ∑_{k < n} (1 - 2 dₖ)`, the term `χ₄(p₀) = χ₄(2) = 0` dropping out. -/
theorem sum_range_succ_chi4_nthPrime (n : ℕ) :
    ∑ k ∈ range (n + 1), chi4 (nthPrime k) =
      ((∑ k ∈ range n, (1 - 2 * (rokickiDigit k : ℝ)) : ℝ) : ℂ) := by
  rw [sum_range_succ', Nat.nth_prime_zero_eq_two]
  push_cast
  simp only [chi4_two, add_zero]
  exact sum_congr rfl fun k _ ↦ chi4_oddPrime k

/-- `∑_{k < n} (1 - 2 dₖ)` is the number of digits `0` minus the number of digits `1` among the
first `n` binary digits `dₖ` of `ρ`. -/
theorem sum_one_sub_two_mul_rokickiDigit (n : ℕ) :
    ∑ k ∈ range n, (1 - 2 * (rokickiDigit k : ℝ)) =
      (#{k ∈ range n | rokickiDigit k = 0} : ℝ) - #{k ∈ range n | rokickiDigit k = 1} := by
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (rokickiDigit_le_one k) with h | h <;> norm_num [h]

/-- **Quantitative oscillation of the digits of `ρ`.** For `θ < 1 / 2`, the imbalance
`∑_{k < n} (1 - 2 dₖ)` between the digits `0` and `1` among the first `n` binary digits of `ρ` is
not bounded by `C n ^ θ`. -/
theorem not_exists_abs_sum_rokickiDigit_le_rpow {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ n, |∑ k ∈ range n, (1 - 2 * (rokickiDigit k : ℝ))| ≤ C * (n : ℝ) ^ θ := by
  rintro ⟨C, hC⟩
  have hχ : chi4.IsQuadratic := ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)
  refine DirichletCharacter.IsQuadratic.not_exists_norm_sum_succ_le_nthPrime_rpow hχ chi4_ne_one
    (max_lt hθ (by norm_num : (0 : ℝ) < 1 / 2)) ⟨|C|, fun k ↦ ?_⟩
  rw [sum_range_succ_chi4_nthPrime, Complex.norm_real, Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (by norm_num) _)
  · exact (hC k).trans (mul_rpow_le_abs_mul_rpow_max (Nat.one_le_cast.2 hk)
      (by exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)))

/-- **Quantitative oscillation of the digits of `ρ`, Landau form.** For `θ < 1 / 2`, the number
of digits `0` minus the number of digits `1` among the first `n` binary digits of `ρ` is not
`O(n ^ θ)`. -/
theorem not_isBigO_card_rokickiDigit_rpow {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ (fun n : ℕ ↦ (#{k ∈ range n | rokickiDigit k = 0} : ℝ) -
      #{k ∈ range n | rokickiDigit k = 1}) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ θ := by
  intro h
  simp only [← sum_one_sub_two_mul_rokickiDigit] at h
  obtain ⟨C, hC⟩ := exists_forall_norm_le_rpow_of_isBigO (by simp) h
  exact not_exists_abs_sum_rokickiDigit_le_rpow (max_lt hθ (by norm_num)) ⟨C, hC⟩

/-- **Log-power refinement for the digits of `ρ`, Landau form.** For `A > 1 / 2`, the number of
digits `0` minus the number of digits `1` among the first `n` binary digits of `ρ` is not
`O(n ^ (1 / 2) / (log n) ^ A)`. -/
theorem not_isBigO_card_rokickiDigit_rpow_div_log_rpow {A : ℝ} (hA : 1 / 2 < A) :
    ¬ (fun n : ℕ ↦ (#{k ∈ range n | rokickiDigit k = 0} : ℝ) -
      #{k ∈ range n | rokickiDigit k = 1}) =O[atTop]
        fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ A := by
  intro h
  simp only [← sum_one_sub_two_mul_rokickiDigit] at h
  have hχ : chi4.IsQuadratic := ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)
  refine DirichletCharacter.IsQuadratic.not_isBigO_sum_succ_rpow_div_log_rpow hχ chi4_ne_one hA
    (Asymptotics.isBigO_norm_left.1 ?_)
  simpa only [sum_range_succ_chi4_nthPrime, Complex.norm_real] using h.norm_left

/-- **Log-power refinement for the digits of `ρ`.** For `A > 1 / 2`, there is no constant `C` with
`|∑_{k < n} (1 - 2 dₖ)| ≤ C n ^ (1 / 2) / (log n) ^ A` for all `n ≥ 2`. -/
theorem not_exists_abs_sum_rokickiDigit_le_rpow_div_log_rpow {A : ℝ} (hA : 1 / 2 < A) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |∑ k ∈ range n, (1 - 2 * (rokickiDigit k : ℝ))| ≤
        C * (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ A := by
  rintro ⟨C, hC⟩
  refine not_isBigO_card_rokickiDigit_rpow_div_log_rpow hA (.of_bound C ?_)
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [Real.norm_of_nonneg (rpow_div_log_rpow_pos (by exact_mod_cast hn) _ _).le, ← mul_div_assoc,
    ← sum_one_sub_two_mul_rokickiDigit, Real.norm_eq_abs]
  exact hC n hn

end RokickiConstant
