/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import RokickiConstant.EulerProduct

/-!
# The Euler product of `L(s, χ)` for an arbitrary Dirichlet character

This generalizes `RokickiConstant.EulerProduct` from `χ₄` to any Dirichlet character `χ`
modulo `q`, and from the odd primes to all primes `p₀ = 2 < p₁ = 3 < ⋯`, written
`Nat.nth Nat.Prime k`. We set `zₖ(s) = χ(pₖ) pₖ ^ (-s)`, `primePart χ s = ∑ₖ zₖ(s)` and
`primePowerPart χ s = ∑ₖ (-log (1 - zₖ(s)) - zₖ(s))`, so that
`L(s, χ) = exp (primePart χ s + primePowerPart χ s)` for `re s > 1`.

The prime-power part is holomorphic on `re s > 1 / 2` and bounded on `re s ≥ 1` for every `χ`.
Its real part tends to `+∞` as `s → 1 / 2⁺` along the reals when `χ` is *quadratic*, that is,
takes values in `{0, 1, -1}`: then `χ(p)² = 1` for all but the finitely many primes dividing
`q`, and the `m = 2` terms `∑ₚ p ^ (-2σ) / 2` of the prime-power part diverge as `σ → 1 / 2⁺`.

## Main definitions

* `DirichletCharacter.primeTerm χ k s`: `χ(pₖ) pₖ ^ (-s)`.
* `DirichletCharacter.primePart χ s`, `DirichletCharacter.primePowerPart χ s`.

## Main statements

* `DirichletCharacter.exp_primePart_add_primePowerPart`: the Euler product.
* `DirichletCharacter.differentiableOn_primePowerPart`, `exists_norm_primePowerPart_le`.
* `DirichletCharacter.IsQuadratic.tendsto_re_primePowerPart`: the blow-up at `1 / 2`.
* `tendsto_tsum_nthPrime_rpow_neg`: `∑ₖ pₖ ^ (-σ) → +∞` as `σ → 1⁺`.

## Tags

Dirichlet character, Euler product, quadratic character
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

section Primes

/-- `k ↦ pₖ` is strictly increasing. -/
theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

/-- The enumeration `k ↦ pₖ` of the primes, as an equivalence `ℕ ≃ Nat.Primes`. -/
noncomputable def nthPrimeEquiv : ℕ ≃ Nat.Primes :=
  Equiv.ofBijective (fun k ↦ ⟨nthPrime k, Nat.prime_nth_prime k⟩)
    ⟨fun _ _ h ↦ Nat.nth_injective Nat.infinite_setOfPred_prime (congrArg Subtype.val h),
      fun p ↦ ⟨Nat.count Nat.Prime p, Subtype.ext (Nat.nth_count p.2)⟩⟩

/-- `∑ₖ 1 / pₖ` diverges. -/
theorem not_summable_nthPrime_inv : ¬ Summable fun k : ℕ ↦ ((nthPrime k : ℝ))⁻¹ := by
  intro h
  apply Nat.Primes.not_summable_one_div
  rw [← nthPrimeEquiv.summable_iff]
  exact h.congr fun k ↦ (one_div _).symm

/-- `∑ₖ pₖ ^ r` converges for `r < -1`. -/
theorem summable_nthPrime_rpow {r : ℝ} (hr : r < -1) :
    Summable fun k : ℕ ↦ (nthPrime k : ℝ) ^ r :=
  summable_natCast_rpow (Nat.prime_nth_prime 0).pos nthPrime_strictMono hr

/-- `∑ₖ pₖ ^ (-σ) → +∞` as `σ → 1⁺`. -/
theorem tendsto_tsum_nthPrime_rpow_neg :
    Tendsto (fun σ : ℝ ↦ ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ)) (𝓝[>] (1 : ℝ)) atTop := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k ↦ by positivity)).mp not_summable_nthPrime_inv
  refine tendsto_atTop.mpr fun M ↦ ?_
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp hdiv (M + 1)).exists
  have hcont : Tendsto (fun σ : ℝ ↦ ∑ k ∈ range N, (nthPrime k : ℝ) ^ (-σ)) (𝓝 1)
      (𝓝 (∑ k ∈ range N, (nthPrime k : ℝ)⁻¹)) := by
    refine tendsto_finsetSum _ fun k _ ↦ ?_
    have := (Real.continuousAt_const_rpow (b := -1)
      (Nat.cast_pos.2 (Nat.prime_nth_prime k).pos).ne').tendsto.comp (tendsto_neg (1 : ℝ))
    simpa [Function.comp_def, Real.rpow_neg_one] using this
  filter_upwards [nhdsWithin_le_nhds (hcont.eventually (lt_mem_nhds (show M < _ by linarith))),
    self_mem_nhdsWithin] with σ hσ (hσ1 : 1 < σ)
  exact hσ.le.trans (Summable.sum_le_tsum _ (fun k _ ↦ by positivity)
    (summable_nthPrime_rpow (by linarith)))

/-- A sum over the primes is a sum over `k` of the `k`-th prime. -/
theorem tsum_primes_eq_tsum_nthPrime {F : Nat.Primes → ℂ} (hF : Summable F) :
    ∑' p : Nat.Primes, F p = ∑' k : ℕ, F ⟨nthPrime k, Nat.prime_nth_prime k⟩ := by
  exact ((nthPrimeEquiv.hasSum_iff.2 hF.hasSum).tsum_eq).symm

end Primes

namespace DirichletCharacter

variable {q : ℕ} (χ : DirichletCharacter ℂ q)

/-- The term `zₖ(s) = χ(pₖ) pₖ ^ (-s)` of the Dirichlet series of `χ` over the primes. -/
noncomputable def primeTerm (k : ℕ) (s : ℂ) : ℂ := χ (nthPrime k) * (nthPrime k : ℂ) ^ (-s)

/-- `‖zₖ(s)‖ ≤ pₖ ^ (-re s)`. -/
theorem norm_primeTerm_le (k : ℕ) (s : ℂ) : ‖χ.primeTerm k s‖ ≤ (nthPrime k : ℝ) ^ (-s.re) := by
  rw [primeTerm, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.prime_nth_prime k).pos, neg_re]
  exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)

/-- `‖zₖ(s)‖ ≤ 3 / 4` when `re s > 1 / 2`. -/
theorem norm_primeTerm_le_three_quarters (k : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖χ.primeTerm k s‖ ≤ 3 / 4 := by
  have h2 : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast (Nat.prime_nth_prime k).two_le
  have h : ‖χ.primeTerm k s‖ ^ 2 ≤ 1 / 2 := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (χ.norm_primeTerm_le k s) 2).trans ?_
    rw [← Real.rpow_mul_natCast (by positivity)]
    calc _ ≤ (nthPrime k : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by push_cast; linarith)
      _ ≤ 1 / 2 := by rw [Real.rpow_neg_one, one_div]; exact inv_anti₀ (by norm_num) h2
  nlinarith [norm_nonneg (χ.primeTerm k s)]

/-- The prime part `∑ₖ χ(pₖ) pₖ ^ (-s)` of the logarithm of the Euler product. -/
noncomputable def primePart (s : ℂ) : ℂ := ∑' k : ℕ, χ.primeTerm k s

/-- The prime-power part `∑ₖ (-log (1 - zₖ(s)) - zₖ(s))` of the logarithm of the Euler product,
the contribution of the prime powers `pₖ ^ m`, `m ≥ 2`. -/
noncomputable def primePowerPart (s : ℂ) : ℂ :=
  ∑' k : ℕ, (-log (1 - χ.primeTerm k s) - χ.primeTerm k s)

/-- For `1 / 2 < σ₀ ≤ re s`, the `k`-th term of `primePowerPart χ s` has norm at most
`2 pₖ ^ (-2σ₀)`. -/
theorem norm_primePowerPart_term_le (k : ℕ) {σ₀ : ℝ} {s : ℂ} (hσ₀ : 1 / 2 < σ₀)
    (hs : σ₀ ≤ s.re) :
    ‖-log (1 - χ.primeTerm k s) - χ.primeTerm k s‖ ≤ 2 * (nthPrime k : ℝ) ^ (-(2 * σ₀)) := by
  refine (RokickiConstant.norm_neg_log_one_sub_sub_le
    (χ.norm_primeTerm_le_three_quarters k (by linarith))).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  refine (pow_le_pow_left₀ (norm_nonneg _) (χ.norm_primeTerm_le k s) 2).trans ?_
  rw [← Real.rpow_mul_natCast (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_le
    (Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le) (by push_cast; linarith)

/-- The prime part converges absolutely for `re s > 1`. -/
theorem summable_primeTerm {s : ℂ} (hs : 1 < s.re) : Summable fun k ↦ χ.primeTerm k s :=
  summable_mul_cpow_neg (C := 1) (fun _ ↦ χ.norm_le_one _) (Nat.prime_nth_prime 0).pos
    nthPrime_strictMono hs

/-- The prime-power part converges absolutely for `re s > 1 / 2`. -/
theorem summable_primePowerPart_term {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun k ↦ -log (1 - χ.primeTerm k s) - χ.primeTerm k s :=
  .of_norm_bounded ((summable_nthPrime_rpow (by linarith)).mul_left 2)
    fun k ↦ χ.norm_primePowerPart_term_le k hs le_rfl

variable [NeZero q] in
/-- **Euler product** for `L(s, χ)` in exponential form, `re s > 1`. -/
theorem exp_primePart_add_primePowerPart {s : ℂ} (hs : 1 < s.re) :
    exp (χ.primePart s + χ.primePowerPart s) = LFunction χ s := by
  have hsum : Summable fun p : Nat.Primes ↦ -log (1 - χ p * (p : ℂ) ^ (-s)) :=
    ((summable_dirichletSummand χ hs).of_norm.comp_injective
      Subtype.val_injective).clog_one_sub.neg
  rw [LFunction_eq_LSeries χ hs, ← LSeries_eulerProduct_exp_log χ hs,
    tsum_primes_eq_tsum_nthPrime hsum, primePart, primePowerPart,
    ← (χ.summable_primeTerm hs).tsum_add (χ.summable_primePowerPart_term (by linarith))]
  simp [primeTerm]

/-- The prime-power part is holomorphic on `re s > 1 / 2`. -/
theorem differentiableOn_primePowerPart :
    DifferentiableOn ℂ χ.primePowerPart {s : ℂ | 1 / 2 < s.re} := by
  intro s₀ (hs₀ : 1 / 2 < s₀.re)
  obtain ⟨σ₀, hσ₀, hσ₀s⟩ := exists_between hs₀
  have hU : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const continuous_re
  refine (DifferentiableOn.differentiableAt ?_ (hU.mem_nhds hσ₀s)).differentiableWithinAt
  refine differentiableOn_tsum_of_summable_norm
    ((summable_nthPrime_rpow (r := -(2 * σ₀)) (by linarith)).mul_left 2)
    (fun k s (hs : σ₀ < s.re) ↦ ?_) hU fun k s (hs : σ₀ < s.re) ↦
      χ.norm_primePowerPart_term_le k hσ₀ hs.le
  have hd : DifferentiableAt ℂ (χ.primeTerm k) s := ((differentiableAt_id.neg).const_cpow
    (Or.inl (Nat.cast_ne_zero.2 (Nat.prime_nth_prime k).ne_zero))).const_mul _
  exact (((hd.const_sub 1).clog (RokickiConstant.one_sub_mem_slitPlane (by
    linarith [χ.norm_primeTerm_le_three_quarters k (s := s) (by linarith)]))).neg.sub
      hd).differentiableWithinAt

/-- The prime-power part is bounded on the closed half-plane `re s ≥ 1`. -/
theorem exists_norm_primePowerPart_le :
    ∃ M : ℝ, ∀ s : ℂ, 1 ≤ s.re → ‖χ.primePowerPart s‖ ≤ M :=
  ⟨_, fun _ hs ↦ tsum_of_norm_bounded ((summable_nthPrime_rpow (r := -(2 * 1))
    (by norm_num)).mul_left 2).hasSum fun k ↦ χ.norm_primePowerPart_term_le k (by norm_num) hs⟩

/-- A quadratic character vanishes at `pₖ` only for the finitely many primes dividing `q`:
`χ(pₖ) = 0` if and only if `pₖ ∣ q`. -/
theorem apply_nthPrime_eq_zero_iff (k : ℕ) : χ (nthPrime k) = 0 ↔ nthPrime k ∣ q := by
  rw [← not_iff_not, ← ZMod.isUnit_prime_iff_not_dvd (Nat.prime_nth_prime k)]
  refine ⟨fun h ↦ by_contra fun hu ↦ h (χ.map_nonunit hu), fun h h0 ↦ ?_⟩
  simpa [h0] using χ.unit_norm_eq_one h.unit

variable [NeZero q] in
/-- `χ(pₖ) ≠ 0` for all sufficiently large `k`. -/
theorem eventually_apply_nthPrime_ne_zero : ∀ᶠ k in atTop, χ (nthPrime k) ≠ 0 := by
  filter_upwards [eventually_ge_atTop q] with k hk
  rw [Ne, apply_nthPrime_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (NeZero.pos q) h
  have := Nat.add_two_le_nth_prime k
  omega

/-- For a quadratic character, `χ(pₖ)² ∈ {0, 1}`, and it is `1` unless `pₖ ∣ q`. -/
theorem IsQuadratic.sq_apply_nthPrime (hχ : χ.IsQuadratic) (k : ℕ) :
    χ (nthPrime k) ^ 2 = if nthPrime k ∣ q then 0 else 1 := by
  have hz := χ.apply_nthPrime_eq_zero_iff k
  split_ifs with hd
  · simp [hz.2 hd]
  · rcases hχ (nthPrime k) with h | h | h
    · exact absurd (hz.1 h) hd
    · simp [h]
    · simp [h]

variable [NeZero q] in
/-- For a quadratic character and real `σ > 1 / 2`, the real part of `primePowerPart χ σ` is at
least `∑ₖ pₖ ^ (-2σ) / 2` minus a constant depending only on `q`. -/
theorem IsQuadratic.le_re_primePowerPart (hχ : χ.IsQuadratic) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' k : ℕ, (nthPrime k : ℝ) ^ (-(2 * σ))) / 2 - (q.primeFactors.card : ℝ) / 2 -
        2 * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-3 / 2 : ℝ) ≤
      (χ.primePowerPart σ).re := by
  have hs : 1 / 2 < (σ : ℂ).re := by simpa using hσ
  set a : ℕ → ℝ := fun k ↦ (nthPrime k : ℝ) ^ (-(2 * σ))
  set d : ℕ → ℝ := fun k ↦ if nthPrime k ∣ q then a k / 2 else 0
  have ha : Summable a := summable_nthPrime_rpow (by linarith)
  have ha1 : ∀ k, a k ≤ 1 := fun k ↦ Real.rpow_le_one_of_one_le_of_nonpos
    (Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le) (by linarith)
  have hd0 : ∀ k, 0 ≤ d k := fun k ↦ by simp only [d]; split_ifs <;> positivity
  have hd : Summable d := (ha.div_const 2).of_nonneg_of_le hd0 fun k ↦ by
    simp only [d]; split_ifs <;> [exact le_rfl; positivity]
  -- The terms with `pₖ ∣ q` contribute at most `#q.primeFactors / 2`.
  have hdq : ∑' k, d k ≤ (q.primeFactors.card : ℝ) / 2 := by
    refine Real.tsum_le_of_sum_le hd0 fun t ↦ ?_
    rw [← Finset.sum_filter]
    calc _ ≤ #(t.filter fun k ↦ nthPrime k ∣ q) • (1 / 2 : ℝ) :=
          Finset.sum_le_card_nsmul _ _ _ fun k _ ↦ by linarith [ha1 k]
      _ ≤ #q.primeFactors • (1 / 2 : ℝ) := by
          refine nsmul_le_nsmul_left (by norm_num) (Finset.card_le_card_of_injOn _
            (fun k hk ↦ ?_) (nthPrime_strictMono.injective.injOn))
          exact Nat.mem_primeFactors.2 ⟨Nat.prime_nth_prime k, (Finset.mem_filter.1 hk).2,
            NeZero.ne q⟩
      _ = _ := by rw [nsmul_eq_mul]; ring
  suffices h : (∑' k, a k) / 2 - ∑' k, d k - 2 * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-3 / 2 : ℝ) ≤
      (χ.primePowerPart σ).re by linarith
  refine hasSum_le (fun k ↦ ?_) (((ha.hasSum.div_const 2).sub hd.hasSum).sub
    ((summable_nthPrime_rpow (by norm_num)).hasSum.mul_left 2))
    (hasSum_re (χ.summable_primePowerPart_term hs).hasSum)
  have hp : (1 : ℝ) ≤ nthPrime k := Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le
  have hw : χ.primeTerm k σ = χ (nthPrime k) * (((nthPrime k : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [primeTerm, ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  have h2 : (χ.primeTerm k σ ^ 2 / 2).re = a k / 2 - d k := by
    rw [hw, mul_pow, IsQuadratic.sq_apply_nthPrime χ hχ, ← ofReal_pow,
      ← Real.rpow_mul_natCast (by positivity)]
    simp only [d, a]
    split_ifs <;> simp [mul_comm σ]
  have h3 : ‖χ.primeTerm k σ‖ ^ 3 ≤ (nthPrime k : ℝ) ^ (-3 / 2 : ℝ) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (χ.norm_primeTerm_le k σ) 3).trans ?_
    rw [← Real.rpow_mul_natCast (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hp (by push_cast; linarith)
  have h := abs_le.1 ((abs_re_le_norm _).trans (RokickiConstant.norm_neg_log_one_sub_sub_sub_le
    (χ.norm_primeTerm_le_three_quarters k hs)))
  simp only [sub_re] at h h2 ⊢
  linarith

variable [NeZero q] in
/-- For a quadratic character, `re (primePowerPart χ σ) → +∞` as `σ → 1 / 2⁺`. -/
theorem IsQuadratic.tendsto_re_primePowerPart (hχ : χ.IsQuadratic) :
    Tendsto (fun σ : ℝ ↦ (χ.primePowerPart σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop := by
  have h2 : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝[>] (1 / 2)) (𝓝[>] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const_mul 2).tendsto' _ _ (by norm_num)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun σ (hσ : 1 / 2 < σ) ↦
        show 1 < 2 * σ by linarith⟩
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _
    (-((q.primeFactors.card : ℝ) / 2 + 2 * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-3 / 2 : ℝ)))
    ((tendsto_tsum_nthPrime_rpow_neg.comp h2).atTop_div_const two_pos))
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 / 2 < σ)
  have := IsQuadratic.le_re_primePowerPart χ hχ hσ
  simp only [Function.comp_apply] at this ⊢
  linarith

end DirichletCharacter
