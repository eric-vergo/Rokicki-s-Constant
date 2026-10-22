/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.Analytic.Order
import RokickiConstant.General.SingleClass

/-!
# Unions of residue classes of primes

Let `q ≥ 3`, let `A` be a set of units modulo `q`, and let `p₀ = 2 < p₁ < ⋯` be the primes. We
study the digit `dₖ = [pₖ mod q ∈ A]`, generalizing `RokickiConstant.General.SingleClass` (the
case `A = {a}`). Write `φ = φ(q)`, `c_χ = ∑_{a ∈ A} χ(a⁻¹)` (`unionCoeff`) and
`ν(A) = #{r mod q | r² ∈ A}`. The weight `e(n) = [n ∈ A] - |A| 1(n) / φ` (`unionWeight`) satisfies
`φ e(n) = ∑_{χ ≠ 1} c_χ χ(n)`, and the proof of the single-class theorem gives:

* **the multiplicity relation** (`sum_unionCoeff_mul_analyticOrderNatAt_eq_of_eventuallyPeriodic`):
  if `d` is eventually periodic, then
  `∑_{χ ≠ 1} c_χ ord_{s = 1/2} L(s, χ) = (|A| - ν(A)) / 2`.

The left side is an algebraic integer and `ν(A)` is even (`even_card_sq_mem`). Hence:

* **T1** (`Nat.not_eventuallyPeriodic_nthPrime_mem_of_odd`, unconditional): if `|A|` is odd, `d`
  is not eventually periodic, and `∑ₖ dₖ / b ^ (k + 1)` is irrational for every `b ≥ 2`
  (`Real.irrational_unionConstant_of_odd`).
* **T2** (`Nat.not_eventuallyPeriodic_nthPrime_mem_of_chowla`, conditional): if `ν(A) ≠ |A|` and
  `L(1/2, χ) ≠ 0` for all nonprincipal `χ` modulo `q` (`ChowlaHypothesis`), the same holds.
* **T3** (complement symmetry): the complement `Aᶜ` of `A` in the units gives the digit `1 - d`
  from `k = q` on (`eventuallyPeriodic_nthPrime_mem_unitsCompl_iff`), with `|Aᶜ| ≡ |A| (mod 2)`
  (`even_card_unitsCompl_iff`) and `|Aᶜ| - ν(Aᶜ) = -(|A| - ν(A))`
  (`card_unitsCompl_sub_card_sq_mem_unitsCompl`).
* **Positivity** (`not_eventuallyPeriodic_of_re_unionCoeff_mul_nonneg`, unconditional): taking real
  parts, `∑_{χ ≠ 1} re c_χ m_χ = (|A| - ν(A)) / 2` with `m_χ ≥ 0`; if every `re c_χ` has the sign
  of `ν(A) - |A| ≠ 0`, `d` is not eventually periodic. This settles the pairs `{1, a}` with
  `ν({1, a}) > 2`, e.g. `a ≠ 1` a square (`Nat.not_eventuallyPeriodic_nthPrime_mem_one_pair`,
  `Nat.not_eventuallyPeriodic_nthPrime_mem_one_pair_of_isSquare`), where `|A|` is even. In general
  (`not_eventuallyPeriodic_of_re_unionCoeff`) it suffices that `L(1/2, χ) ≠ 0` for the `χ` with
  `re c_χ (|A| - ν(A)) > 0`.
* Examples modulo `7`: `{1, 2, 4}`, `{1, 2, 3}` (T1), `{1, 2}` (positivity), `{3, 6}` (T2), and
  `{1, 3}`, where `ν(A) = |A|` and the method says nothing.

## Tags

Dirichlet character, residue class, order of vanishing, Chowla's conjecture, algebraic integer
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

/-- **Logarithmic derivatives at a real point, with orders of vanishing.** The version of
`Complex.exists_norm_sub_mul_log_le_of_prod_mul_deriv_eq` that identifies the multiplicities: if
`(∏ᵢ f i) Φ' = ∑ᵢ c i f i' ∏_{j ≠ i} f j` at the points `σ > s₀` close to `s₀`, then
`Φ(σ) = (∑ᵢ c i ord_{s₀} (f i)) log (σ - s₀) + O(1)` as `σ → s₀⁺`. -/
theorem Complex.exists_norm_sub_mul_analyticOrderNatAt_log_le {ι : Type*} [DecidableEq ι]
    (X : Finset ι) (f : ι → ℂ → ℂ) (c : ι → ℂ) {s₀ : ℝ} {Φ : ℂ → ℂ}
    (hf : ∀ i ∈ X, AnalyticAt ℂ (f i) s₀) (hf0 : ∀ i ∈ X, ¬ ∀ᶠ z in 𝓝 (s₀ : ℂ), f i z = 0)
    (hΦ : ∀ᶠ σ : ℝ in 𝓝[>] s₀, DifferentiableAt ℂ Φ σ ∧
      (∏ i ∈ X, f i σ) * deriv Φ σ = ∑ i ∈ X, c i * deriv (f i) σ * ∏ j ∈ X.erase i, f j σ) :
    ∃ C : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
      ‖Φ σ - (∑ i ∈ X, c i * analyticOrderNatAt (f i) (s₀ : ℂ)) * Real.log (σ - s₀)‖ ≤ C := by
  have hfac : ∀ i ∈ X, ∃ m : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g s₀ ∧ g s₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 (s₀ : ℂ), f i z = (z - s₀) ^ m • g z :=
    fun i hi ↦ (hf i hi).exists_eventuallyEq_pow_smul_nonzero_iff.2 (hf0 i hi)
  choose! m g hg hg0 hfg using hfac
  have hm : ∀ i ∈ X, analyticOrderNatAt (f i) (s₀ : ℂ) = m i := fun i hi ↦
    ((hf i hi).analyticOrderNatAt_eq_iff (analyticOrderAt_eq_top.not.2 (hf0 i hi))).2
      ⟨g i, hg i hi, hg0 i hi, hfg i hi⟩
  rw [show ∑ i ∈ X, c i * (analyticOrderNatAt (f i) (s₀ : ℂ) : ℂ) = ∑ i ∈ X, c i * m i from
    sum_congr rfl fun i hi ↦ by rw [hm i hi]]
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

section Coefficients

omit [NeZero q] in
/-- For a unit `a`, `χ(a⁻¹)` is the value of `χ` at the inverse unit. -/
theorem apply_inv_eq_apply_coe_inv {a : ZMod q} (ha : IsUnit a) (χ : DirichletCharacter ℂ q) :
    χ a⁻¹ = χ ↑ha.unit⁻¹ := by
  rw [← ZMod.inv_coe_unit, IsUnit.unit_spec]

/-- The character coefficient `c_χ(A) = ∑_{a ∈ A} χ(a⁻¹)` of a set `A` of residues. -/
noncomputable def unionCoeff (A : Finset (ZMod q)) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ a ∈ A, χ a⁻¹

omit [NeZero q] in
/-- `‖c_χ(A)‖ ≤ |A|`. -/
theorem norm_unionCoeff_le (A : Finset (ZMod q)) (χ : DirichletCharacter ℂ q) :
    ‖unionCoeff A χ‖ ≤ #A := by
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _a ∈ A, (1 : ℝ) := sum_le_sum fun a _ ↦ χ.norm_le_one _
    _ = #A := by simp

/-- For a set `A` of units, `c_χ(A)` is an algebraic integer. -/
theorem isIntegral_unionCoeff {A : Finset (ZMod q)} (hA : ∀ a ∈ A, IsUnit a)
    (χ : DirichletCharacter ℂ q) : IsIntegral ℤ (unionCoeff A χ) :=
  IsIntegral.sum _ fun a ha ↦ by
    rw [apply_inv_eq_apply_coe_inv (hA a ha)]
    exact isIntegral_apply_unit χ _

/-- **Orthogonality for a union of classes**: for a set `A` of units,
`∑_{χ ≠ 1} c_χ(A) χ(n) = φ(q) [n ∈ A] - |A| 1(n)`. -/
theorem sum_nonprincipal_unionCoeff_mul_apply {A : Finset (ZMod q)} (hA : ∀ a ∈ A, IsUnit a)
    (n : ZMod q) :
    ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ n =
      (if n ∈ A then (q.totient : ℂ) else 0) - #A * (1 : DirichletCharacter ℂ q) n := by
  have h : ∀ a ∈ A, ∑ χ ∈ nonprincipal q, χ a⁻¹ * χ n =
      (if n = a then (q.totient : ℂ) else 0) - (1 : DirichletCharacter ℂ q) n := by
    intro a ha
    simp_rw [apply_inv_eq_apply_coe_inv (hA a ha)]
    rw [sum_nonprincipal_apply_inv_mul_apply, IsUnit.unit_spec]
  simp_rw [unionCoeff, sum_mul]
  rw [sum_comm, sum_congr rfl h, sum_sub_distrib, sum_ite_eq, sum_const, nsmul_eq_mul]

end Coefficients

section Squares

/-- `ν(A) = ∑_{a ∈ A} ν(a)`: the square roots of the elements of `A`, counted fiberwise. -/
theorem card_sq_mem_eq_sum (A : Finset (ZMod q)) :
    #{r : ZMod q | r ^ 2 ∈ A} = ∑ a ∈ A, #{r : ZMod q | r ^ 2 = a} := by
  rw [card_eq_sum_card_fiberwise (f := fun r ↦ r ^ 2) (s := {r : ZMod q | r ^ 2 ∈ A}) (t := A)
    fun r hr ↦ (mem_filter.1 (mem_coe.1 hr)).2]
  refine sum_congr rfl fun a ha ↦ ?_
  rw [filter_filter]
  congr 1
  ext r
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ ha, h⟩⟩

/-- For `q ≥ 3` and a set `A` of units, `ν(A) = #{r mod q | r² ∈ A}` is even: each `ν(a)` is
(`even_card_sq_eq`). -/
theorem even_card_sq_mem (hq : 3 ≤ q) {A : Finset (ZMod q)} (hA : ∀ a ∈ A, IsUnit a) :
    _root_.Even #{r : ZMod q | r ^ 2 ∈ A} := by
  rw [card_sq_mem_eq_sum]
  refine sum_induction _ _root_.Even (fun _ _ ↦ Even.add) ⟨0, rfl⟩ fun a ha ↦ ?_
  have h := even_card_sq_eq hq (hA a ha).unit
  rw [IsUnit.unit_spec] at h
  convert h using 2

end Squares

section Weight

variable {A : Finset (ZMod q)}

variable (A) in
/-- The weight `e(n) = [n ∈ A] - |A| 1(n) / φ(q)` of the union `A`, centred by its expected
density `|A| / φ(q)` among the units. -/
noncomputable def unionWeight (n : ZMod q) : ℂ :=
  (if n ∈ A then 1 else 0) - #A * (q.totient : ℂ)⁻¹ * (1 : DirichletCharacter ℂ q) n

/-- **Orthogonality for the weight**: `φ(q) e(n) = ∑_{χ ≠ 1} c_χ(A) χ(n)`. -/
theorem totient_mul_unionWeight (hA : ∀ a ∈ A, IsUnit a) (n : ZMod q) :
    (q.totient : ℂ) * unionWeight A n = ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ n := by
  rw [sum_nonprincipal_unionCoeff_mul_apply hA, unionWeight]
  have := totient_ne_zero (q := q)
  split_ifs
  · field_simp
  · simp only [zero_sub, mul_neg, neg_inj]
    field_simp

variable (A) in
/-- The weight is real. -/
theorem ofReal_re_unionWeight (n : ZMod q) :
    ((unionWeight A n).re : ℂ) = unionWeight A n := by
  refine Complex.ext (by simp) ?_
  by_cases hn : IsUnit n
  · simp only [unionWeight, MulChar.one_apply hn, ofReal_im]
    split_ifs <;> simp
  · simp only [unionWeight, MulChar.map_nonunit _ hn, ofReal_im]
    split_ifs <;> simp

variable (A) in
/-- `‖e(n)‖ ≤ 1 + |A|`. -/
theorem norm_unionWeight_le (n : ZMod q) : ‖unionWeight A n‖ ≤ 1 + #A := by
  refine (norm_sub_le _ _).trans (add_le_add (by split_ifs <;> simp) ?_)
  rw [norm_mul, norm_mul, norm_inv, norm_natCast, norm_natCast]
  have h1 : (q.totient : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Nat.one_le_cast.2 (Nat.totient_pos.2 (NeZero.pos q)))
  calc _ ≤ (#A : ℝ) * 1 * 1 := by
        gcongr
        exact (1 : DirichletCharacter ℂ q).norm_le_one n
    _ = #A := by ring

variable (A) in
/-- A combination `∑_{χ ≠ 1} c_χ(A) primePart χ σ` is bounded on `1 < σ ≤ 2`. -/
theorem exists_norm_sum_unionCoeff_mul_primePart_le :
    ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      ‖∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePart σ‖ ≤ M := by
  have hA1 : ((#A + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  obtain ⟨M, hM⟩ := exists_norm_sum_nonprincipal_mul_primePart_le (q := q)
    (fun χ ↦ unionCoeff A χ / ((#A + 1 : ℕ) : ℂ)) fun χ ↦ by
      rw [norm_div, norm_natCast, div_le_one (by positivity)]
      push_cast
      linarith [norm_unionCoeff_le A χ]
  refine ⟨(#A + 1) * M, fun σ hσ hσ2 ↦ ?_⟩
  have e : ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePart σ = ((#A + 1 : ℕ) : ℂ) *
      ∑ χ ∈ nonprincipal q, unionCoeff A χ / ((#A + 1 : ℕ) : ℂ) * χ.primePart σ := by
    rw [mul_sum]
    refine sum_congr rfl fun χ _ ↦ ?_
    field_simp
  rw [e, norm_mul, norm_natCast]
  have h := hM σ hσ hσ2
  push_cast at h ⊢
  gcongr

/-- For `re s > 1`, `φ(q) ∑ₖ e(pₖ) pₖ ^ (-s) = ∑_{χ ≠ 1} c_χ(A) primePart χ s`. -/
theorem totient_mul_tsum_unionWeight (hA : ∀ a ∈ A, IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    (q.totient : ℂ) * ∑' k : ℕ, unionWeight A (nthPrime k) * (nthPrime k : ℂ) ^ (-s) =
      ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePart s := by
  rw [← tsum_mul_left]
  have e : ∀ k : ℕ, (q.totient : ℂ) * (unionWeight A (nthPrime k) * (nthPrime k : ℂ) ^ (-s)) =
      ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primeTerm k s := by
    intro k
    rw [← mul_assoc, totient_mul_unionWeight hA, sum_mul]
    refine sum_congr rfl fun χ _ ↦ ?_
    rw [primeTerm]
    ring
  rw [tsum_congr e, Summable.tsum_finsetSum fun χ _ ↦ (χ.summable_primeTerm hs).mul_left _]
  refine sum_congr rfl fun χ _ ↦ ?_
  rw [primePart, tsum_mul_left]

variable (A) in
/-- The Abel series `A(s)` of `k ↦ e(pₖ)`. -/
noncomputable def unionAbel : ℂ → ℂ := abelSeries (fun k ↦ unionWeight A (nthPrime k)) nthPrime

variable (A) in
/-- The combination `Φ(s) = φ(q) A(s) + ∑_{χ ≠ 1} c_χ(A) primePowerPart χ s`. On `re s > 1` it is
`∑_{χ ≠ 1} c_χ(A) log L(s, χ)` (`unionLog_eq`); under bounded partial sums it is holomorphic on
`re s > 1 / 2`. -/
noncomputable def unionLog (s : ℂ) : ℂ :=
  q.totient * unionAbel A s + ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePowerPart s

variable {C : ℝ} (hC : ∀ n, ‖∑ k ∈ range n, unionWeight A (nthPrime k)‖ ≤ C)
include hC

omit [NeZero q] in
/-- Under bounded partial sums, `A` is holomorphic on `re s > 0`. -/
theorem differentiableOn_unionAbel : DifferentiableOn ℂ (unionAbel A) {s : ℂ | 0 < s.re} :=
  differentiableOn_abelSeries hC (Nat.prime_nth_prime 0).pos nthPrime_strictMono

/-- Under bounded partial sums, `Φ(s) = ∑_{χ ≠ 1} c_χ(A) (primePart χ s + primePowerPart χ s)`
for `re s > 1`. -/
theorem unionLog_eq (hA : ∀ a ∈ A, IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    unionLog A s =
      ∑ χ ∈ nonprincipal q, unionCoeff A χ * (χ.primePart s + χ.primePowerPart s) := by
  rw [unionLog, unionAbel, abelSeries_eq_tsum hC (Nat.prime_nth_prime 0).pos nthPrime_strictMono
    hs, totient_mul_tsum_unionWeight hA hs, ← sum_add_distrib]
  simp only [mul_add]

omit [NeZero q] in
/-- Under bounded partial sums, `Φ` is holomorphic on `re s > 1 / 2`. -/
theorem differentiableOn_unionLog : DifferentiableOn ℂ (unionLog A) {s : ℂ | 1 / 2 < s.re} :=
  (((differentiableOn_unionAbel hC).mono fun s (hs : 1 / 2 < s.re) ↦
    show 0 < s.re by linarith).const_mul _).add
    (DifferentiableOn.fun_sum fun χ _ ↦ χ.differentiableOn_primePowerPart.const_mul _)

/-- Under bounded partial sums, `Φ' = ∑_{χ ≠ 1} c_χ(A) L'(s, χ) / L(s, χ)` on `re s > 1`. -/
theorem hasDerivAt_unionLog (hA : ∀ a ∈ A, IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (unionLog A)
      (∑ χ ∈ nonprincipal q, unionCoeff A χ * (deriv (LFunction χ) s / LFunction χ s)) s := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have h : HasDerivAt (fun s ↦ ∑ χ ∈ nonprincipal q,
      unionCoeff A χ * (χ.primePart s + χ.primePowerPart s)) _ s :=
    HasDerivAt.fun_sum fun χ _ ↦ (χ.hasDerivAt_primePart_add_primePowerPart hs).const_mul _
  exact h.congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hs) fun s hs ↦
    unionLog_eq hC hA hs)

open Classical in
/-- **Continuation of the logarithmic derivative identity.** Under bounded partial sums, on
`re s > 1 / 2`,
`(∏_{χ ≠ 1} L(s, χ)) Φ'(s) = ∑_{χ ≠ 1} c_χ(A) L'(s, χ) ∏_{ψ ≠ 1, ψ ≠ χ} L(s, ψ)`. -/
theorem prod_mul_deriv_unionLog (hA : ∀ a ∈ A, IsUnit a) {s : ℂ} (hs : 1 / 2 < s.re) :
    (∏ χ ∈ nonprincipal q, LFunction χ s) * deriv (unionLog A) s =
      ∑ χ ∈ nonprincipal q, unionCoeff A χ * deriv (LFunction χ) s *
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
      (fun s ↦ (∏ χ ∈ nonprincipal q, LFunction χ s) * deriv (unionLog A) s) U :=
    (((hPr _ subset_rfl).differentiableOn).mul
      ((differentiableOn_unionLog hC).deriv hUo)).analyticOnNhd hUo
  have hrhs : AnalyticOnNhd ℂ (fun s ↦ ∑ χ ∈ nonprincipal q, unionCoeff A χ *
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
  rw [(hasDerivAt_unionLog hC hA hs).deriv, mul_sum]
  refine sum_congr rfl fun χ hχ ↦ ?_
  rw [← mul_prod_erase _ (fun ψ ↦ LFunction ψ s) hχ]
  field_simp [hne χ hχ]

end Weight

section PrimeSquares

/-- **The prime-square side at `1 / 2`, for one unit `a`.** With `ν(a) = #{r mod q | r ^ 2 = a}`,
`∑_{χ ≠ 1} χ(a⁻¹) primePowerPart χ σ = ((ν(a) - 1) / 2) log (1 / (σ - 1 / 2)) + O(1)` as
`σ → 1 / 2⁺`. This is the part of `exists_norm_classLog_add_mul_log_le` that does not involve the
Abel series, with the same proof: the `p²` terms, orthogonality, and Dirichlet density in the
`ν(a)` classes `r` with `r² = a`. -/
theorem exists_norm_sum_primePowerPart_add_mul_log_le {a : ZMod q} (ha : IsUnit a) :
    ∃ C' : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖∑ χ ∈ nonprincipal q, χ a⁻¹ * χ.primePowerPart σ +
      (((#{r : ZMod q | r ^ 2 = a} : ℕ) : ℂ) - 1) / 2 * Real.log (σ - 1 / 2)‖ ≤ C' := by
  set u : (ZMod q)ˣ := ha.unit
  have hu : (u : ZMod q) = a := ha.unit_spec
  set S : Finset (ZMod q) := {r : ZMod q | r ^ 2 = a}
  set ν : ℂ := ((#S : ℕ) : ℂ)
  set G1 : ℂ → ℂ := (1 : DirichletCharacter ℂ q).primePart
  set R : ℂ → ℂ := fun s ↦ ∑ χ ∈ nonprincipal q, χ a⁻¹ * χ.tailPart 3 s
  have hR : ContinuousAt R ((1 / 2 : ℝ) : ℂ) := by
    have hT : ∀ χ : DirichletCharacter ℂ q, DifferentiableAt ℂ (χ.tailPart 3) ((1 / 2 : ℝ) : ℂ) :=
      fun χ ↦ (χ.differentiableOn_tailPart (m := 3) (by norm_num)).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (show 1 / ((3 : ℕ) : ℝ) < ((1 / 2 : ℝ) : ℂ).re by norm_num))
    exact (DifferentiableAt.fun_sum fun χ _ ↦ (hT χ).const_mul _).continuousAt
  have hRe : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖R σ‖ ≤ ‖R ((1 / 2 : ℝ) : ℂ)‖ + 1 :=
    ((continuous_ofReal.tendsto _).eventually
      (hR.norm.eventually (eventually_le_nhds (lt_add_one _)))).filter_mono nhdsWithin_le_nhds
  have hSu : ∀ r ∈ S, IsUnit r := fun r hr ↦
    (isUnit_pow_iff two_ne_zero).1 ((mem_filter.1 hr).2 ▸ ha)
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
  have hA : ∑ χ ∈ nonprincipal q, χ a⁻¹ * χ.primePowerPart σ = R σ +
      (∑ χ ∈ nonprincipal q, χ a⁻¹ * (χ ^ 2).primePart ((2 * σ : ℝ) : ℂ)) / 2 := by
    have e : ∀ χ : DirichletCharacter ℂ q, χ.primePowerPart σ =
        (χ ^ 2).primePart ((2 * σ : ℝ) : ℂ) / 2 + χ.tailPart 3 σ := fun χ ↦ by
      rw [primePowerPart_eq_primePart_sq_add_tailPart χ hσ', ofReal_mul, ofReal_ofNat]
    simp only [R, e, mul_add, sum_add_distrib, sum_div, mul_div_assoc]
    ring
  -- orthogonality and the square roots of `a`
  have hB : ∑ χ ∈ nonprincipal q, χ a⁻¹ * (χ ^ 2).primePart ((2 * σ : ℝ) : ℂ) =
      ∑ r ∈ S, ((q.totient : ℂ) * classSeries r (2 * σ) - G1 ((2 * σ : ℝ) : ℂ)) +
        (ν - 1) * G1 ((2 * σ : ℝ) : ℂ) := by
    have e2 : ∀ χ : DirichletCharacter ℂ q, (χ ^ 2).primePart ((2 * σ : ℝ) : ℂ) =
        ∑' k : ℕ, χ ((nthPrime k : ZMod q) ^ 2) * (nthPrime k : ℂ) ^ (-((2 * σ : ℝ) : ℂ)) :=
      fun χ ↦ tsum_congr fun k ↦ by rw [primeTerm, MulChar.pow_apply' χ two_ne_zero, map_pow]
    have h := sum_nonprincipal_mul_tsum_eq u (fun r ↦ r ^ 2) hσ2
    rw [hu] at h
    have h1sq : ∀ r : ZMod q, (1 : DirichletCharacter ℂ q) (r ^ 2) =
        (1 : DirichletCharacter ℂ q) r := fun r ↦ by
      by_cases hr : IsUnit r
      · rw [MulChar.one_apply hr, MulChar.one_apply (hr.pow 2)]
      · rw [MulChar.map_nonunit _ hr,
          MulChar.map_nonunit _ (mt (isUnit_pow_iff two_ne_zero).1 hr)]
    have hG : G1 ((2 * σ : ℝ) : ℂ) =
        ∑ r : ZMod q, (1 : DirichletCharacter ℂ q) r * classSeries r (2 * σ) :=
      primePart_ofReal_eq_sum _ hσ2
    simp_rw [apply_inv_eq_apply_coe_inv ha]
    rw [sum_congr rfl fun χ _ ↦ by rw [e2 χ], h, hG]
    simp only [h1sq, sub_mul, sum_sub_distrib, ite_mul, zero_mul, ← sum_filter]
    rw [sum_const, nsmul_eq_mul, mul_sum]
    ring
  have hlog2 : ((Real.log (2 * σ - 1) : ℝ) : ℂ) = Real.log 2 + Real.log (σ - 1 / 2) := by
    rw [show 2 * σ - 1 = 2 * (σ - 1 / 2) by ring,
      Real.log_mul two_ne_zero (sub_ne_zero.2 hσ.1.ne'), ofReal_add]
  have key : ∑ χ ∈ nonprincipal q, χ a⁻¹ * χ.primePowerPart σ +
      (ν - 1) / 2 * Real.log (σ - 1 / 2) = R σ +
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

variable {A : Finset (ZMod q)} {C : ℝ}

/-- **The prime-square side at `1 / 2`, for a union.** Under bounded partial sums, with
`ν(A) = #{r mod q | r ^ 2 ∈ A}`, `Φ(σ) = ((ν(A) - |A|) / 2) log (1 / (σ - 1 / 2)) + O(1)` as
`σ → 1 / 2⁺`: sum the single-unit statements over `a ∈ A`; the Abel series is continuous at
`1 / 2`. -/
theorem exists_norm_unionLog_add_mul_log_le (hA : ∀ a ∈ A, IsUnit a)
    (hC : ∀ n, ‖∑ k ∈ range n, unionWeight A (nthPrime k)‖ ≤ C) :
    ∃ C' : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖unionLog A σ +
      (((#{r : ZMod q | r ^ 2 ∈ A} : ℕ) : ℂ) - #A) / 2 * Real.log (σ - 1 / 2)‖ ≤ C' := by
  have hD : ∀ a ∈ A, ∃ C' : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2),
      ‖∑ χ ∈ nonprincipal q, χ a⁻¹ * χ.primePowerPart σ +
        (((#{r : ZMod q | r ^ 2 = a} : ℕ) : ℂ) - 1) / 2 * Real.log (σ - 1 / 2)‖ ≤ C' :=
    fun a ha ↦ exists_norm_sum_primePowerPart_add_mul_log_le (hA a ha)
  choose! M hM using hD
  have hAb : ContinuousAt (unionAbel A) ((1 / 2 : ℝ) : ℂ) :=
    ((differentiableOn_unionAbel hC).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show (0 : ℝ) < ((1 / 2 : ℝ) : ℂ).re by norm_num))).continuousAt
  have hAe : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2),
      ‖unionAbel A σ‖ ≤ ‖unionAbel A ((1 / 2 : ℝ) : ℂ)‖ + 1 :=
    ((continuous_ofReal.tendsto _).eventually
      (hAb.norm.eventually (eventually_le_nhds (lt_add_one _)))).filter_mono nhdsWithin_le_nhds
  refine ⟨q.totient * (‖unionAbel A ((1 / 2 : ℝ) : ℂ)‖ + 1) + ∑ a ∈ A, M a, ?_⟩
  filter_upwards [hAe, (eventually_all_finset A).2 hM] with σ hσA hσM
  have hν : (((#{r : ZMod q | r ^ 2 ∈ A} : ℕ) : ℂ) - #A) / 2 =
      ∑ a ∈ A, (((#{r : ZMod q | r ^ 2 = a} : ℕ) : ℂ) - 1) / 2 := by
    rw [card_sq_mem_eq_sum, ← sum_div, sum_sub_distrib]
    push_cast
    simp
  have hL : unionLog A σ = q.totient * unionAbel A σ +
      ∑ a ∈ A, ∑ χ ∈ nonprincipal q, χ a⁻¹ * χ.primePowerPart σ := by
    rw [unionLog]
    simp_rw [unionCoeff, sum_mul]
    rw [sum_comm]
  rw [hL, hν, sum_mul, add_assoc, ← sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans
    (sum_le_sum fun a ha ↦ hσM a ha)))
  rw [norm_mul, norm_natCast]
  gcongr

end PrimeSquares

section Main

variable {A : Finset (ZMod q)}

/-- **The multiplicity relation, analytic form.** If the partial sums of `e(pₖ)` are bounded,
then the orders of vanishing `m_χ = ord_{s = 1/2} L(s, χ)` satisfy
`∑_{χ ≠ 1} c_χ(A) m_χ = (|A| - ν(A)) / 2`, with `ν(A) = #{r mod q | r² ∈ A}`.

Indeed `Φ = unionLog A` is holomorphic on `re s > 1 / 2`; near `1 / 2` it is
`(∑_{χ ≠ 1} c_χ(A) m_χ) log (σ - 1 / 2) + O(1)` by the logarithmic derivative identity
(`prod_mul_deriv_unionLog`), and `-((ν(A) - |A|) / 2) log (σ - 1 / 2) + O(1)` by the prime squares
(`exists_norm_unionLog_add_mul_log_le`). -/
theorem sum_unionCoeff_mul_analyticOrderNatAt_eq (hA : ∀ a ∈ A, IsUnit a) {C : ℝ}
    (hC : ∀ n, ‖∑ k ∈ range n, unionWeight A (nthPrime k)‖ ≤ C) :
    ∑ χ ∈ nonprincipal q, unionCoeff A χ * (analyticOrderNatAt (LFunction χ) (1 / 2) : ℂ) =
      ((#A : ℂ) - #{r : ZMod q | r ^ 2 ∈ A}) / 2 := by
  classical
  obtain ⟨C₁, h₁⟩ := exists_norm_unionLog_add_mul_log_le hA hC
  have hΦ : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), DifferentiableAt ℂ (unionLog A) σ ∧
      (∏ χ ∈ nonprincipal q, LFunction χ σ) * deriv (unionLog A) σ =
        ∑ χ ∈ nonprincipal q, unionCoeff A χ * deriv (LFunction χ) σ *
          ∏ ψ ∈ (nonprincipal q).erase χ, LFunction ψ σ := by
    refine eventually_nhdsWithin_of_forall fun σ (hσ : 1 / 2 < σ) ↦ ?_
    have hσ' : 1 / 2 < (σ : ℂ).re := by simpa using hσ
    exact ⟨(differentiableOn_unionLog hC).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hσ'),
      prod_mul_deriv_unionLog hC hA hσ'⟩
  obtain ⟨C₂, h₂⟩ := Complex.exists_norm_sub_mul_analyticOrderNatAt_log_le (nonprincipal q)
    (fun χ ↦ LFunction χ) (unionCoeff A) (s₀ := 1 / 2)
    (fun χ hχ ↦ (differentiable_LFunction (mem_nonprincipal.1 hχ)).analyticAt _)
    (fun χ hχ ↦ not_eventually_LFunction_eq_zero (mem_nonprincipal.1 hχ) _) hΦ
  have e : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by norm_num
  rw [e] at h₂
  set x : ℂ := ∑ χ ∈ nonprincipal q,
    unionCoeff A χ * (analyticOrderNatAt (LFunction χ) (1 / 2) : ℂ)
  set ν : ℕ := #{r : ZMod q | r ^ 2 ∈ A}
  have hx : x + ((ν : ℂ) - #A) / 2 = 0 := by
    refine Complex.eq_zero_of_eventually_norm_mul_log_le (s₀ := 1 / 2) (C := C₁ + C₂) ?_
    filter_upwards [h₁, h₂] with σ h1 h2
    calc ‖(x + ((ν : ℂ) - #A) / 2) * Real.log (σ - 1 / 2)‖ =
        ‖(unionLog A σ + ((ν : ℂ) - #A) / 2 * Real.log (σ - 1 / 2)) -
          (unionLog A σ - x * Real.log (σ - 1 / 2))‖ := by ring_nf
      _ ≤ C₁ + C₂ := (norm_sub_le _ _).trans (add_le_add h1 h2)
  linear_combination hx

omit [NeZero q] in
/-- For a natural number `n`, `re e(n) = [n ∈ A] - |A| φ(q)⁻¹ re 1(n)`. -/
theorem re_unionWeight_natCast [NeZero q] (n : ℕ) :
    (unionWeight A n).re = (if (n : ZMod q) ∈ A then 1 else 0) -
      #A * (q.totient : ℝ)⁻¹ * ((1 : DirichletCharacter ℂ q) n).re := by
  have hφ : (#A : ℂ) * (q.totient : ℂ)⁻¹ = (((#A : ℝ) * (q.totient : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [unionWeight, sub_re, hφ, re_ofReal_mul]
  congr 1
  split_ifs <;> simp

/-- **Linear sums.** If the digits `[pₖ mod q ∈ A]` are eventually periodic, then the partial
sums of `e(pₖ) = [pₖ ∈ A] - |A| [pₖ ∤ q] / φ(q)` are bounded. Periodicity gives
`∑_{k < n} e(pₖ) = c' n + O(1)`, and since `∑ₖ e(pₖ) pₖ ^ (-σ)` stays bounded as `σ → 1⁺`
(orthogonality and `exists_norm_primePart_le`), `c' = 0`
(`not_exists_abs_sum_sub_mul_le_of_abs_tsum_le`). -/
theorem exists_norm_sum_unionWeight_le (hA : ∀ a ∈ A, IsUnit a) {P : ℕ} (hP : 0 < P)
    (hper : Function.EventuallyPeriodic
      (fun k ↦ if (nthPrime k : ZMod q) ∈ A then 1 else 0) P) :
    ∃ C : ℝ, ∀ n, ‖∑ k ∈ range n, unionWeight A (nthPrime k)‖ ≤ C := by
  set φ : ℝ := (q.totient : ℝ)
  set κ : ℝ := #A * φ⁻¹
  set d : ℕ → ℝ := fun k ↦ if (nthPrime k : ZMod q) ∈ A then 1 else 0
  set e : ℕ → ℝ := fun k ↦ (unionWeight A (nthPrime k)).re
  have hd : Function.EventuallyPeriodic d P := by
    filter_upwards [hper] with k hk
    simp only [d]
    split_ifs at hk ⊢ <;> simp_all
  obtain ⟨c, C, hcC⟩ := hd.exists_abs_sum_real_sub_mul_le hP
  have hφ : 0 < φ := Nat.cast_pos.2 (Nat.totient_pos.2 (NeZero.pos q))
  have hκ : 0 ≤ κ := by positivity
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
  have hlin : ∀ n : ℕ, |∑ k ∈ range n, e k - (c - κ) * n| ≤ C + κ * q := by
    intro n
    have he : ∑ k ∈ range n, e k = ∑ k ∈ range n, d k -
        κ * ∑ k ∈ range n, ((1 : DirichletCharacter ℂ q) (nthPrime k)).re := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ ↦ re_unionWeight_natCast _
    rw [he]
    calc _ = |(∑ k ∈ range n, d k - c * n) - κ *
          (∑ k ∈ range n, ((1 : DirichletCharacter ℂ q) (nthPrime k)).re - n)| := by ring_nf
      _ ≤ |∑ k ∈ range n, d k - c * n| + |κ *
          (∑ k ∈ range n, ((1 : DirichletCharacter ℂ q) (nthPrime k)).re - n)| := abs_sub _ _
      _ ≤ C + κ * q := by
          rw [abs_mul, abs_of_nonneg hκ]
          gcongr
          · exact hcC n
          · exact hone n
  by_cases hc : c - κ = 0
  · refine ⟨C + κ * q, fun n ↦ ?_⟩
    have h : ∑ k ∈ range n, unionWeight A (nthPrime k) = ((∑ k ∈ range n, e k : ℝ) : ℂ) := by
      push_cast
      exact sum_congr rfl fun k _ ↦ (ofReal_re_unionWeight A _).symm
    rw [h, norm_real, Real.norm_eq_abs]
    simpa [hc] using hlin n
  · obtain ⟨M, hM⟩ := exists_norm_sum_unionCoeff_mul_primePart_le (q := q) A
    refine absurd ⟨c - κ, hc, _, hlin⟩ (not_exists_abs_sum_sub_mul_le_of_abs_tsum_le (a := e)
      (B := 1 + #A) (fun k ↦ (abs_re_le_norm _).trans (norm_unionWeight_le A _)) (M := φ⁻¹ * M)
      fun σ hσ hσ2 ↦ ?_)
    have hs : 1 < (σ : ℂ).re := by simpa using hσ
    have e1 : ((∑' k, e k * (nthPrime k : ℝ) ^ (-σ) : ℝ) : ℂ) = (q.totient : ℂ)⁻¹ *
        ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePart σ := by
      rw [← totient_mul_tsum_unionWeight hA hs, ← mul_assoc, inv_mul_cancel₀ totient_ne_zero,
        one_mul, ofReal_tsum]
      refine tsum_congr fun k ↦ ?_
      rw [ofReal_mul, ofReal_re_unionWeight, ofReal_cpow (Nat.cast_nonneg _)]
      push_cast
      rfl
    rw [← Real.norm_eq_abs, ← norm_real, e1, norm_mul, norm_inv, norm_natCast]
    exact mul_le_mul_of_nonneg_left (hM σ hσ hσ2) (inv_nonneg.2 hφ.le)

/-- **The multiplicity relation.** If the digits `[pₖ mod q ∈ A]` are eventually periodic, then
the orders of vanishing `m_χ` of the `L(s, χ)`, `χ ≠ 1`, at `s = 1 / 2` satisfy
`∑_{χ ≠ 1} c_χ(A) m_χ = (|A| - ν(A)) / 2`, where `c_χ(A) = ∑_{a ∈ A} χ(a⁻¹)` and
`ν(A) = #{r mod q | r² ∈ A}`. -/
theorem sum_unionCoeff_mul_analyticOrderNatAt_eq_of_eventuallyPeriodic (hA : ∀ a ∈ A, IsUnit a)
    {P : ℕ} (hP : 0 < P)
    (hper : Function.EventuallyPeriodic
      (fun k ↦ if (nthPrime k : ZMod q) ∈ A then 1 else 0) P) :
    ∑ χ ∈ nonprincipal q, unionCoeff A χ * (analyticOrderNatAt (LFunction χ) (1 / 2) : ℂ) =
      ((#A : ℂ) - #{r : ZMod q | r ^ 2 ∈ A}) / 2 :=
  have ⟨_, hC⟩ := exists_norm_sum_unionWeight_le hA hP hper
  sum_unionCoeff_mul_analyticOrderNatAt_eq hA hC

variable (q) in
/-- **Chowla's hypothesis at level `q`**: `L(1 / 2, χ) ≠ 0` for every nonprincipal Dirichlet
character `χ` modulo `q`. Chowla (1965) conjectured that `L(1 / 2, χ) ≠ 0` for every Dirichlet
character `χ`; this is expected to hold for every `q`, and is known for many small moduli by
computation, but is open in general. -/
def ChowlaHypothesis : Prop :=
  ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → LFunction χ (1 / 2) ≠ 0

/-- **Even unions under partial central nonvanishing.** Taking real parts in the multiplicity
relation gives `∑_{χ ≠ 1} re c_χ(A) m_χ = (|A| - ν(A)) / 2`, with `m_χ ≥ 0`. Suppose
`ν(A) ≠ |A|`. Only the characters with `re c_χ(A) (|A| - ν(A)) > 0` can contribute to the right
sign; so if `L(1 / 2, χ) ≠ 0` for those `χ` (and no others need be assumed), the digits
`[pₖ mod q ∈ A]` are not eventually periodic. -/
theorem not_eventuallyPeriodic_of_re_unionCoeff (hA : ∀ a ∈ A, IsUnit a)
    (hν : #{r : ZMod q | r ^ 2 ∈ A} ≠ #A)
    (hL : ∀ χ ∈ nonprincipal q,
      0 < (unionCoeff A χ).re * ((#A : ℝ) - #{r : ZMod q | r ^ 2 ∈ A}) →
        LFunction χ (1 / 2) ≠ 0)
    {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic (fun k ↦ if (nthPrime k : ZMod q) ∈ A then 1 else 0) P := by
  intro hper
  have h := congrArg Complex.re
    (sum_unionCoeff_mul_analyticOrderNatAt_eq_of_eventuallyPeriodic hA hP hper)
  set ν : ℕ := #{r : ZMod q | r ^ 2 ∈ A}
  simp only [re_sum, mul_re, natCast_re, natCast_im, mul_zero, sub_zero] at h
  have hre : (((#A : ℂ) - ν) / 2).re = ((#A : ℝ) - ν) / 2 := by
    rw [div_ofNat_re, sub_re, natCast_re, natCast_re]
  rw [hre] at h
  have h1 : (∑ χ ∈ nonprincipal q,
      (unionCoeff A χ).re * (analyticOrderNatAt (LFunction χ) (1 / 2) : ℝ)) * ((#A : ℝ) - ν) ≤
        0 := by
    rw [sum_mul]
    refine sum_nonpos fun χ hχ ↦ ?_
    rw [mul_right_comm]
    by_cases hc : 0 < (unionCoeff A χ).re * ((#A : ℝ) - ν)
    · have hz : analyticOrderNatAt (LFunction χ) (1 / 2) = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero.2 (.inr (hL χ hχ hc)), ENat.toNat_zero]
      rw [hz, Nat.cast_zero, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) (Nat.cast_nonneg _)
  rw [h] at h1
  have h2 : ((#A : ℝ) - ν) ^ 2 ≤ 0 := by nlinarith
  have h3 : (ν : ℝ) = #A := by nlinarith [sq_nonneg ((#A : ℝ) - ν)]
  exact hν (by exact_mod_cast h3)

/-- **Even unions under central nonvanishing** (analytic form of T2). If `ν(A) ≠ |A|` and
`L(1 / 2, χ) ≠ 0` for every nonprincipal `χ` with `c_χ(A) ≠ 0`, then the digits
`[pₖ mod q ∈ A]` are not eventually periodic. -/
theorem not_eventuallyPeriodic_of_LFunction_ne_zero (hA : ∀ a ∈ A, IsUnit a)
    (hL : ∀ χ ∈ nonprincipal q, unionCoeff A χ ≠ 0 → LFunction χ (1 / 2) ≠ 0)
    (hν : #{r : ZMod q | r ^ 2 ∈ A} ≠ #A) {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic (fun k ↦ if (nthPrime k : ZMod q) ∈ A then 1 else 0) P :=
  not_eventuallyPeriodic_of_re_unionCoeff hA hν
    (fun χ hχ hpos ↦ hL χ hχ fun hc ↦ by simp [hc] at hpos) hP

/-- **Even unions, by positivity** (unconditional). If `ν(A) ≠ |A|` and every `re c_χ(A)` has
the sign of `ν(A) - |A|` (or vanishes), the digits `[pₖ mod q ∈ A]` are not eventually periodic:
no zero at `1 / 2` can push `∑_{χ ≠ 1} re c_χ(A) m_χ` to the sign of `|A| - ν(A)`. -/
theorem not_eventuallyPeriodic_of_re_unionCoeff_mul_nonneg (hA : ∀ a ∈ A, IsUnit a)
    (hs : ∀ χ ∈ nonprincipal q,
      0 ≤ (unionCoeff A χ).re * ((#{r : ZMod q | r ^ 2 ∈ A} : ℝ) - #A))
    (hν : #{r : ZMod q | r ^ 2 ∈ A} ≠ #A) {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic (fun k ↦ if (nthPrime k : ZMod q) ∈ A then 1 else 0) P :=
  not_eventuallyPeriodic_of_re_unionCoeff hA hν
    (fun χ hχ hpos ↦ absurd hpos (by have := hs χ hχ; linarith)) hP

end Main

section Complement

variable {A : Finset (ZMod q)}

open Classical in
/-- The complement `Aᶜ` of `A` in the units modulo `q`. -/
noncomputable def unitsCompl (A : Finset (ZMod q)) : Finset (ZMod q) := {a | IsUnit a ∧ a ∉ A}

theorem mem_unitsCompl {a : ZMod q} : a ∈ unitsCompl A ↔ IsUnit a ∧ a ∉ A := by
  simp [unitsCompl]

theorem isUnit_of_mem_unitsCompl : ∀ a ∈ unitsCompl A, IsUnit a :=
  fun _ ha ↦ (mem_unitsCompl.1 ha).1

open Classical in
/-- Splitting the units modulo `q` along a predicate. -/
theorem card_isUnit_and_not_add_card_isUnit_and (P : ZMod q → Prop) :
    #{a : ZMod q | IsUnit a ∧ ¬ P a} + #{a : ZMod q | IsUnit a ∧ P a} = q.totient := by
  have hU : #({a : ZMod q | IsUnit a} : Finset (ZMod q)) = q.totient := by
    rw [← ZMod.card_units_eq_totient, ← Finset.card_univ]
    symm
    refine card_nbij (fun u : (ZMod q)ˣ ↦ (u : ZMod q)) (fun u _ ↦ by simp)
      (fun u _ v _ h ↦ Units.ext h) fun a ha ↦ ?_
    exact ⟨(mem_filter.1 ha).2.unit, mem_coe.2 (mem_univ _), IsUnit.unit_spec _⟩
  rw [← hU, ← card_filter_add_card_filter_not (s := {a : ZMod q | IsUnit a})
    (fun a ↦ ¬ P a), filter_filter, filter_filter]
  simp only [not_not]

/-- `|Aᶜ| + |A| = φ(q)`. -/
theorem card_unitsCompl_add_card (hA : ∀ a ∈ A, IsUnit a) : #(unitsCompl A) + #A = q.totient := by
  classical
  convert card_isUnit_and_not_add_card_isUnit_and (q := q) (· ∈ A) using 3
  · ext a
    simp [unitsCompl]
  · ext a
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h ↦ ⟨hA a h, h⟩, fun h ↦ h.2⟩

/-- `ν(Aᶜ) + ν(A) = φ(q)`: the units `r` split according to whether `r² ∈ A`. -/
theorem card_sq_mem_unitsCompl_add_card_sq_mem (hA : ∀ a ∈ A, IsUnit a) :
    #{r : ZMod q | r ^ 2 ∈ unitsCompl A} + #{r : ZMod q | r ^ 2 ∈ A} = q.totient := by
  classical
  convert card_isUnit_and_not_add_card_isUnit_and (q := q) (fun r ↦ r ^ 2 ∈ A) using 3
  · ext r
    simp only [mem_filter, mem_univ, true_and, mem_unitsCompl, isUnit_pow_iff two_ne_zero]
  · ext r
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h ↦ ⟨(isUnit_pow_iff two_ne_zero).1 (hA _ h), h⟩, fun h ↦ h.2⟩

/-- **Complement symmetry, parity.** For `q ≥ 3`, `|Aᶜ|` and `|A|` have the same parity, since
`φ(q)` is even: T1 applies to `A` exactly when it applies to `Aᶜ`. -/
theorem even_card_unitsCompl_iff (hq : 3 ≤ q) (hA : ∀ a ∈ A, IsUnit a) :
    _root_.Even #(unitsCompl A) ↔ _root_.Even #A := by
  have he := Nat.totient_even (by omega : 2 < q)
  rwa [← card_unitsCompl_add_card hA, Nat.even_add] at he

/-- **Complement symmetry, defect.** `|Aᶜ| - ν(Aᶜ) = -(|A| - ν(A))`: the right side of the
multiplicity relation changes sign, so `ν(A) ≠ |A|` (the hypothesis of T2) is also invariant. -/
theorem card_unitsCompl_sub_card_sq_mem_unitsCompl (hA : ∀ a ∈ A, IsUnit a) :
    (#(unitsCompl A) : ℤ) - #{r : ZMod q | r ^ 2 ∈ unitsCompl A} =
      -((#A : ℤ) - #{r : ZMod q | r ^ 2 ∈ A}) := by
  have h1 := card_unitsCompl_add_card hA
  have h2 := card_sq_mem_unitsCompl_add_card_sq_mem hA
  omega

/-- The prime `pₖ` is a unit modulo `q` once `k ≥ q`. -/
theorem isUnit_nthPrime {k : ℕ} (hk : q ≤ k) : IsUnit ((nthPrime k : ℕ) : ZMod q) := by
  by_contra hu
  have hdvd : nthPrime k ∣ q := by
    by_contra h
    exact hu ((ZMod.isUnit_prime_iff_not_dvd (Nat.prime_nth_prime k)).2 h)
  have := Nat.le_of_dvd (NeZero.pos q) hdvd
  have := Nat.add_two_le_nth_prime k
  omega

/-- **Complement symmetry, digits.** From `k = q` on, the digit of `Aᶜ` is `1 - [pₖ ∈ A]`; so the
two digit sequences are eventually periodic for the same periods. -/
theorem eventuallyPeriodic_nthPrime_mem_unitsCompl_iff {P : ℕ} :
    Function.EventuallyPeriodic
        (fun k ↦ if (nthPrime k : ZMod q) ∈ unitsCompl A then 1 else 0) P ↔
      Function.EventuallyPeriodic (fun k ↦ if (nthPrime k : ZMod q) ∈ A then 1 else 0) P := by
  have key : ∀ k, q ≤ k → ((nthPrime k : ZMod q) ∈ unitsCompl A ↔ (nthPrime k : ZMod q) ∉ A) :=
    fun k hk ↦ by rw [mem_unitsCompl]; exact and_iff_right (isUnit_nthPrime hk)
  constructor <;> intro h <;> filter_upwards [h, eventually_ge_atTop q] with k hk hkq <;>
    simp only [key k hkq, key (k + P) (by omega)] at hk ⊢ <;> split_ifs at hk ⊢ <;> simp_all

end Complement

end DirichletCharacter

open DirichletCharacter in
/-- **T1: odd unions.** For `q ≥ 3` and a set `A` of units with `|A|` odd, the
digits `[pₖ mod q ∈ A]` are not eventually periodic: the multiplicity relation would equate an
algebraic integer with the half odd integer `(|A| - ν(A)) / 2`. -/
theorem Nat.not_eventuallyPeriodic_nthPrime_mem_of_odd {q : ℕ} (hq : 3 ≤ q)
    {A : Finset (ZMod q)} (hA : ∀ a ∈ A, IsUnit a) (hodd : Odd #A) {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic
      (fun k ↦ if (Nat.nth Nat.Prime k : ZMod q) ∈ A then 1 else 0) P := by
  have : NeZero q := ⟨by omega⟩
  intro hper
  have h := sum_unionCoeff_mul_analyticOrderNatAt_eq_of_eventuallyPeriodic hA hP hper
  have hint : IsIntegral ℤ (∑ χ ∈ nonprincipal q,
      unionCoeff A χ * (analyticOrderNatAt (LFunction χ) (1 / 2) : ℂ)) :=
    IsIntegral.sum _ fun χ _ ↦ (isIntegral_unionCoeff hA χ).mul (isIntegral_natCast _)
  rw [h] at hint
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨k, hk⟩ := even_card_sq_mem hq hA
  refine Complex.not_isIntegral_intCast_div_two
    (n := (#A : ℤ) - #{r : ZMod q | r ^ 2 ∈ A}) ⟨(m : ℤ) - k, by rw [hm, hk]; push_cast; ring⟩ ?_
  push_cast
  exact hint

open DirichletCharacter in
/-- **T2: even unions under Chowla's hypothesis.** If `ν(A) = #{r mod q | r² ∈ A}` differs from
`|A|` and `L(1 / 2, χ) ≠ 0` for every nonprincipal `χ` modulo `q`, then the digits
`[pₖ mod q ∈ A]` are not eventually periodic. -/
theorem Nat.not_eventuallyPeriodic_nthPrime_mem_of_chowla {q : ℕ} [NeZero q]
    (hχ : ChowlaHypothesis q) {A : Finset (ZMod q)} (hA : ∀ a ∈ A, IsUnit a)
    (hν : #{r : ZMod q | r ^ 2 ∈ A} ≠ #A) {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic
      (fun k ↦ if (Nat.nth Nat.Prime k : ZMod q) ∈ A then 1 else 0) P :=
  not_eventuallyPeriodic_of_LFunction_ne_zero hA
    (fun χ hχ' _ ↦ hχ χ (mem_nonprincipal.1 hχ')) hν hP

open DirichletCharacter in
/-- **Pairs `{1, a}`** (unconditional). For a unit `a ≠ 1` modulo `q` with `ν({1, a}) > 2`, the
digits `[pₖ mod q ∈ {1, a}]` are not eventually periodic. Here `|A| = 2` is even, so T1 does not
apply; but `re c_χ(A) = 1 + re χ(a⁻¹) ≥ 0` for every `χ`, so positivity applies
(`not_eventuallyPeriodic_of_re_unionCoeff_mul_nonneg`). -/
theorem Nat.not_eventuallyPeriodic_nthPrime_mem_one_pair {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (ha1 : a ≠ 1)
    (hν : 2 < #{r : ZMod q | r ^ 2 ∈ ({1, a} : Finset (ZMod q))}) {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic
      (fun k ↦ if (Nat.nth Nat.Prime k : ZMod q) ∈ ({1, a} : Finset (ZMod q)) then 1 else 0) P := by
  have h1a : (1 : ZMod q) ≠ a := Ne.symm ha1
  have hA : ∀ b ∈ ({1, a} : Finset (ZMod q)), IsUnit b := by
    intro b hb
    rcases mem_insert.1 hb with rfl | hb
    · exact isUnit_one
    · rw [mem_singleton.1 hb]
      exact ha
  have hcard : #({1, a} : Finset (ZMod q)) = 2 := Finset.card_pair h1a
  refine not_eventuallyPeriodic_of_re_unionCoeff_mul_nonneg hA (fun χ _ ↦ mul_nonneg ?_ ?_)
    (by omega) hP
  · rw [unionCoeff, Finset.sum_pair h1a, ZMod.inv_one, map_one, add_re, one_re]
    linarith [neg_abs_le (χ a⁻¹).re, abs_re_le_norm (χ a⁻¹), χ.norm_le_one a⁻¹]
  · rw [hcard, sub_nonneg]
    exact_mod_cast hν.le

open DirichletCharacter in
/-- **Pairs `{1, a}` with `a` a square** (unconditional). For `q ≥ 3` and a unit `a ≠ 1` that is
a square modulo `q`, the digits `[pₖ mod q ∈ {1, a}]` are not eventually periodic:
`ν({1, a}) = ν(1) + ν(a) ≥ 4`, as each of `ν(1)`, `ν(a)` is positive and even. -/
theorem Nat.not_eventuallyPeriodic_nthPrime_mem_one_pair_of_isSquare {q : ℕ} (hq : 3 ≤ q)
    {a : ZMod q} (ha : IsUnit a) (ha1 : a ≠ 1) (hsq : IsSquare a) {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic
      (fun k ↦ if (Nat.nth Nat.Prime k : ZMod q) ∈ ({1, a} : Finset (ZMod q)) then 1 else 0) P := by
  have : NeZero q := ⟨by omega⟩
  refine Nat.not_eventuallyPeriodic_nthPrime_mem_one_pair ha ha1 ?_ hP
  have two_le : ∀ b : ZMod q, IsUnit b → IsSquare b → 2 ≤ #{r : ZMod q | r ^ 2 = b} := by
    intro b hb ⟨c, hc⟩
    have hpos : 0 < #{r : ZMod q | r ^ 2 = b} :=
      Finset.card_pos.2 ⟨c, mem_filter.2 ⟨mem_univ _, by rw [hc, sq]⟩⟩
    have he := even_card_sq_eq hq hb.unit
    rw [IsUnit.unit_spec] at he
    obtain ⟨k, hk⟩ := he
    have : #{r : ZMod q | r ^ 2 = b} = k + k := by convert hk using 2
    omega
  rw [card_sq_mem_eq_sum, Finset.sum_pair (Ne.symm ha1)]
  have := two_le 1 isUnit_one ⟨1, (one_mul 1).symm⟩
  have := two_le a ha hsq
  omega

namespace Real

/-- The **union constant** of modulus `q`, set of residues `A` and base `b`: the number whose
`k`-th base-`b` digit is `1` if `pₖ mod q ∈ A` (with `p₀ = 2`), and `0` otherwise. For
`A = {a}` it is `classConstant q a b`. -/
noncomputable def unionConstant (q : ℕ) (A : Finset (ZMod q)) (b : ℕ) : ℝ :=
  ∑' k : ℕ, (if (Nat.nth Nat.Prime k : ZMod q) ∈ A then (1 : ℝ) else 0) / b ^ (k + 1)

/-- A digit sequence of union type that is never eventually periodic gives an irrational
constant. -/
theorem irrational_unionConstant_of_forall {q b : ℕ} {A : Finset (ZMod q)} (hb : 2 ≤ b)
    (h : ∀ P, 0 < P → ¬ Function.EventuallyPeriodic
      (fun k ↦ if (Nat.nth Nat.Prime k : ZMod q) ∈ A then 1 else 0) P) :
    Irrational (unionConstant q A b) := by
  have h := irrational_tsum_div_pow hb
    (d := fun k ↦ if (Nat.nth Nat.Prime k : ZMod q) ∈ A then 1 else 0)
    (fun k ↦ by split_ifs <;> omega) h
  convert h using 1
  refine tsum_congr fun k ↦ ?_
  split_ifs <;> simp

/-- **Odd union constants are irrational** (T1): for `q ≥ 3`, a set `A` of units with `|A|` odd
and every base `b ≥ 2`, `∑ₖ [pₖ mod q ∈ A] / b ^ (k + 1)` is irrational. -/
theorem irrational_unionConstant_of_odd {q b : ℕ} (hq : 3 ≤ q) {A : Finset (ZMod q)}
    (hA : ∀ a ∈ A, IsUnit a) (hodd : Odd #A) (hb : 2 ≤ b) :
    Irrational (unionConstant q A b) :=
  irrational_unionConstant_of_forall hb fun _ hP ↦
    Nat.not_eventuallyPeriodic_nthPrime_mem_of_odd hq hA hodd hP

/-- **Union constants under Chowla's hypothesis** (T2): if `ν(A) ≠ |A|` and `L(1 / 2, χ) ≠ 0` for
every nonprincipal `χ` modulo `q`, then `∑ₖ [pₖ mod q ∈ A] / b ^ (k + 1)` is irrational. -/
theorem irrational_unionConstant_of_chowla {q b : ℕ} [NeZero q]
    (hχ : DirichletCharacter.ChowlaHypothesis q) {A : Finset (ZMod q)}
    (hA : ∀ a ∈ A, IsUnit a) (hν : #{r : ZMod q | r ^ 2 ∈ A} ≠ #A) (hb : 2 ≤ b) :
    Irrational (unionConstant q A b) :=
  irrational_unionConstant_of_forall hb fun _ hP ↦
    Nat.not_eventuallyPeriodic_nthPrime_mem_of_chowla hχ hA hν hP

end Real

section Examples

/-- For a prime `ℓ`, a set of residues avoiding `0` consists of units. -/
theorem ZMod.isUnit_of_mem_of_zero_notMem {ℓ : ℕ} [Fact ℓ.Prime] {A : Finset (ZMod ℓ)}
    (h0 : (0 : ZMod ℓ) ∉ A) : ∀ a ∈ A, IsUnit a :=
  fun _ ha ↦ isUnit_iff_ne_zero.2 fun h ↦ h0 (h ▸ ha)

/-- **Quadratic residues modulo `7`** (T1): `A = {1, 2, 4}`, `|A| = 3`. The digit determines the
Legendre symbol of `pₖ` modulo `7` for `pₖ ≠ 7`, so this case also follows from
`Real.irrational_legendreConstant`. -/
theorem Nat.not_eventuallyPeriodic_nthPrime_mod_seven_mem_squares {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic (fun k ↦
      if (Nat.nth Nat.Prime k : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)) then 1 else 0) P :=
  Nat.not_eventuallyPeriodic_nthPrime_mem_of_odd (by norm_num)
    (@ZMod.isUnit_of_mem_of_zero_notMem 7 ⟨by norm_num⟩ _ (by decide)) ⟨1, by decide⟩ hP

/-- **A union that is not a union of cosets** (T1): `A = {1, 2, 3}` modulo `7`. No single
character value is determined by the digit, and neither the character routes nor the
single-class theorem apply. -/
theorem Nat.not_eventuallyPeriodic_nthPrime_mod_seven_mem_one_two_three {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic (fun k ↦
      if (Nat.nth Nat.Prime k : ZMod 7) ∈ ({1, 2, 3} : Finset (ZMod 7)) then 1 else 0) P :=
  Nat.not_eventuallyPeriodic_nthPrime_mem_of_odd (by norm_num)
    (@ZMod.isUnit_of_mem_of_zero_notMem 7 ⟨by norm_num⟩ _ (by decide)) ⟨1, by decide⟩ hP

/-- **An even union, unconditionally**: `A = {1, 2}` modulo `7`, with `|A| = 2` and `ν(A) = 4`
(`2 = 3²`). Positivity (`Nat.not_eventuallyPeriodic_nthPrime_mem_one_pair_of_isSquare`) settles
it. -/
theorem Nat.not_eventuallyPeriodic_nthPrime_mod_seven_mem_one_two {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic (fun k ↦
      if (Nat.nth Nat.Prime k : ZMod 7) ∈ ({1, 2} : Finset (ZMod 7)) then 1 else 0) P :=
  Nat.not_eventuallyPeriodic_nthPrime_mem_one_pair_of_isSquare (by norm_num)
    (IsUnit.of_mul_eq_one (b := 4) (by decide)) (by decide) ⟨3, by decide⟩ hP

/-- **A conditional case** (T2): `A = {3, 6}` modulo `7`, with `|A| = 2` and `ν(A) = 0` (both
elements are non-squares). Under Chowla's hypothesis for `q = 7` the digit is not eventually
periodic. Here the multiplicity relation is consistent with simple zeros at `1 / 2` of the two
cubic characters modulo `7` (see `research/unions.md`), so some information about central zeros
is genuinely needed by this method. -/
theorem Nat.not_eventuallyPeriodic_nthPrime_mod_seven_mem_three_six_of_chowla
    (hχ : DirichletCharacter.ChowlaHypothesis 7) {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic (fun k ↦
      if (Nat.nth Nat.Prime k : ZMod 7) ∈ ({3, 6} : Finset (ZMod 7)) then 1 else 0) P :=
  Nat.not_eventuallyPeriodic_nthPrime_mem_of_chowla hχ
    (@ZMod.isUnit_of_mem_of_zero_notMem 7 ⟨by norm_num⟩ _ (by decide)) (by decide) hP

/-- **A silent case**: for `A = {1, 3}` modulo `7`, `ν(A) = |A| = 2`, so the multiplicity relation
reads `∑_{χ ≠ 1} c_χ(A) m_χ = 0`, which holds when no `L(1 / 2, χ)` vanishes: the method gives
nothing, even conditionally. -/
theorem card_sq_mem_one_three_mod_seven :
    #{r : ZMod 7 | r ^ 2 ∈ ({1, 3} : Finset (ZMod 7))} = #({1, 3} : Finset (ZMod 7)) := by
  decide

end Examples
