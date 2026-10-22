/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import RokickiConstant.General.Landau
import RokickiConstant.General.Unions

/-!
# The rate of equidistribution of the primes in one residue class

Let `q ≥ 3`, let `a` be coprime to `q` and let `p₀ = 2 < p₁ < ⋯` be the primes. Write
`π(x; q, a) = #{p < x | p ≡ a (mod q)}` and `π(x) = #{p < x}`. We prove, without the prime number
theorem and without any information on the zeros of Dirichlet `L`-functions:

* `π(x; q, a) - π(x) / φ(q)` is not `O(√x / (log x) ^ β)` for any `β > 1`, so in Landau's notation
  `π(x; q, a) - π(x) / φ(q) = Ω(√x / (log x) ^ (1 + ε))` for every `ε > 0`;
* in the index scale, `E(n) = #{k < n | pₖ ≡ a (mod q)} - n / φ(q)` is not `O(n ^ θ)` for any
  `θ < 1 / 2`, and not `O(√n / (log n) ^ β)` for any `β > 1 / 2`;
* the same for a union `A` of an odd number of unit classes, with `|A| / φ(q)` as the density.

This is the quantitative form of `RokickiConstant.General.SingleClass` and
`RokickiConstant.General.Unions` (where the partial sums of `e(pₖ)` were assumed bounded). The
proof is the same with a quantitative Abel series (`RokickiConstant.General.Oscillation`): a bound
`‖∑_{j ≤ k} e(pⱼ)‖ ≤ C pₖ ^ θ` with `θ < 1 / 2`, or `≤ C pₖ ^ (1 / 2) / (log pₖ) ^ β` with
`β > 1`, makes the Abel series `B` of the centred weight `e` holomorphic on `re s > 1 / 2` and
bounded as `σ → 1 / 2⁺`, with `φ(q) B = ∑_{χ ≠ 1} c_χ(A) primePart χ` on `re s > 1`. The
single-class argument only uses these three properties of `B` (`unionLogOf`): the derivative
identity `(∏ L) Φ_B' = ∑ c_χ L' ∏_{ψ ≠ χ} L` continues to `re s > 1 / 2`, the `L` side gives
`Φ_B(σ) = (∑ c_χ m_χ) log (σ - 1 / 2) + O(1)`, the prime squares give
`Φ_B(σ) = -((ν(A) - |A|) / 2) log (σ - 1 / 2) + O(1)`, and the multiplicity relation
`∑_{χ ≠ 1} c_χ(A) m_χ = (|A| - ν(A)) / 2` contradicts integrality when `|A|` is odd
(`not_exists_differentiableOn_of_odd`).

The method gives no sign: the zeros of the `L(s, χ)` at real points of `[1 / 2, 1)` contribute
`∑ re χ(a⁻¹) m_χ` with weights of both signs, so a one-sided (Chebyshev bias) version needs a
hypothesis on real zeros (see `research/single-class-rate.md`).

## Main statements

* `DirichletCharacter.sum_unionCoeff_mul_analyticOrderNatAt_eq_of_differentiableOn`: the
  multiplicity relation for any continuation `B` holomorphic on `re s > 1 / 2` and bounded at
  `1 / 2⁺`; `DirichletCharacter.not_exists_differentiableOn_of_odd`: no such `B` for odd `|A|`.
* `DirichletCharacter.not_exists_norm_sum_succ_unionWeight_le_nthPrime_rpow`,
  `DirichletCharacter.not_exists_norm_sum_succ_unionWeight_le_nthPrime_rpow_div_log_rpow`: the
  weight sums are neither `O(pₖ ^ θ)`, `θ < 1 / 2`, nor `O(pₖ ^ (1 / 2) / (log pₖ) ^ β)`, `β > 1`.
* `Nat.not_isBigO_card_primesBelow_modEq_sub_rpow_div_log_rpow`,
  `Nat.not_exists_abs_card_primesBelow_modEq_sub_le_rpow_div_log_rpow`: the `x` scale, `β > 1`.
* `Nat.not_isBigO_card_nthPrime_modEq_sub_rpow`,
  `Nat.not_exists_abs_card_nthPrime_modEq_sub_le_rpow`,
  `Nat.not_isBigO_card_primesBelow_modEq_sub_rpow`: the exponent `θ < 1 / 2`.
* `Nat.not_isBigO_card_nthPrime_modEq_sub_rpow_div_log_rpow`,
  `Nat.not_exists_abs_card_nthPrime_modEq_sub_le_rpow_div_log_rpow`: the index scale, `β > 1 / 2`.
* The same for odd unions: `Nat.not_isBigO_card_nthPrime_mem_sub_rpow`,
  `Nat.not_isBigO_card_primesBelow_mem_sub_rpow_div_log_rpow`, and so on.

## Tags

Dirichlet character, residue class, prime number race, Omega theorem, Abel summation
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] {A : Finset (ZMod q)}

section Engine

variable (A) in
/-- The combination `Φ_B(s) = φ(q) B(s) + ∑_{χ ≠ 1} c_χ(A) primePowerPart χ s` for a function `B`
that continues `φ(q)⁻¹ ∑_{χ ≠ 1} c_χ(A) primePart χ s` from `re s > 1`. -/
noncomputable def unionLogOf (B : ℂ → ℂ) (s : ℂ) : ℂ :=
  q.totient * B s + ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePowerPart s

variable {B : ℂ → ℂ}

omit [NeZero q] in
/-- If `φ(q) B = ∑_{χ ≠ 1} c_χ(A) primePart χ` on `re s > 1`, then
`Φ_B(s) = ∑_{χ ≠ 1} c_χ(A) (primePart χ s + primePowerPart χ s)` there. -/
theorem unionLogOf_eq
    (hB1 : ∀ s : ℂ, 1 < s.re →
      (q.totient : ℂ) * B s = ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePart s)
    {s : ℂ} (hs : 1 < s.re) :
    unionLogOf A B s =
      ∑ χ ∈ nonprincipal q, unionCoeff A χ * (χ.primePart s + χ.primePowerPart s) := by
  rw [unionLogOf, hB1 s hs, ← sum_add_distrib]
  simp only [mul_add]

omit [NeZero q] in
/-- If `B` is holomorphic on `re s > 1 / 2`, so is `Φ_B`. -/
theorem differentiableOn_unionLogOf (hB : DifferentiableOn ℂ B {s : ℂ | 1 / 2 < s.re}) :
    DifferentiableOn ℂ (unionLogOf A B) {s : ℂ | 1 / 2 < s.re} :=
  (hB.const_mul _).add
    (DifferentiableOn.fun_sum fun χ _ ↦ χ.differentiableOn_primePowerPart.const_mul _)

/-- `Φ_B' = ∑_{χ ≠ 1} c_χ(A) L'(s, χ) / L(s, χ)` on `re s > 1`. -/
theorem hasDerivAt_unionLogOf
    (hB1 : ∀ s : ℂ, 1 < s.re →
      (q.totient : ℂ) * B s = ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePart s)
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (unionLogOf A B)
      (∑ χ ∈ nonprincipal q, unionCoeff A χ * (deriv (LFunction χ) s / LFunction χ s)) s := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have h : HasDerivAt (fun s ↦ ∑ χ ∈ nonprincipal q,
      unionCoeff A χ * (χ.primePart s + χ.primePowerPart s)) _ s :=
    HasDerivAt.fun_sum fun χ _ ↦ (χ.hasDerivAt_primePart_add_primePowerPart hs).const_mul _
  exact h.congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hs) fun s hs ↦
    unionLogOf_eq hB1 hs)

open Classical in
/-- **Continuation of the logarithmic derivative identity.** If `B` is holomorphic on
`re s > 1 / 2` and `φ(q) B = ∑_{χ ≠ 1} c_χ(A) primePart χ` on `re s > 1`, then on `re s > 1 / 2`,
`(∏_{χ ≠ 1} L(s, χ)) Φ_B'(s) = ∑_{χ ≠ 1} c_χ(A) L'(s, χ) ∏_{ψ ≠ 1, ψ ≠ χ} L(s, ψ)`. -/
theorem prod_mul_deriv_unionLogOf (hB : DifferentiableOn ℂ B {s : ℂ | 1 / 2 < s.re})
    (hB1 : ∀ s : ℂ, 1 < s.re →
      (q.totient : ℂ) * B s = ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePart s)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    (∏ χ ∈ nonprincipal q, LFunction χ s) * deriv (unionLogOf A B) s =
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
      (fun s ↦ (∏ χ ∈ nonprincipal q, LFunction χ s) * deriv (unionLogOf A B) s) U :=
    (((hPr _ subset_rfl).differentiableOn).mul
      ((differentiableOn_unionLogOf hB).deriv hUo)).analyticOnNhd hUo
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
  rw [(hasDerivAt_unionLogOf hB1 hs).deriv, mul_sum]
  refine sum_congr rfl fun χ hχ ↦ ?_
  rw [← mul_prod_erase _ (fun ψ ↦ LFunction ψ s) hχ]
  field_simp [hne χ hχ]

/-- **The prime-square side at `1 / 2`.** If `B` stays bounded as `σ → 1 / 2⁺`, then with
`ν(A) = #{r mod q | r ^ 2 ∈ A}`, `Φ_B(σ) = ((ν(A) - |A|) / 2) log (1 / (σ - 1 / 2)) + O(1)`. -/
theorem exists_norm_unionLogOf_add_mul_log_le (hA : ∀ a ∈ A, IsUnit a)
    (hBb : ∃ M : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖B σ‖ ≤ M) :
    ∃ C' : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖unionLogOf A B σ +
      (((#{r : ZMod q | r ^ 2 ∈ A} : ℕ) : ℂ) - #A) / 2 * Real.log (σ - 1 / 2)‖ ≤ C' := by
  obtain ⟨M₀, hM₀⟩ := hBb
  have hD : ∀ a ∈ A, ∃ C' : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2),
      ‖∑ χ ∈ nonprincipal q, χ a⁻¹ * χ.primePowerPart σ +
        (((#{r : ZMod q | r ^ 2 = a} : ℕ) : ℂ) - 1) / 2 * Real.log (σ - 1 / 2)‖ ≤ C' :=
    fun a ha ↦ exists_norm_sum_primePowerPart_add_mul_log_le (hA a ha)
  choose! M hM using hD
  refine ⟨q.totient * M₀ + ∑ a ∈ A, M a, ?_⟩
  filter_upwards [hM₀, (eventually_all_finset A).2 hM] with σ hσA hσM
  have hν : (((#{r : ZMod q | r ^ 2 ∈ A} : ℕ) : ℂ) - #A) / 2 =
      ∑ a ∈ A, (((#{r : ZMod q | r ^ 2 = a} : ℕ) : ℂ) - 1) / 2 := by
    rw [card_sq_mem_eq_sum, ← sum_div, sum_sub_distrib]
    push_cast
    simp
  have hL : unionLogOf A B σ = q.totient * B σ +
      ∑ a ∈ A, ∑ χ ∈ nonprincipal q, χ a⁻¹ * χ.primePowerPart σ := by
    rw [unionLogOf]
    simp_rw [unionCoeff, sum_mul]
    rw [sum_comm]
  rw [hL, hν, sum_mul, add_assoc, ← sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans
    (sum_le_sum fun a ha ↦ hσM a ha)))
  rw [norm_mul, norm_natCast]
  gcongr

/-- **The multiplicity relation for a continuation.** Let `A` be a set of units and let `B` be
holomorphic on `re s > 1 / 2`, bounded as `σ → 1 / 2⁺`, with
`φ(q) B(s) = ∑_{χ ≠ 1} c_χ(A) primePart χ s` on `re s > 1`. Then
`∑_{χ ≠ 1} c_χ(A) ord_{s = 1/2} L(s, χ) = (|A| - ν(A)) / 2`. -/
theorem sum_unionCoeff_mul_analyticOrderNatAt_eq_of_differentiableOn (hA : ∀ a ∈ A, IsUnit a)
    (hB : DifferentiableOn ℂ B {s : ℂ | 1 / 2 < s.re})
    (hB1 : ∀ s : ℂ, 1 < s.re →
      (q.totient : ℂ) * B s = ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePart s)
    (hBb : ∃ M : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖B σ‖ ≤ M) :
    ∑ χ ∈ nonprincipal q, unionCoeff A χ * (analyticOrderNatAt (LFunction χ) (1 / 2) : ℂ) =
      ((#A : ℂ) - #{r : ZMod q | r ^ 2 ∈ A}) / 2 := by
  classical
  obtain ⟨C₁, h₁⟩ := exists_norm_unionLogOf_add_mul_log_le hA hBb
  have hΦ : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), DifferentiableAt ℂ (unionLogOf A B) σ ∧
      (∏ χ ∈ nonprincipal q, LFunction χ σ) * deriv (unionLogOf A B) σ =
        ∑ χ ∈ nonprincipal q, unionCoeff A χ * deriv (LFunction χ) σ *
          ∏ ψ ∈ (nonprincipal q).erase χ, LFunction ψ σ := by
    refine eventually_nhdsWithin_of_forall fun σ (hσ : 1 / 2 < σ) ↦ ?_
    have hσ' : 1 / 2 < (σ : ℂ).re := by simpa using hσ
    exact ⟨(differentiableOn_unionLogOf hB).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hσ'),
      prod_mul_deriv_unionLogOf hB hB1 hσ'⟩
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
        ‖(unionLogOf A B σ + ((ν : ℂ) - #A) / 2 * Real.log (σ - 1 / 2)) -
          (unionLogOf A B σ - x * Real.log (σ - 1 / 2))‖ := by ring_nf
      _ ≤ C₁ + C₂ := (norm_sub_le _ _).trans (add_le_add h1 h2)
  linear_combination hx

/-- **No continuation for odd unions.** For `q ≥ 3` and a set `A` of units with `|A|` odd, the
function `φ(q)⁻¹ ∑_{χ ≠ 1} c_χ(A) primePart χ s` (the Dirichlet series
`∑ₖ ([pₖ ∈ A] - |A| [pₖ ∤ q] / φ(q)) pₖ ^ (-s)`) has no continuation from `re s > 1` to a
holomorphic function on `re s > 1 / 2` that stays bounded as `σ → 1 / 2⁺`. -/
theorem not_exists_differentiableOn_of_odd (hq : 3 ≤ q) (hA : ∀ a ∈ A, IsUnit a)
    (hodd : _root_.Odd #A) :
    ¬ ∃ B : ℂ → ℂ, DifferentiableOn ℂ B {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        (q.totient : ℂ) * B s = ∑ χ ∈ nonprincipal q, unionCoeff A χ * χ.primePart s) ∧
      ∃ M : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖B σ‖ ≤ M := by
  rintro ⟨B, hB, hB1, hBb⟩
  have h := sum_unionCoeff_mul_analyticOrderNatAt_eq_of_differentiableOn hA hB hB1 hBb
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

end Engine

section Growth

/-- If `F σ → c` as `σ → 1 / 2⁺`, then `F` is bounded on a right neighbourhood of `1 / 2`. -/
theorem exists_eventually_norm_le_of_tendsto {F : ℂ → ℂ} {c : ℂ}
    (h : Tendsto (fun σ : ℝ ↦ F σ) (𝓝[>] (1 / 2)) (𝓝 c)) :
    ∃ M : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖F σ‖ ≤ M :=
  ⟨‖c‖ + 1, h.norm.eventually (eventually_le_nhds (lt_add_one _))⟩

/-- **Polynomial growth.** For `q ≥ 3`, a set `A` of units with `|A|` odd and `θ < 1 / 2`, the
partial sums of `e(pₖ) = [pₖ ∈ A] - |A| [pₖ ∤ q] / φ(q)` are not `O(pₖ ^ θ)`: there is no `C` with
`‖∑_{j ≤ k} e(pⱼ)‖ ≤ C pₖ ^ θ` for all `k`. Such a bound makes the Abel series of `e(pₖ)`
holomorphic on `re s > max θ 0`, in particular at `1 / 2`, which
`not_exists_differentiableOn_of_odd` excludes. -/
theorem not_exists_norm_sum_succ_unionWeight_le_nthPrime_rpow (hq : 3 ≤ q)
    (hA : ∀ a ∈ A, IsUnit a) (hodd : _root_.Odd #A) {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ k, ‖∑ j ∈ range (k + 1), unionWeight A (nthPrime j)‖ ≤
      C * (nthPrime k : ℝ) ^ θ := by
  rintro ⟨C, hC⟩
  have hC' : ∀ k, ‖∑ j ∈ range (k + 1), unionWeight A (nthPrime j)‖ ≤
      |C| * (nthPrime k : ℝ) ^ max θ 0 := fun k ↦ (hC k).trans
    (mul_rpow_le_abs_mul_rpow_max (Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le) le_rfl)
  have hθ' : max θ 0 < 1 / 2 := max_lt hθ (by norm_num)
  set F := abelSeries (fun k ↦ unionWeight A (nthPrime k)) nthPrime
  have hd : DifferentiableOn ℂ F {s : ℂ | max θ 0 < s.re} :=
    differentiableOn_abelSeries_of_le_rpow (le_max_right θ 0) hC' (Nat.prime_nth_prime 0).pos
      nthPrime_strictMono
  have hF : ContinuousAt F ((1 / 2 : ℝ) : ℂ) :=
    (hd.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show max θ 0 < ((1 / 2 : ℝ) : ℂ).re by simpa using hθ'))).continuousAt
  refine not_exists_differentiableOn_of_odd hq hA hodd ⟨F,
    hd.mono fun s (hs : 1 / 2 < s.re) ↦ show max θ 0 < s.re by linarith, fun s hs ↦ ?_,
    exists_eventually_norm_le_of_tendsto
      ((hF.tendsto.comp (continuous_ofReal.tendsto _)).mono_left nhdsWithin_le_nhds)⟩
  rw [← totient_mul_tsum_unionWeight hA hs]
  exact congrArg _ (abelSeries_eq_tsum_of_le_rpow (le_max_right θ 0) hC'
    (fun k ↦ norm_unionWeight_le A _) (Nat.prime_nth_prime 0).pos nthPrime_strictMono hs
    (by linarith))

/-- **Log-power growth at the exponent `1 / 2`.** For `q ≥ 3`, a set `A` of units with `|A|` odd
and `β > 1`, there is no `C` with `‖∑_{j ≤ k} e(pⱼ)‖ ≤ C pₖ ^ (1 / 2) / (log pₖ) ^ β` for all `k`.
Such a bound makes the Abel series holomorphic on `re s > 1 / 2` and, by uniform convergence on
`[1 / 2, 2]` (`continuousOn_abelSeries_of_le_rpow_div_log_rpow`), continuous at `σ = 1 / 2` from
the right. -/
theorem not_exists_norm_sum_succ_unionWeight_le_nthPrime_rpow_div_log_rpow (hq : 3 ≤ q)
    (hA : ∀ a ∈ A, IsUnit a) (hodd : _root_.Odd #A) {β : ℝ} (hβ : 1 < β) :
    ¬ ∃ C : ℝ, ∀ k, ‖∑ j ∈ range (k + 1), unionWeight A (nthPrime j)‖ ≤
      C * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ β := by
  rintro ⟨C, hC⟩
  have hq₀ : 2 ≤ nthPrime 0 := (Nat.prime_nth_prime 0).two_le
  have hC' : ∀ k, ‖∑ j ∈ range (k + 1), unionWeight A (nthPrime j)‖ ≤
      |C| / Real.log 2 ^ β * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) := fun k ↦ by
    have hp : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast (Nat.prime_nth_prime k).two_le
    have hl : Real.log 2 ^ β ≤ Real.log (nthPrime k) ^ β :=
      Real.rpow_le_rpow (Real.log_nonneg one_le_two) (Real.log_le_log two_pos hp) (by linarith)
    have hl0 : 0 < Real.log 2 ^ β := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) β
    refine (hC k).trans ?_
    calc C * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ β ≤
          |C| * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ β := by
          gcongr
          exact le_abs_self C
      _ ≤ |C| * (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log 2 ^ β :=
          div_le_div_of_nonneg_left (by positivity) hl0 hl
      _ = _ := by ring
  set F := abelSeries (fun k ↦ unionWeight A (nthPrime k)) nthPrime
  have hF : Tendsto (fun σ : ℝ ↦ F σ) (𝓝[>] (1 / 2)) (𝓝 (F ((1 / 2 : ℝ) : ℂ))) :=
    (((continuousOn_abelSeries_of_le_rpow_div_log_rpow hβ hC hq₀ nthPrime_strictMono
      Nat.nth_prime_succ_le_two_mul) (1 / 2) ⟨le_rfl, by norm_num⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT (by norm_num))).tendsto
  refine not_exists_differentiableOn_of_odd hq hA hodd ⟨F,
    differentiableOn_abelSeries_of_le_rpow (by norm_num) hC' (Nat.prime_nth_prime 0).pos
      nthPrime_strictMono, fun s hs ↦ ?_, exists_eventually_norm_le_of_tendsto hF⟩
  rw [← totient_mul_tsum_unionWeight hA hs]
  exact congrArg _ (abelSeries_eq_tsum_of_le_rpow (by norm_num) hC'
    (fun k ↦ norm_unionWeight_le A _) (Nat.prime_nth_prime 0).pos nthPrime_strictMono hs
    (by linarith))

end Growth

section Counting

/-- `|∑_{k < n} re 1(pₖ) - n| ≤ q`: only the primes `pₖ ∣ q`, all with `k < q`, are not units. -/
theorem abs_sum_re_one_apply_nthPrime_sub_le (n : ℕ) :
    |∑ k ∈ range n, ((1 : DirichletCharacter ℂ q) (nthPrime k)).re - n| ≤ q := by
  calc _ = |∑ k ∈ range n, (((1 : DirichletCharacter ℂ q) (nthPrime k)).re - 1)| := by
        simp [sum_sub_distrib]
    _ ≤ ∑ k ∈ range n, (if k < q then (1 : ℝ) else 0) := (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun k _ ↦ abs_re_one_apply_nthPrime_sub_one_le k)
    _ ≤ q := by
        rw [sum_boole]
        exact_mod_cast (card_le_card fun k hk ↦ by
          simp only [mem_filter, mem_range] at hk ⊢; exact hk.2).trans (card_range q).le

variable (A) in
/-- The **discrepancy** `E_A(n) = #{k < n | pₖ mod q ∈ A} - |A| n / φ(q)` of the first `n` primes
in the union `A` of residue classes. -/
noncomputable def unionDiscrepancy (n : ℕ) : ℝ :=
  #{k ∈ range n | (nthPrime k : ZMod q) ∈ A} - #A * n / q.totient

omit [NeZero q] in
/-- `E_A(0) = 0`. -/
@[simp]
theorem unionDiscrepancy_zero : unionDiscrepancy A 0 = 0 := by
  simp [unionDiscrepancy]

variable (A) in
/-- The partial sums of the centred weight differ from the discrepancy by a bounded amount:
`‖∑_{k < n} e(pₖ)‖ ≤ |E_A(n)| + |A| q / φ(q)`. -/
theorem norm_sum_unionWeight_le (n : ℕ) :
    ‖∑ k ∈ range n, unionWeight A (nthPrime k)‖ ≤
      |unionDiscrepancy A n| + #A * q / q.totient := by
  set κ : ℝ := #A * (q.totient : ℝ)⁻¹
  have hκ : 0 ≤ κ := by positivity
  have h : ∑ k ∈ range n, unionWeight A (nthPrime k) =
      ((∑ k ∈ range n, (unionWeight A (nthPrime k)).re : ℝ) : ℂ) := by
    push_cast
    exact sum_congr rfl fun k _ ↦ (ofReal_re_unionWeight A _).symm
  have he : ∑ k ∈ range n, (unionWeight A (nthPrime k)).re = unionDiscrepancy A n -
      κ * (∑ k ∈ range n, ((1 : DirichletCharacter ℂ q) (nthPrime k)).re - n) := by
    simp only [re_unionWeight_natCast, sum_sub_distrib, unionDiscrepancy,
      Finset.natCast_card_filter, ← mul_sum, κ]
    ring
  rw [h, norm_real, Real.norm_eq_abs, he]
  refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_nonneg hκ]
  calc κ * _ ≤ κ * q := mul_le_mul_of_nonneg_left (abs_sum_re_one_apply_nthPrime_sub_le n) hκ
    _ = _ := by simp only [κ]; ring

omit [NeZero q] in
/-- Counting primes below `x` with a property is counting the first `π'(x)` primes with it. -/
theorem card_primesBelow_filter (x : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    #{p ∈ Nat.primesBelow x | P p} = #{k ∈ range (Nat.primeCounting' x) | P (nthPrime k)} := by
  have h : Nat.primesBelow x = (range (Nat.primeCounting' x)).image nthPrime := by
    ext p
    simp only [Nat.mem_primesBelow, mem_image, mem_range]
    constructor
    · rintro ⟨hpx, hp⟩
      refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hp⟩
      exact (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2 (by rwa [Nat.nth_count hp])
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).1 hk, Nat.prime_nth_prime k⟩
  rw [h, filter_image, card_image_of_injective _ nthPrime_strictMono.injective]

omit [NeZero q] in
/-- The discrepancy in the `x` scale: `π_A(x) - |A| π(x) / φ(q) = E_A(π(x))`, where
`π_A(x) = #{p < x | p mod q ∈ A}` and `π(x) = π'(x)` counts the primes below `x`. -/
theorem card_primesBelow_mem_sub_eq (x : ℕ) :
    (#{p ∈ Nat.primesBelow x | ((p : ℕ) : ZMod q) ∈ A} : ℝ) -
        #A * Nat.primeCounting' x / q.totient =
      unionDiscrepancy A (Nat.primeCounting' x) := by
  rw [card_primesBelow_filter, unionDiscrepancy]

/-- `π'(pₖ + 1) = k + 1`. -/
theorem primeCounting'_nthPrime_add_one (k : ℕ) : Nat.primeCounting' (nthPrime k + 1) = k + 1 :=
  Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k

/-- For `x > 1` and `β > 0`, `1 ≤ (2 β) ^ β x ^ (1 / 2) / (log x) ^ β`: from
`log x ≤ 2 β x ^ (1 / (2 β))`. -/
theorem one_le_mul_rpow_div_log_rpow {x β : ℝ} (hx : 1 < x) (hβ : 0 < β) :
    1 ≤ (2 * β) ^ β * (x ^ (1 / 2 : ℝ) / Real.log x ^ β) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have h1 := Real.log_le_rpow_div (by linarith : 0 ≤ x) (by positivity : 0 < 1 / (2 * β))
  rw [div_div_eq_mul_div, div_one] at h1
  have h2 : Real.log x ^ β ≤ (2 * β) ^ β * x ^ (1 / 2 : ℝ) := by
    calc Real.log x ^ β ≤ (x ^ (1 / (2 * β)) * (2 * β)) ^ β :=
          Real.rpow_le_rpow hl.le h1 hβ.le
      _ = (2 * β) ^ β * x ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by linarith),
            mul_comm]
          congr 2
          field_simp
  rw [mul_div_assoc', le_div_iff₀ (Real.rpow_pos_of_pos hl β), one_mul]
  exact h2

/-- **Polynomial growth, prime scale.** For `q ≥ 3`, a set `A` of units with `|A|` odd and
`θ < 1 / 2`, the discrepancy `E_A(k + 1)` of the primes up to `pₖ` is not `O(pₖ ^ θ)`. -/
theorem not_isBigO_unionDiscrepancy_succ_nthPrime_rpow (hq : 3 ≤ q) (hA : ∀ a ∈ A, IsUnit a)
    (hodd : _root_.Odd #A) {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ (fun k ↦ unionDiscrepancy A (k + 1)) =O[atTop] fun k ↦ (nthPrime k : ℝ) ^ θ := by
  intro h
  obtain ⟨C, hC⟩ := exists_forall_norm_le_mul_of_isBigO (fun k ↦ Real.rpow_pos_of_pos
    (by exact_mod_cast (Nat.prime_nth_prime k).pos) θ) h
  set K : ℝ := #A * q / q.totient
  have hK : 0 ≤ K := by positivity
  refine not_exists_norm_sum_succ_unionWeight_le_nthPrime_rpow hq hA hodd
    (max_lt hθ (by norm_num : (0 : ℝ) < 1 / 2)) ⟨|C| + K, fun k ↦ ?_⟩
  have hp : (1 : ℝ) ≤ nthPrime k := Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le
  have h1 : 1 ≤ (nthPrime k : ℝ) ^ max θ 0 := Real.one_le_rpow hp (le_max_right _ _)
  calc _ ≤ |unionDiscrepancy A (k + 1)| + K := norm_sum_unionWeight_le A _
    _ ≤ C * (nthPrime k : ℝ) ^ θ + K := by
        rw [← Real.norm_eq_abs]
        exact add_le_add (hC k) le_rfl
    _ ≤ |C| * (nthPrime k : ℝ) ^ max θ 0 + K * (nthPrime k : ℝ) ^ max θ 0 :=
        add_le_add (mul_rpow_le_abs_mul_rpow_max hp le_rfl) (le_mul_of_one_le_right hK h1)
    _ = _ := by ring

/-- **Log-power growth, prime scale.** For `q ≥ 3`, a set `A` of units with `|A|` odd and
`β > 1`, the discrepancy `E_A(k + 1)` of the primes up to `pₖ` is not
`O(pₖ ^ (1 / 2) / (log pₖ) ^ β)`. -/
theorem not_isBigO_unionDiscrepancy_succ_nthPrime_rpow_div_log_rpow (hq : 3 ≤ q)
    (hA : ∀ a ∈ A, IsUnit a) (hodd : _root_.Odd #A) {β : ℝ} (hβ : 1 < β) :
    ¬ (fun k ↦ unionDiscrepancy A (k + 1)) =O[atTop]
      fun k ↦ (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ β := by
  intro h
  have hp1 : ∀ k, (1 : ℝ) < nthPrime k := fun k ↦ by
    exact_mod_cast (Nat.prime_nth_prime k).one_lt
  obtain ⟨C, hC⟩ := exists_forall_norm_le_mul_of_isBigO
    (fun k ↦ rpow_div_log_rpow_pos (hp1 k) _ _) h
  set K : ℝ := #A * q / q.totient
  have hK : 0 ≤ K := by positivity
  refine not_exists_norm_sum_succ_unionWeight_le_nthPrime_rpow_div_log_rpow hq hA hodd hβ
    ⟨|C| + K * (2 * β) ^ β, fun k ↦ ?_⟩
  set g : ℝ := (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ β
  have hg : 0 ≤ g := (rpow_div_log_rpow_pos (hp1 k) _ _).le
  have h1 := one_le_mul_rpow_div_log_rpow (hp1 k) (by linarith : 0 < β)
  calc _ ≤ |unionDiscrepancy A (k + 1)| + K := norm_sum_unionWeight_le A _
    _ ≤ |C| * g + K * ((2 * β) ^ β * g) := by
        rw [← Real.norm_eq_abs]
        exact add_le_add ((hC k).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hg))
          (le_mul_of_one_le_right hK h1)
    _ = _ := by simp only [g]; ring

end Counting

end DirichletCharacter

/-- Chebyshev in the index scale:
`k ^ (1 / 2) / (log k) ^ β = O(pₖ ^ (1 / 2) / (log pₖ) ^ (β + 1 / 2))` for `β ≥ 0`, via
`k log pₖ ≤ 5 pₖ` and `log pₖ ≤ 2 log k` for `k ≥ 4096` (`rpow_div_log_rpow_le_nthPrime`). -/
theorem Nat.isBigO_rpow_div_log_rpow_nth_prime {β : ℝ} (hβ : 0 ≤ β) :
    (fun k : ℕ ↦ (k : ℝ) ^ (1 / 2 : ℝ) / Real.log k ^ β) =O[atTop]
      fun k ↦ (nthPrime k : ℝ) ^ (1 / 2 : ℝ) / Real.log (nthPrime k) ^ (β + 1 / 2) := by
  refine .of_bound ((5 : ℝ) ^ (1 / 2 : ℝ) * 2 ^ β) ?_
  filter_upwards [eventually_ge_atTop 4096] with k hk
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hkp : (k : ℝ) ≤ nthPrime k := by
    exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)
  rw [Real.norm_of_nonneg (rpow_div_log_rpow_pos hk1 _ _).le,
    Real.norm_of_nonneg (rpow_div_log_rpow_pos (hk1.trans_le hkp) _ _).le]
  exact rpow_div_log_rpow_le_nthPrime hk hβ

/-- A function that is not `O(g)` admits no bound `|f n| ≤ C g n` for `n ≥ N`. -/
theorem not_exists_abs_le_mul_of_not_isBigO {f g : ℕ → ℝ} {N : ℕ} (hg : ∀ n, N ≤ n → 0 ≤ g n)
    (h : ¬ f =O[atTop] g) : ¬ ∃ C : ℝ, ∀ n, N ≤ n → |f n| ≤ C * g n := by
  rintro ⟨C, hC⟩
  refine h (.of_bound C ?_)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (hg n hn)]
  exact hC n hn

open DirichletCharacter

section Unions

variable {q : ℕ} {A : Finset (ZMod q)}

/-- **Rate of equidistribution for an odd union, index scale.** For `q ≥ 3`, a set `A` of units
modulo `q` with `|A|` odd and `θ < 1 / 2`, the discrepancy
`#{k < n | pₖ mod q ∈ A} - |A| n / φ(q)` is not `O(n ^ θ)`. -/
theorem Nat.not_isBigO_card_nthPrime_mem_sub_rpow (hq : 3 ≤ q) (hA : ∀ a ∈ A, IsUnit a)
    (hodd : _root_.Odd #A) {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ (fun n : ℕ ↦ (#{k ∈ range n | (nthPrime k : ZMod q) ∈ A} : ℝ) - #A * n / q.totient)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ θ := by
  have : NeZero q := ⟨by omega⟩
  intro h
  change unionDiscrepancy A =O[atTop] _ at h
  refine not_isBigO_unionDiscrepancy_succ_nthPrime_rpow hq hA hodd
    (max_lt hθ (by norm_num : (0 : ℝ) < 1 / 2))
    ((h.comp_tendsto (tendsto_add_atTop_nat 1)).trans (.of_bound 1 (.of_forall fun k ↦ ?_)))
  have hp : ((k + 1 : ℕ) : ℝ) ≤ nthPrime k := by
    exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)
  simp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  simpa using mul_rpow_le_abs_mul_rpow_max (C := 1) (θ := θ)
    (Nat.one_le_cast.2 (Nat.succ_pos k)) hp

/-- **Rate of equidistribution for an odd union, index scale.** For `q ≥ 3`, a set `A` of units
with `|A|` odd and `θ < 1 / 2`, there is no `C` with
`|#{k < n | pₖ mod q ∈ A} - |A| n / φ(q)| ≤ C n ^ θ` for all `n`. -/
theorem Nat.not_exists_abs_card_nthPrime_mem_sub_le_rpow (hq : 3 ≤ q) (hA : ∀ a ∈ A, IsUnit a)
    (hodd : _root_.Odd #A) {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      |(#{k ∈ range n | (nthPrime k : ZMod q) ∈ A} : ℝ) - #A * n / q.totient| ≤
        C * (n : ℝ) ^ θ := fun ⟨C, hC⟩ ↦
  not_exists_abs_le_mul_of_not_isBigO (N := 0) (fun n _ ↦ by positivity)
    (Nat.not_isBigO_card_nthPrime_mem_sub_rpow hq hA hodd hθ) ⟨C, fun n _ ↦ hC n⟩

/-- **Rate of equidistribution for an odd union, `x` scale.** For `q ≥ 3`, a set `A` of units
with `|A|` odd and `θ < 1 / 2`, `π_A(x) - |A| π(x) / φ(q)` is not `O(x ^ θ)`, where
`π_A(x) = #{p < x | p mod q ∈ A}` and `π(x) = π'(x)` is the number of primes below `x`. -/
theorem Nat.not_isBigO_card_primesBelow_mem_sub_rpow (hq : 3 ≤ q) (hA : ∀ a ∈ A, IsUnit a)
    (hodd : _root_.Odd #A) {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ (fun x : ℕ ↦ (#{p ∈ Nat.primesBelow x | ((p : ℕ) : ZMod q) ∈ A} : ℝ) -
      #A * Nat.primeCounting' x / q.totient) =O[atTop] fun x : ℕ ↦ (x : ℝ) ^ θ := by
  have : NeZero q := ⟨by omega⟩
  intro h
  rw [show (fun x : ℕ ↦ (#{p ∈ Nat.primesBelow x | ((p : ℕ) : ZMod q) ∈ A} : ℝ) -
      #A * Nat.primeCounting' x / q.totient) = unionDiscrepancy A ∘ Nat.primeCounting' from
    funext fun x ↦ card_primesBelow_mem_sub_eq x] at h
  have h' := h.comp_tendsto (k := fun k ↦ nthPrime k + 1)
    ((tendsto_add_atTop_nat 1).comp nthPrime_strictMono.tendsto_atTop)
  refine not_isBigO_unionDiscrepancy_succ_nthPrime_rpow hq hA hodd
    (max_lt hθ (by norm_num : (0 : ℝ) < 1 / 2)) ?_
  rw [show (fun k ↦ unionDiscrepancy A (k + 1)) =
      (unionDiscrepancy A ∘ Nat.primeCounting') ∘ fun k ↦ nthPrime k + 1 from
    funext fun k ↦ by simp [primeCounting'_nthPrime_add_one]]
  refine h'.trans (.of_bound (2 ^ max θ 0) (.of_forall fun k ↦ ?_))
  have hp : (1 : ℝ) ≤ nthPrime k := Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    ← Real.mul_rpow (by norm_num) (by positivity)]
  simpa using mul_rpow_le_abs_mul_rpow_max (C := 1) (θ := θ)
    (x := (nthPrime k : ℝ) + 1) (y := 2 * nthPrime k) (by linarith) (by linarith)

/-- **Rate of equidistribution for an odd union, log-power form, `x` scale.** For `q ≥ 3`, a set
`A` of units with `|A|` odd and `β > 1`, `π_A(x) - |A| π(x) / φ(q)` is not
`O(x ^ (1 / 2) / (log x) ^ β)`. -/
theorem Nat.not_isBigO_card_primesBelow_mem_sub_rpow_div_log_rpow (hq : 3 ≤ q)
    (hA : ∀ a ∈ A, IsUnit a) (hodd : _root_.Odd #A) {β : ℝ} (hβ : 1 < β) :
    ¬ (fun x : ℕ ↦ (#{p ∈ Nat.primesBelow x | ((p : ℕ) : ZMod q) ∈ A} : ℝ) -
      #A * Nat.primeCounting' x / q.totient) =O[atTop]
        fun x : ℕ ↦ (x : ℝ) ^ (1 / 2 : ℝ) / Real.log x ^ β := by
  have : NeZero q := ⟨by omega⟩
  intro h
  rw [show (fun x : ℕ ↦ (#{p ∈ Nat.primesBelow x | ((p : ℕ) : ZMod q) ∈ A} : ℝ) -
      #A * Nat.primeCounting' x / q.totient) = unionDiscrepancy A ∘ Nat.primeCounting' from
    funext fun x ↦ card_primesBelow_mem_sub_eq x] at h
  have h' := h.comp_tendsto (k := fun k ↦ nthPrime k + 1)
    ((tendsto_add_atTop_nat 1).comp nthPrime_strictMono.tendsto_atTop)
  refine not_isBigO_unionDiscrepancy_succ_nthPrime_rpow_div_log_rpow hq hA hodd hβ ?_
  rw [show (fun k ↦ unionDiscrepancy A (k + 1)) =
      (unionDiscrepancy A ∘ Nat.primeCounting') ∘ fun k ↦ nthPrime k + 1 from
    funext fun k ↦ by simp [primeCounting'_nthPrime_add_one]]
  refine h'.trans (.of_bound (2 ^ (1 / 2 : ℝ)) (.of_forall fun k ↦ ?_))
  have hp : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast (Nat.prime_nth_prime k).two_le
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [Real.norm_of_nonneg (rpow_div_log_rpow_pos (by linarith) _ _).le,
    Real.norm_of_nonneg (rpow_div_log_rpow_pos (by linarith) _ _).le]
  exact rpow_div_log_rpow_add_one_le hp (by linarith)

/-- **Rate of equidistribution for an odd union, log-power form.** For `q ≥ 3`, a set `A` of
units with `|A|` odd and `β > 1`, there is no `C` with
`|π_A(x) - |A| π(x) / φ(q)| ≤ C x ^ (1 / 2) / (log x) ^ β` for all `x ≥ 2`. -/
theorem Nat.not_exists_abs_card_primesBelow_mem_sub_le_rpow_div_log_rpow (hq : 3 ≤ q)
    (hA : ∀ a ∈ A, IsUnit a) (hodd : _root_.Odd #A) {β : ℝ} (hβ : 1 < β) :
    ¬ ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |(#{p ∈ Nat.primesBelow x | ((p : ℕ) : ZMod q) ∈ A} : ℝ) -
        #A * Nat.primeCounting' x / q.totient| ≤
          C * (x : ℝ) ^ (1 / 2 : ℝ) / Real.log x ^ β := fun ⟨C, hC⟩ ↦
  not_exists_abs_le_mul_of_not_isBigO
    (fun x hx ↦ (rpow_div_log_rpow_pos (by exact_mod_cast hx) _ _).le)
    (Nat.not_isBigO_card_primesBelow_mem_sub_rpow_div_log_rpow hq hA hodd hβ)
    ⟨C, fun x hx ↦ (hC x hx).trans_eq (mul_div_assoc _ _ _)⟩

/-- **Rate of equidistribution for an odd union, log-power form, index scale.** For `q ≥ 3`, a set
`A` of units with `|A|` odd and `β > 1 / 2`, `#{k < n | pₖ mod q ∈ A} - |A| n / φ(q)` is not
`O(n ^ (1 / 2) / (log n) ^ β)`. -/
theorem Nat.not_isBigO_card_nthPrime_mem_sub_rpow_div_log_rpow (hq : 3 ≤ q)
    (hA : ∀ a ∈ A, IsUnit a) (hodd : _root_.Odd #A) {β : ℝ} (hβ : 1 / 2 < β) :
    ¬ (fun n : ℕ ↦ (#{k ∈ range n | (nthPrime k : ZMod q) ∈ A} : ℝ) - #A * n / q.totient)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ β := by
  have : NeZero q := ⟨by omega⟩
  intro h
  change unionDiscrepancy A =O[atTop] _ at h
  refine not_isBigO_unionDiscrepancy_succ_nthPrime_rpow_div_log_rpow hq hA hodd
    (β := β + 1 / 2) (by linarith) (((h.comp_tendsto (tendsto_add_atTop_nat 1)).trans
      (.of_bound (2 ^ (1 / 2 : ℝ)) ?_)).trans (Nat.isBigO_rpow_div_log_rpow_nth_prime
        (by linarith)))
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [Real.norm_of_nonneg (rpow_div_log_rpow_pos (by linarith) _ _).le,
    Real.norm_of_nonneg (rpow_div_log_rpow_pos (by linarith) _ _).le]
  exact rpow_div_log_rpow_add_one_le hk2 (by linarith)

/-- **Rate of equidistribution for an odd union, log-power form, index scale.** For `q ≥ 3`, a set
`A` of units with `|A|` odd and `β > 1 / 2`, there is no `C` with
`|#{k < n | pₖ mod q ∈ A} - |A| n / φ(q)| ≤ C n ^ (1 / 2) / (log n) ^ β` for all `n ≥ 2`. -/
theorem Nat.not_exists_abs_card_nthPrime_mem_sub_le_rpow_div_log_rpow (hq : 3 ≤ q)
    (hA : ∀ a ∈ A, IsUnit a) (hodd : _root_.Odd #A) {β : ℝ} (hβ : 1 / 2 < β) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |(#{k ∈ range n | (nthPrime k : ZMod q) ∈ A} : ℝ) - #A * n / q.totient| ≤
        C * (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ β := fun ⟨C, hC⟩ ↦
  not_exists_abs_le_mul_of_not_isBigO
    (fun n hn ↦ (rpow_div_log_rpow_pos (by exact_mod_cast hn) _ _).le)
    (Nat.not_isBigO_card_nthPrime_mem_sub_rpow_div_log_rpow hq hA hodd hβ)
    ⟨C, fun n hn ↦ (hC n hn).trans_eq (mul_div_assoc _ _ _)⟩

end Unions

section SingleClass

variable {q a : ℕ}

/-- Membership in the singleton `{a mod q}` is congruence modulo `q`. -/
theorem card_filter_natCast_mem_singleton (s : Finset ℕ) (f : ℕ → ℕ) :
    #{k ∈ s | ((f k : ℕ) : ZMod q) ∈ ({(a : ZMod q)} : Finset (ZMod q))} =
      #{k ∈ s | f k % q = a % q} := by
  rw [filter_congr fun k _ ↦ by rw [mem_singleton, ZMod.natCast_eq_natCast_iff']]

/-- Membership in the singleton `{a mod q}` is congruence modulo `q`. -/
theorem card_filter_natCast_mem_singleton' (s : Finset ℕ) :
    #{p ∈ s | ((p : ℕ) : ZMod q) ∈ ({(a : ZMod q)} : Finset (ZMod q))} =
      #{p ∈ s | p % q = a % q} :=
  card_filter_natCast_mem_singleton s id

/-- The single-class discrepancy `#{k < n | pₖ ≡ a (mod q)} - n / φ(q)` is the union discrepancy of
`A = {a}`. -/
theorem fun_card_nthPrime_modEq_sub_eq :
    (fun n : ℕ ↦ (#{k ∈ range n | nthPrime k % q = a % q} : ℝ) - n / q.totient) =
      fun n : ℕ ↦ (#{k ∈ range n | (nthPrime k : ZMod q) ∈ ({(a : ZMod q)} : Finset (ZMod q))} :
        ℝ) - #({(a : ZMod q)} : Finset (ZMod q)) * n / q.totient := by
  funext n
  rw [card_filter_natCast_mem_singleton, card_singleton, Nat.cast_one, one_mul]

/-- The single-class discrepancy `π(x; q, a) - π(x) / φ(q)` in the `x` scale is the union
discrepancy of `A = {a}`. -/
theorem fun_card_primesBelow_modEq_sub_eq :
    (fun x : ℕ ↦ (#{p ∈ Nat.primesBelow x | p % q = a % q} : ℝ) -
      Nat.primeCounting' x / q.totient) =
      fun x : ℕ ↦ (#{p ∈ Nat.primesBelow x |
        ((p : ℕ) : ZMod q) ∈ ({(a : ZMod q)} : Finset (ZMod q))} : ℝ) -
          #({(a : ZMod q)} : Finset (ZMod q)) * Nat.primeCounting' x / q.totient := by
  funext x
  rw [card_filter_natCast_mem_singleton', card_singleton, Nat.cast_one, one_mul]

/-- **The single-class rate theorem, index scale.** For `q ≥ 3`, `a` coprime to `q` and
`θ < 1 / 2`, `E(n) = #{k < n | pₖ ≡ a (mod q)} - n / φ(q)` is not `O(n ^ θ)`. Neither the prime
number theorem nor any information on zeros of `L`-functions is used. -/
theorem Nat.not_isBigO_card_nthPrime_modEq_sub_rpow (hq : 3 ≤ q) (ha : a.Coprime q) {θ : ℝ}
    (hθ : θ < 1 / 2) :
    ¬ (fun n : ℕ ↦ (#{k ∈ range n | nthPrime k % q = a % q} : ℝ) - n / q.totient)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ θ := by
  rw [fun_card_nthPrime_modEq_sub_eq]
  exact Nat.not_isBigO_card_nthPrime_mem_sub_rpow hq
    (by simpa using (ZMod.isUnit_iff_coprime a q).2 ha) (by simp) hθ

/-- **The single-class rate theorem, index scale.** For `q ≥ 3`, `a` coprime to `q` and
`θ < 1 / 2`, there is no `C` with `|#{k < n | pₖ ≡ a (mod q)} - n / φ(q)| ≤ C n ^ θ` for all `n`. -/
theorem Nat.not_exists_abs_card_nthPrime_modEq_sub_le_rpow (hq : 3 ≤ q) (ha : a.Coprime q)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      |(#{k ∈ range n | nthPrime k % q = a % q} : ℝ) - n / q.totient| ≤ C * (n : ℝ) ^ θ :=
  fun ⟨C, hC⟩ ↦ not_exists_abs_le_mul_of_not_isBigO (N := 0) (fun n _ ↦ by positivity)
    (Nat.not_isBigO_card_nthPrime_modEq_sub_rpow hq ha hθ) ⟨C, fun n _ ↦ hC n⟩

/-- **The single-class rate theorem, `x` scale.** For `q ≥ 3`, `a` coprime to `q` and `θ < 1 / 2`,
`π(x; q, a) - π(x) / φ(q)` is not `O(x ^ θ)`. -/
theorem Nat.not_isBigO_card_primesBelow_modEq_sub_rpow (hq : 3 ≤ q) (ha : a.Coprime q) {θ : ℝ}
    (hθ : θ < 1 / 2) :
    ¬ (fun x : ℕ ↦ (#{p ∈ Nat.primesBelow x | p % q = a % q} : ℝ) -
      Nat.primeCounting' x / q.totient) =O[atTop] fun x : ℕ ↦ (x : ℝ) ^ θ := by
  rw [fun_card_primesBelow_modEq_sub_eq]
  exact Nat.not_isBigO_card_primesBelow_mem_sub_rpow hq
    (by simpa using (ZMod.isUnit_iff_coprime a q).2 ha) (by simp) hθ

/-- **The single-class rate theorem, log-power form, `x` scale.** For `q ≥ 3`, `a` coprime to `q`
and `β > 1`, `π(x; q, a) - π(x) / φ(q)` is not `O(x ^ (1 / 2) / (log x) ^ β)`: in Landau's notation,
`π(x; q, a) - π(x) / φ(q) = Ω(√x / (log x) ^ (1 + ε))` for every `ε > 0`. -/
theorem Nat.not_isBigO_card_primesBelow_modEq_sub_rpow_div_log_rpow (hq : 3 ≤ q)
    (ha : a.Coprime q) {β : ℝ} (hβ : 1 < β) :
    ¬ (fun x : ℕ ↦ (#{p ∈ Nat.primesBelow x | p % q = a % q} : ℝ) -
      Nat.primeCounting' x / q.totient) =O[atTop]
        fun x : ℕ ↦ (x : ℝ) ^ (1 / 2 : ℝ) / Real.log x ^ β := by
  rw [fun_card_primesBelow_modEq_sub_eq]
  exact Nat.not_isBigO_card_primesBelow_mem_sub_rpow_div_log_rpow hq
    (by simpa using (ZMod.isUnit_iff_coprime a q).2 ha) (by simp) hβ

/-- **The single-class rate theorem, log-power form.** For `q ≥ 3`, `a` coprime to `q` and
`β > 1`, there is no `C` with `|π(x; q, a) - π(x) / φ(q)| ≤ C √x / (log x) ^ β` for all `x ≥ 2`. -/
theorem Nat.not_exists_abs_card_primesBelow_modEq_sub_le_rpow_div_log_rpow (hq : 3 ≤ q)
    (ha : a.Coprime q) {β : ℝ} (hβ : 1 < β) :
    ¬ ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |(#{p ∈ Nat.primesBelow x | p % q = a % q} : ℝ) - Nat.primeCounting' x / q.totient| ≤
        C * (x : ℝ) ^ (1 / 2 : ℝ) / Real.log x ^ β := fun ⟨C, hC⟩ ↦
  not_exists_abs_le_mul_of_not_isBigO
    (fun x hx ↦ (rpow_div_log_rpow_pos (by exact_mod_cast hx) _ _).le)
    (Nat.not_isBigO_card_primesBelow_modEq_sub_rpow_div_log_rpow hq ha hβ)
    ⟨C, fun x hx ↦ (hC x hx).trans_eq (mul_div_assoc _ _ _)⟩

/-- **The single-class rate theorem, log-power form, index scale.** For `q ≥ 3`, `a` coprime to
`q` and `β > 1 / 2`, `#{k < n | pₖ ≡ a (mod q)} - n / φ(q)` is not
`O(n ^ (1 / 2) / (log n) ^ β)`. -/
theorem Nat.not_isBigO_card_nthPrime_modEq_sub_rpow_div_log_rpow (hq : 3 ≤ q)
    (ha : a.Coprime q) {β : ℝ} (hβ : 1 / 2 < β) :
    ¬ (fun n : ℕ ↦ (#{k ∈ range n | nthPrime k % q = a % q} : ℝ) - n / q.totient)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ β := by
  rw [fun_card_nthPrime_modEq_sub_eq]
  exact Nat.not_isBigO_card_nthPrime_mem_sub_rpow_div_log_rpow hq
    (by simpa using (ZMod.isUnit_iff_coprime a q).2 ha) (by simp) hβ

/-- **The single-class rate theorem, log-power form, index scale.** For `q ≥ 3`, `a` coprime to
`q` and `β > 1 / 2`, there is no `C` with
`|#{k < n | pₖ ≡ a (mod q)} - n / φ(q)| ≤ C n ^ (1 / 2) / (log n) ^ β` for all `n ≥ 2`. -/
theorem Nat.not_exists_abs_card_nthPrime_modEq_sub_le_rpow_div_log_rpow (hq : 3 ≤ q)
    (ha : a.Coprime q) {β : ℝ} (hβ : 1 / 2 < β) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |(#{k ∈ range n | nthPrime k % q = a % q} : ℝ) - n / q.totient| ≤
        C * (n : ℝ) ^ (1 / 2 : ℝ) / Real.log n ^ β := fun ⟨C, hC⟩ ↦
  not_exists_abs_le_mul_of_not_isBigO
    (fun n hn ↦ (rpow_div_log_rpow_pos (by exact_mod_cast hn) _ _).le)
    (Nat.not_isBigO_card_nthPrime_modEq_sub_rpow_div_log_rpow hq ha hβ)
    ⟨C, fun n hn ↦ (hC n hn).trans_eq (mul_div_assoc _ _ _)⟩

end SingleClass
