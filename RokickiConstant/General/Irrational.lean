/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import RokickiConstant.CharacterSums
import RokickiConstant.Defs
import RokickiConstant.General.CharacterSums
import RokickiConstant.General.Expansion

/-!
# Irrational numbers from quadratic characters at the primes

Let `χ` be a nonprincipal quadratic Dirichlet character modulo `q`, let `p₀ = 2 < p₁ < ⋯` be the
primes, let `b ≥ 2` be a base, and let `f` encode the values of `χ` as digits `f z < b` with
`f 1 ≠ f (-1)`. Then
$$`\sum_{k \geq 0} \frac{f(\chi(p_k))}{b^{k+1}}`
is irrational (`DirichletCharacter.IsQuadratic.irrational_tsum`). If the digits were eventually
periodic, so would be `χ(pₖ)` (which is nonzero for all large `k`), hence its partial sums would
be `c · n + O(1)`, contradicting `RokickiConstant.General.CharacterSums`.

Consequences:

* `Real.irrational_rokickiConstantBase`: Rokicki's digit sequence read in any base `b ≥ 2`
  gives an irrational number; `b = 2` is Rokicki's constant. The digits are the invariant, the
  base is only a way of reading them.
* `Real.irrational_legendreConstant`: for an odd prime `ℓ`, the number whose `k`-th digit records
  whether `pₖ` is a quadratic non-residue modulo `ℓ` is irrational.
* `Real.irrational_rokickiConstant'`: a second proof that Rokicki's constant is irrational, as a
  special case of the general theorem.

## Main statements

* `DirichletCharacter.IsQuadratic.irrational_tsum`
* `Real.irrational_rokickiConstantBase`
* `Real.irrational_legendreConstant`

## Tags

Dirichlet character, quadratic character, irrational, Legendre symbol
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Function

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

namespace DirichletCharacter.IsQuadratic

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsQuadratic)
include hχ

/-- If the digits `f (χ pₖ)` are eventually periodic and `f 1 ≠ f (-1)`, then `k ↦ χ(pₖ)` is
eventually periodic with the same period. -/
theorem eventuallyPeriodic_apply_nthPrime {f : ℂ → ℕ} (hf : f 1 ≠ f (-1)) {p : ℕ}
    (h : EventuallyPeriodic (fun k ↦ f (χ (nthPrime k))) p) :
    EventuallyPeriodic (fun k ↦ χ (nthPrime k)) p := by
  have hv : ∀ᶠ k in atTop, χ (nthPrime k) = 1 ∨ χ (nthPrime k) = -1 :=
    χ.eventually_apply_nthPrime_ne_zero.mono fun k hk ↦ (hχ _).resolve_left hk
  filter_upwards [h, hv, (tendsto_add_atTop_nat p).eventually hv] with k hk h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂] at hk ⊢
  exacts [absurd hk.symm hf, absurd hk hf]

/-- The sequence `k ↦ χ(pₖ)` of a nonprincipal quadratic character is not eventually periodic. -/
theorem not_eventuallyPeriodic_apply_nthPrime (hχ₁ : χ ≠ 1) {p : ℕ} (hp : 0 < p) :
    ¬ EventuallyPeriodic (fun k ↦ χ (nthPrime k)) p := by
  intro h
  let a : ℕ → ℤ := fun k ↦
    if χ (nthPrime k) = 1 then 1 else if χ (nthPrime k) = -1 then -1 else 0
  have ha (k : ℕ) : (a k : ℂ) = χ (nthPrime k) := by
    rcases hχ (nthPrime k) with h | h | h <;> norm_num [a, h]
  have hper : EventuallyPeriodic a p :=
    h.mono fun k hk ↦ Int.cast_injective (α := ℂ) (by rw [ha, ha]; exact hk)
  obtain ⟨c, C, hC⟩ := hper.exists_abs_sum_sub_mul_le hp
  have hC' (n : ℕ) : ‖(∑ k ∈ range n, χ (nthPrime k)) - ((c : ℝ) : ℂ) * n‖ ≤ C := by
    have : (∑ k ∈ range n, χ (nthPrime k)) - ((c : ℝ) : ℂ) * n =
        (((∑ k ∈ range n, (a k : ℝ)) - c * n : ℝ) : ℂ) := by
      push_cast [ha]
      rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hC n
  by_cases hc : (c : ℝ) = 0
  · exact not_exists_norm_sum_le hχ hχ₁ ⟨C, fun n ↦ by simpa [hc] using hC' n⟩
  · exact not_exists_norm_sum_sub_mul_le hχ hχ₁ ⟨c, hc, C, hC'⟩

/-- **Irrationality from a quadratic character.** For a nonprincipal quadratic character `χ`, a
base `b ≥ 2` and digits `f (χ pₖ) < b` with `f 1 ≠ f (-1)`, the number `∑ₖ f (χ pₖ) / b ^ (k + 1)`
is irrational. -/
theorem irrational_tsum (hχ₁ : χ ≠ 1) {b : ℕ} (hb : 2 ≤ b) {f : ℂ → ℕ} (hfb : ∀ z, f z < b)
    (hf : f 1 ≠ f (-1)) :
    Irrational (∑' k : ℕ, (f (χ (nthPrime k)) : ℝ) / b ^ (k + 1)) :=
  irrational_tsum_div_pow hb (fun _ ↦ hfb _) fun _ hp hper ↦
    not_eventuallyPeriodic_apply_nthPrime hχ hχ₁ hp (eventuallyPeriodic_apply_nthPrime hχ hf hper)

end DirichletCharacter.IsQuadratic

namespace Real

/-- Rokicki's digit sequence read in base `b`: `∑ₖ rokickiDigit k / b ^ (k + 1)`. For `b = 2` this
is Rokicki's constant. -/
noncomputable def rokickiConstantBase (b : ℕ) : ℝ := ∑' k : ℕ, (rokickiDigit k : ℝ) / b ^ (k + 1)

/-- In base `2`, `rokickiConstantBase 2 = ρ`. -/
theorem rokickiConstantBase_two : rokickiConstantBase 2 = rokickiConstant := by
  simp [rokickiConstantBase, rokickiConstant]

/-- Rokicki's digit sequence is not eventually periodic. -/
theorem not_eventuallyPeriodic_rokickiDigit {p : ℕ} (hp : 0 < p) :
    ¬ EventuallyPeriodic rokickiDigit p := by
  intro hd
  have ha : EventuallyPeriodic (fun k ↦ ZMod.χ₄ (RokickiConstant.oddPrime k)) p :=
    hd.mono fun n hn ↦ by simp only [RokickiConstant.χ₄_oddPrime, hn]
  obtain ⟨c, C, hC⟩ := ha.exists_abs_sum_sub_mul_le hp
  by_cases hc : (c : ℝ) = 0
  · exact RokickiConstant.not_exists_abs_sum_chi4_le ⟨C, fun n ↦ by simpa [hc] using hC n⟩
  · exact RokickiConstant.not_exists_abs_sum_chi4_sub_mul_le ⟨c, hc, C, hC⟩

/-- **Rokicki's digits give an irrational number in every base** `b ≥ 2`. -/
theorem irrational_rokickiConstantBase {b : ℕ} (hb : 2 ≤ b) :
    Irrational (rokickiConstantBase b) :=
  irrational_tsum_div_pow hb (fun k ↦ by have := rokickiDigit_le_one k; omega)
    fun _ hp ↦ not_eventuallyPeriodic_rokickiDigit hp

open RokickiConstant in
/-- A second proof that Rokicki's constant is irrational, as a special case of the general
theorem. -/
theorem irrational_rokickiConstant' : Irrational rokickiConstant := by
  let f : ℂ → ℕ := fun z ↦ if z = -1 then 1 else 0
  have h₀ : f (chi4 (nthPrime 0)) = 0 := by
    simp [f, Nat.nth_prime_zero_eq_two, chi4_two]
  have hd (k : ℕ) : f (chi4 (nthPrime (k + 1))) = rokickiDigit k := by
    have := chi4_oddPrime k
    rw [oddPrime] at this
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (rokickiDigit_le_one k) with h | h <;>
      norm_num [f, this, h]
  have hterm (k : ℕ) : (f (chi4 (nthPrime (k + 1))) : ℝ) / 2 ^ (k + 1 + 1) =
      (rokickiDigit k : ℝ) / 2 ^ (k + 1) / 2 := by
    rw [hd, pow_succ, div_div]
  have hs : Summable fun k ↦ (f (chi4 (nthPrime (k + 1))) : ℝ) / 2 ^ (k + 1 + 1) := by
    simpa only [hterm] using summable_rokickiDigit_div_two_pow.div_const 2
  have hχ : chi4.IsQuadratic := ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)
  have hfb (z : ℂ) : f z < 2 := by
    simp only [f]
    split_ifs <;> omega
  have hf : f 1 ≠ f (-1) := by norm_num [f]
  have h := DirichletCharacter.IsQuadratic.irrational_tsum hχ chi4_ne_one le_rfl hfb hf
  simp only [Nat.cast_ofNat] at h
  rw [tsum_eq_zero_add' (f := fun k ↦ (f (chi4 (nthPrime k)) : ℝ) / 2 ^ (k + 1)) hs] at h
  simp only [h₀, Nat.cast_zero, zero_div, zero_add, hterm, tsum_div_const] at h
  exact h.of_div_natCast 2

/-- The Legendre symbol modulo an odd prime `ℓ`, as a Dirichlet character with values in `ℂ`. -/
noncomputable def legendreChar (ℓ : ℕ) [Fact ℓ.Prime] : DirichletCharacter ℂ ℓ :=
  (quadraticChar (ZMod ℓ)).ringHomComp (Int.castRingHom ℂ)

/-- The Legendre character is quadratic. -/
theorem isQuadratic_legendreChar (ℓ : ℕ) [Fact ℓ.Prime] : (legendreChar ℓ).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod ℓ)).comp _

/-- The Legendre character is nonprincipal for odd `ℓ`. -/
theorem legendreChar_ne_one (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) : legendreChar ℓ ≠ 1 := by
  refine (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one ?_)
  rwa [ZMod.ringChar_zmod_n]

/-- The **Legendre constant** of an odd prime `ℓ` in base `b`: the number whose `k`-th base-`b`
digit is `1` if the `k`-th prime `pₖ` is a quadratic non-residue modulo `ℓ`, and `0` otherwise
(so the digit is `0` for `pₖ = ℓ` and for quadratic residues). For `ℓ = 2` and `b = 2`, compare
Rokicki's constant, which encodes the residue of `pₖ` modulo `4` instead. -/
noncomputable def legendreConstant (ℓ b : ℕ) [Fact ℓ.Prime] : ℝ :=
  ∑' k : ℕ, (if legendreChar ℓ (nthPrime k) = -1 then (1 : ℝ) else 0) / b ^ (k + 1)

/-- **Legendre constants are irrational**: for every odd prime `ℓ` and base `b ≥ 2`. -/
theorem irrational_legendreConstant (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) {b : ℕ} (hb : 2 ≤ b) :
    Irrational (legendreConstant ℓ b) := by
  have := DirichletCharacter.IsQuadratic.irrational_tsum (isQuadratic_legendreChar ℓ)
    (legendreChar_ne_one ℓ hℓ) hb
    (f := fun z ↦ if z = -1 then 1 else 0) (fun z ↦ by split_ifs <;> omega) (by norm_num)
  simpa only [legendreConstant, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using this

end Real
