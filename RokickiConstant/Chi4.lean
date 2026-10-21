/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import RokickiConstant.Defs
import RokickiConstant.PartialSums

/-!
# The character `χ₄` at the odd primes

Let `χ₄` be the nontrivial Dirichlet character modulo `4`, and write `3 = p₂ < p₃ < ⋯` for the
odd primes. This file records the values of `χ₄` at the odd primes, which encode the binary
digits of Rokicki's constant, together with the facts about the series `∑ₖ pₖ₊₂ ^ (-s)` needed
for the Euler product of `L(s, χ₄)` in `RokickiConstant.EulerProduct`: a sum over all primes is the
term at `2` plus a sum over the odd primes, `∑ₖ pₖ₊₂ ^ (-σ)` converges for `σ > 1` and tends to
`+∞` as `σ → 1⁺`, and the terms `χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)` of the Euler product have norm
`pₖ₊₂ ^ (-re s)`, at most `3 / 4` for `re s > 1 / 2`.

## Main definitions

* `RokickiConstant.chi4`: the nontrivial Dirichlet character modulo `4` with values in `ℂ`.
* `RokickiConstant.primeTerm k s`: the term `χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)` of the Euler product.

## Main statements

* `RokickiConstant.chi4_oddPrime`: `χ₄ pₖ₊₂ = 1 - 2 · rokickiDigit k`.
* `RokickiConstant.tsum_primes_eq_add_tsum_oddPrime`: a sum over the primes is the term at `2`
  plus a sum over the odd primes.
* `RokickiConstant.tendsto_tsum_oddPrime_rpow_neg`: `∑ₖ pₖ₊₂ ^ (-σ) → +∞` as `σ → 1⁺`.

## Tags

Dirichlet character, primes modulo 4
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

namespace RokickiConstant

open Real

/-- The nontrivial Dirichlet character modulo `4`, with values in `ℂ`: `chi4 n = 1` if
`n ≡ 1 (mod 4)`, `-1` if `n ≡ 3 (mod 4)`, and `0` for even `n`. -/
noncomputable def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- On natural numbers, `chi4` is the cast of `ZMod.χ₄`. -/
theorem chi4_natCast (n : ℕ) : chi4 n = (ZMod.χ₄ n : ℂ) := by
  simp [chi4, MulChar.ringHomComp_apply]

/-- `chi4` is not the trivial character. -/
theorem chi4_ne_one : chi4 ≠ 1 := by
  refine (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr ?_
  exact MulChar.ne_one_iff.mpr ⟨-1, by decide⟩

/-- The digits of Rokicki's constant in terms of `chi4`: `chi4 pₖ₊₂ = 1 - 2 · rokickiDigit k`. -/
theorem chi4_oddPrime (k : ℕ) : chi4 (oddPrime k) = 1 - 2 * (rokickiDigit k : ℂ) := by
  rw [chi4_natCast, χ₄_oddPrime]
  push_cast
  ring

/-- `chi4` squares to `1` at the odd primes. -/
theorem chi4_oddPrime_sq (k : ℕ) : chi4 (oddPrime k) ^ 2 = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (rokickiDigit_le_one k) with h | h <;>
    norm_num [chi4_oddPrime, h]

/-- `chi4` has norm `1` at the odd primes. -/
theorem norm_chi4_oddPrime (k : ℕ) : ‖chi4 (oddPrime k)‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← norm_pow, chi4_oddPrime_sq,
    norm_one])

/-- `chi4` vanishes at `2`. -/
theorem chi4_two : chi4 2 = 0 := by
  simpa using chi4_natCast 2

/-- The enumeration `Nat.nth Nat.Prime` of the primes, as an equivalence `ℕ ≃ Nat.Primes`. -/
private noncomputable def primesEquiv : ℕ ≃ Nat.Primes :=
  Equiv.ofBijective (fun k ↦ ⟨Nat.nth Nat.Prime k, Nat.prime_nth_prime k⟩)
    ⟨fun _ _ h ↦ Nat.nth_injective Nat.infinite_setOfPred_prime (congrArg Subtype.val h),
      fun p ↦ ⟨Nat.count Nat.Prime p, Subtype.ext (Nat.nth_count p.2)⟩⟩

/-- A sum over all primes splits as the term at `2` plus a sum over the odd primes. -/
theorem tsum_primes_eq_add_tsum_oddPrime {F : Nat.Primes → ℂ} (hF : Summable F) :
    ∑' p : Nat.Primes, F p = F ⟨2, Nat.prime_two⟩ + ∑' k : ℕ, F ⟨oddPrime k, prime_oddPrime k⟩ := by
  rw [← primesEquiv.tsum_eq]
  refine ((primesEquiv.summable_iff.mpr hF).tsum_eq_zero_add).trans ?_
  have h0 : primesEquiv 0 = ⟨2, Nat.prime_two⟩ := Subtype.ext Nat.nth_prime_zero_eq_two
  rw [Function.comp_apply, h0]
  rfl

/-- The sum of the reciprocals of the odd primes diverges. -/
theorem not_summable_oddPrime_inv : ¬ Summable fun k : ℕ ↦ ((oddPrime k : ℝ))⁻¹ := by
  intro h
  apply Nat.Primes.not_summable_one_div
  rw [← primesEquiv.summable_iff]
  refine (summable_nat_add_iff 1).mp (h.congr fun k ↦ ?_)
  exact (one_div _).symm

/-- The series `∑ₖ pₖ₊₂ ^ r` converges for `r < -1`. -/
theorem summable_oddPrime_rpow {r : ℝ} (hr : r < -1) :
    Summable fun k : ℕ ↦ (oddPrime k : ℝ) ^ r :=
  summable_natCast_rpow (oddPrime_pos 0) oddPrime_strictMono hr

/-- `∑ₖ pₖ₊₂ ^ (-σ) → ∞` as `σ → 1⁺`, since `∑_p 1 / p` diverges. -/
theorem tendsto_tsum_oddPrime_rpow_neg :
    Tendsto (fun σ : ℝ ↦ ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ)) (𝓝[>] (1 : ℝ)) atTop := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k ↦ by positivity)).mp not_summable_oddPrime_inv
  refine tendsto_atTop.mpr fun M ↦ ?_
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp hdiv (M + 1)).exists
  have hcont : Tendsto (fun σ : ℝ ↦ ∑ k ∈ range N, (oddPrime k : ℝ) ^ (-σ)) (𝓝 1)
      (𝓝 (∑ k ∈ range N, (oddPrime k : ℝ)⁻¹)) := by
    refine tendsto_finsetSum _ fun k _ ↦ ?_
    have := (Real.continuousAt_const_rpow (b := -1)
      (Nat.cast_pos.2 (oddPrime_pos k)).ne').tendsto.comp (tendsto_neg (1 : ℝ))
    simpa [Function.comp_def, Real.rpow_neg_one] using this
  filter_upwards [nhdsWithin_le_nhds (hcont.eventually (lt_mem_nhds (show M < _ by linarith))),
    self_mem_nhdsWithin] with σ hσ (hσ1 : 1 < σ)
  exact hσ.le.trans (Summable.sum_le_tsum _ (fun k _ ↦ by positivity)
    (summable_oddPrime_rpow (by linarith)))

/-- The term `χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)` of the Euler product of `L(s, χ₄)`. -/
noncomputable def primeTerm (k : ℕ) (s : ℂ) : ℂ := chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s)

/-- `‖χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)‖ = pₖ₊₂ ^ (-re s)`. -/
theorem norm_primeTerm (k : ℕ) (s : ℂ) : ‖primeTerm k s‖ = (oddPrime k : ℝ) ^ (-s.re) := by
  rw [primeTerm, norm_mul, norm_chi4_oddPrime, one_mul,
    Complex.norm_natCast_cpow_of_pos (oddPrime_pos k), neg_re]

/-- For `1 / 2 < re s`, `‖χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)‖ ≤ 3 / 4`, because its square is at most
`1 / pₖ₊₂ ≤ 1 / 3`. -/
theorem norm_primeTerm_le (k : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) : ‖primeTerm k s‖ ≤ 3 / 4 := by
  have h3 : (3 : ℝ) ≤ oddPrime k := by
    exact_mod_cast oddPrime_zero ▸ oddPrime_strictMono.monotone k.zero_le
  have h : ‖primeTerm k s‖ ^ 2 ≤ 1 / 3 := by
    rw [norm_primeTerm, ← Real.rpow_mul_natCast (by positivity)]
    calc _ ≤ (oddPrime k : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by push_cast; linarith)
      _ ≤ 1 / 3 := by rw [Real.rpow_neg_one, one_div]; exact inv_anti₀ (by norm_num) h3
  nlinarith [norm_nonneg (primeTerm k s)]

end RokickiConstant
