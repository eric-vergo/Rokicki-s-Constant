/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.SumPrimeReciprocals
import RokickiConstant.Defs
import RokickiConstant.PartialSums

/-!
# The Euler product of `L(s, χ₄)`

Let `χ₄` be the nontrivial Dirichlet character modulo `4`, so that `χ₄ p = 1` for primes
`p ≡ 1 (mod 4)` and `χ₄ p = -1` for primes `p ≡ 3 (mod 4)`. Writing `3 = p₂ < p₃ < ⋯` for the
odd primes, this file sets up the Euler product of `L(s, χ₄)` in the form
$$`L(s, \chi_4) = \exp\Big(\sum_p \chi_4(p) p^{-s}
  + \sum_p \sum_{m \geq 2} \frac{\chi_4(p)^m p^{-ms}}{m}\Big), \qquad \operatorname{re} s > 1,`
which Mathlib provides as `DirichletCharacter.LSeries_eulerProduct_exp_log`. The first sum is
`primePart s`, the second `primePowerPart s`. We prove that `primePowerPart` is holomorphic on
`re s > 1 / 2`, bounded on `re s ≥ 1`, and that its real part tends to `+∞` as `s → 1 / 2⁺`
along the reals: its `m = 2` terms are `∑_p p^{-2s} / 2` and `∑_p 1 / p` diverges.

The consequences for the partial sums of `χ₄` over the primes are drawn in
`RokickiConstant.CharacterSums`.

## Main definitions

* `RokickiConstant.chi4`: the nontrivial Dirichlet character modulo `4` with values in `ℂ`.
* `RokickiConstant.primePart s`: `∑ₖ χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)`.
* `RokickiConstant.primePowerPart s`: `∑ₖ ∑_{m ≥ 2} χ₄ pₖ₊₂ ^ m · pₖ₊₂ ^ (-m s) / m`.

## Main statements

* `RokickiConstant.exp_primePart_add_primePowerPart`: the Euler product in the form above.
* `RokickiConstant.differentiableOn_primePowerPart`: `primePowerPart` is holomorphic on
  `re s > 1 / 2`.
* `RokickiConstant.exists_norm_primePowerPart_le`: `primePowerPart` is bounded on `re s ≥ 1`.
* `RokickiConstant.tendsto_re_primePowerPart`: `re (primePowerPart σ) → +∞` as `σ → 1 / 2⁺`.
* `RokickiConstant.tendsto_tsum_oddPrime_rpow_neg`: `∑ₖ pₖ₊₂ ^ (-σ) → +∞` as `σ → 1⁺`.

## Tags

Dirichlet character, L-function, Euler product
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
theorem norm_chi4_oddPrime (k : ℕ) : ‖chi4 (oddPrime k)‖ = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (rokickiDigit_le_one k) with h | h <;>
    norm_num [chi4_oddPrime, h]

/-- `chi4` vanishes at `2`. -/
theorem chi4_two : chi4 2 = 0 := by
  simp only [chi4, MulChar.ringHomComp_apply]
  rw [show ZMod.χ₄ 2 = 0 by decide]
  simp

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

/-- `oddPrime k` is positive as a real number. -/
private theorem cast_oddPrime_pos (k : ℕ) : (0 : ℝ) < oddPrime k := by
  exact_mod_cast oddPrime_pos k

/-- `oddPrime k` is at least `1` as a real number. -/
private theorem one_le_cast_oddPrime (k : ℕ) : (1 : ℝ) ≤ oddPrime k := by
  exact_mod_cast (prime_oddPrime k).one_lt.le

/-- `oddPrime k` is at least `3` as a real number. -/
private theorem three_le_cast_oddPrime (k : ℕ) : (3 : ℝ) ≤ oddPrime k := by
  exact_mod_cast oddPrime_zero ▸ oddPrime_strictMono.monotone (Nat.zero_le k)

/-- The series `∑ₖ pₖ₊₂ ^ r` converges for `r < -1`. -/
theorem summable_oddPrime_rpow {r : ℝ} (hr : r < -1) :
    Summable fun k : ℕ ↦ (oddPrime k : ℝ) ^ r := by
  have h2 : Summable fun k : ℕ ↦ ((k + 2 : ℕ) : ℝ) ^ r :=
    (summable_nat_add_iff 2 (f := fun n : ℕ ↦ (n : ℝ) ^ r)).mpr (Real.summable_nat_rpow.mpr hr)
  refine Summable.of_nonneg_of_le (fun k ↦ (Real.rpow_pos_of_pos (cast_oddPrime_pos k) _).le)
    (fun k ↦ ?_) h2
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast add_two_le_oddPrime k)
    (by linarith)

/-- `∑ₖ pₖ₊₂ ^ (-σ) → ∞` as `σ → 1⁺`, since `∑_p 1 / p` diverges. -/
theorem tendsto_tsum_oddPrime_rpow_neg :
    Tendsto (fun σ : ℝ ↦ ∑' k : ℕ, (oddPrime k : ℝ) ^ (-σ)) (𝓝[>] (1 : ℝ)) atTop := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k ↦ inv_nonneg.mpr (cast_oddPrime_pos k).le)).mp not_summable_oddPrime_inv
  refine tendsto_atTop.mpr fun M ↦ ?_
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp hdiv (M + 1)).exists
  have hcont : Tendsto (fun σ : ℝ ↦ ∑ k ∈ range N, (oddPrime k : ℝ) ^ (-σ)) (𝓝 1)
      (𝓝 (∑ k ∈ range N, (oddPrime k : ℝ)⁻¹)) := by
    refine tendsto_finsetSum _ fun k _ ↦ ?_
    have := (Real.continuousAt_const_rpow (b := -1) (cast_oddPrime_pos k).ne').tendsto.comp
      (tendsto_neg (1 : ℝ))
    simpa [Function.comp_def, Real.rpow_neg_one] using this
  have hev : ∀ᶠ σ in 𝓝 (1 : ℝ), M < ∑ k ∈ range N, (oddPrime k : ℝ) ^ (-σ) :=
    hcont.eventually (lt_mem_nhds (by linarith))
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with σ hσ hσ1
  refine hσ.le.trans (Summable.sum_le_tsum _
    (fun k _ ↦ (Real.rpow_pos_of_pos (cast_oddPrime_pos k) _).le) ?_)
  exact summable_oddPrime_rpow (by rw [Set.mem_Ioi] at hσ1; linarith)

section EulerProduct

/-- The prime part `∑ₖ χ₄ pₖ₊₂ · pₖ₊₂ ^ (-s)` of the logarithm of the Euler product of
`L(s, χ₄)`; absolutely convergent for `1 < re s`. -/
noncomputable def primePart (s : ℂ) : ℂ := ∑' k : ℕ, chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s)

/-- The prime power part `∑ₖ ∑_{m ≥ 2} χ₄ pₖ₊₂ ^ m · pₖ₊₂ ^ (-m s) / m` of the logarithm of the
Euler product of `L(s, χ₄)`; absolutely convergent for `1 / 2 < re s`. -/
noncomputable def primePowerPart (s : ℂ) : ℂ :=
  ∑' k : ℕ, ∑' m : ℕ,
    chi4 (oddPrime k) ^ (m + 2) * ((oddPrime k : ℂ) ^ (-s)) ^ (m + 2) / (m + 2)

/-- For `0 < re s`, every odd prime `p` satisfies `‖p ^ (-s)‖ < 1`. -/
theorem norm_oddPrime_cpow_neg_lt_one {k : ℕ} {s : ℂ} (hs : 0 < s.re) :
    ‖(oddPrime k : ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (oddPrime_pos k)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (prime_oddPrime k).one_lt)
    (by simpa using hs)

/-- The tail `∑' m : ℕ, z ^ (m + 2) / (m + 2)` of the Taylor series of `-log (1 - z)` equals
`-log (1 - z) - z`. -/
theorem hasSum_pow_add_two_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun m : ℕ ↦ z ^ (m + 2) / (m + 2)) (-log (1 - z) - z) := by
  have h := (hasSum_nat_add_iff' 2).mpr (hasSum_taylorSeries_neg_log hz)
  simp only [sum_range_succ, sum_range_zero, pow_zero, Nat.cast_zero, div_zero, pow_one,
    Nat.cast_one, div_one, zero_add] at h
  convert h using 2 with m
  push_cast
  ring

/-- The Taylor expansion `-log (1 - z) = z + ∑_{m ≥ 2} z ^ m / m` at `z = χ₄ p · p ^ (-s)`. -/
theorem neg_log_one_sub_chi4_mul_cpow_neg (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    -log (1 - chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s)) =
      chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s) +
        ∑' m : ℕ, chi4 (oddPrime k) ^ (m + 2) * ((oddPrime k : ℂ) ^ (-s)) ^ (m + 2) / (m + 2) := by
  have hz : ‖chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, norm_chi4_oddPrime, one_mul]
    exact norm_oddPrime_cpow_neg_lt_one hs
  have h := hasSum_pow_add_two_div hz
  simp_rw [mul_pow] at h
  rw [h.tsum_eq]
  ring

/-- The series defining `primePart s` converges for `1 < re s`. -/
theorem summable_primePart {s : ℂ} (hs : 1 < s.re) :
    Summable fun k : ℕ ↦ chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s) :=
  summable_mul_cpow_neg (C := 1) (fun k ↦ (norm_chi4_oddPrime k).le)
    (oddPrime_pos 0) oddPrime_strictMono hs

/-- Termwise bound for the series `∑' m : ℕ, w ^ (m + n) / (m + n)` when `2 ≤ n`. -/
private theorem norm_pow_add_div_le (w : ℂ) {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    ‖w ^ (m + n) / ((m : ℂ) + n)‖ ≤ ‖w‖ ^ (m + n) / 2 := by
  rw [norm_div, norm_pow]
  have h : ‖(m : ℂ) + n‖ = m + n := by
    rw [show (m : ℂ) + n = ((m + n : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast
    ring
  rw [h]
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  gcongr
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- For `‖w‖ ≤ 3 / 4` and `2 ≤ n`, the norm of `∑' m : ℕ, w ^ (m + n) / (m + n)` is at most
`2 * ‖w‖ ^ n`. -/
private theorem norm_tsum_pow_add_div_le {w : ℂ} (hw : ‖w‖ ≤ 3 / 4) {n : ℕ} (hn : 2 ≤ n) :
    ‖∑' m : ℕ, w ^ (m + n) / ((m : ℂ) + n)‖ ≤ 2 * ‖w‖ ^ n := by
  have hr0 := norm_nonneg w
  have hgeo : HasSum (fun m : ℕ ↦ ‖w‖ ^ (m + n) / 2) (‖w‖ ^ n / (2 * (1 - ‖w‖))) := by
    have := (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left (‖w‖ ^ n / 2)
    convert this using 1
    · ext m
      ring
    · field_simp
  have hs : Summable fun m : ℕ ↦ ‖w ^ (m + n) / ((m : ℂ) + n)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_pow_add_div_le w hn) hgeo.summable
  calc ‖∑' m : ℕ, w ^ (m + n) / ((m : ℂ) + n)‖
      ≤ ∑' m : ℕ, ‖w ^ (m + n) / ((m : ℂ) + n)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ‖w‖ ^ n / (2 * (1 - ‖w‖)) :=
      (hs.tsum_le_tsum (norm_pow_add_div_le w hn) hgeo.summable).trans_eq hgeo.tsum_eq
    _ ≤ 2 * ‖w‖ ^ n := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [pow_nonneg hr0 n]

/-- `‖pₖ₊₂ ^ (-s)‖ ^ a = pₖ₊₂ ^ (-(a · re s))` for real `a`. -/
private theorem norm_oddPrime_cpow_rpow (k : ℕ) (s : ℂ) (a : ℝ) :
    ‖(oddPrime k : ℂ) ^ (-s)‖ ^ a = (oddPrime k : ℝ) ^ (-(a * s.re)) := by
  rw [Complex.norm_natCast_cpow_of_pos (oddPrime_pos k), ← Real.rpow_mul
    (cast_oddPrime_pos k).le]
  congr 1
  rw [Complex.neg_re]
  ring

/-- `‖pₖ₊₂ ^ (-s)‖ ^ 2 = pₖ₊₂ ^ (-2 · re s)`. -/
private theorem norm_oddPrime_cpow_sq (k : ℕ) (s : ℂ) :
    ‖(oddPrime k : ℂ) ^ (-s)‖ ^ 2 = (oddPrime k : ℝ) ^ (-2 * s.re) := by
  rw [← Real.rpow_natCast, norm_oddPrime_cpow_rpow]
  push_cast
  ring_nf

/-- For `1 / 2 < re s`, `‖pₖ₊₂ ^ (-s)‖ ≤ 3 / 4`. -/
private theorem norm_oddPrime_cpow_le {k : ℕ} {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖(oddPrime k : ℂ) ^ (-s)‖ ≤ 3 / 4 := by
  have h1 : (oddPrime k : ℝ) ^ (-2 * s.re) ≤ (oddPrime k : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_cast_oddPrime k) (by linarith)
  rw [Real.rpow_neg_one] at h1
  have h2 : (oddPrime k : ℝ)⁻¹ ≤ 1 / 3 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (three_le_cast_oddPrime k)
  have h3 := norm_oddPrime_cpow_sq k s
  nlinarith [norm_nonneg ((oddPrime k : ℂ) ^ (-s))]

/-- For `1 / 2 < re s`, the inner sums of `primePowerPart` are dominated by `2 · p ^ (-2 re s)`. -/
theorem norm_tsum_primePowerPart_le (k : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖∑' m : ℕ, chi4 (oddPrime k) ^ (m + 2) * ((oddPrime k : ℂ) ^ (-s)) ^ (m + 2) / (m + 2)‖ ≤
      2 * (oddPrime k : ℝ) ^ (-2 * s.re) := by
  have hw : ‖chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s)‖ = ‖(oddPrime k : ℂ) ^ (-s)‖ := by
    rw [norm_mul, norm_chi4_oddPrime, one_mul]
  have h := norm_tsum_pow_add_div_le (w := chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s))
    (hw ▸ norm_oddPrime_cpow_le hs) le_rfl
  simp_rw [mul_pow, hw, norm_oddPrime_cpow_sq] at h
  simpa using h

/-- The series defining `primePowerPart s` converges absolutely for `1 / 2 < re s`. -/
private theorem summable_norm_primePowerPart {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun k : ℕ ↦
      ‖∑' m : ℕ, chi4 (oddPrime k) ^ (m + 2) * ((oddPrime k : ℂ) ^ (-s)) ^ (m + 2) / (m + 2)‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ norm_tsum_primePowerPart_le k hs)
    ((summable_oddPrime_rpow (by linarith)).mul_left 2)

/-- The series defining `primePowerPart s` converges for `1 / 2 < re s`. -/
theorem summable_primePowerPart {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun k : ℕ ↦
      ∑' m : ℕ, chi4 (oddPrime k) ^ (m + 2) * ((oddPrime k : ℂ) ^ (-s)) ^ (m + 2) / (m + 2) :=
  (summable_norm_primePowerPart hs).of_norm

/-- **Euler product** for `L(s, χ₄)` in exponential form, `1 < re s`. -/
theorem exp_primePart_add_primePowerPart {s : ℂ} (hs : 1 < s.re) :
    exp (primePart s + primePowerPart s) = DirichletCharacter.LFunction chi4 s := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi4 hs,
    ← DirichletCharacter.LSeries_eulerProduct_exp_log chi4 hs]
  congr 1
  have hsum : Summable fun p : Nat.Primes ↦ -log (1 - chi4 p * (p : ℂ) ^ (-s)) := by
    have h : Summable fun p : Nat.Primes ↦ chi4 p * (p : ℂ) ^ (-s) :=
      (summable_dirichletSummand chi4 hs).of_norm.comp_injective Subtype.val_injective
    exact h.clog_one_sub.neg
  rw [tsum_primes_eq_add_tsum_oddPrime hsum]
  have h0 : 0 < s.re := by linarith
  simp only [Nat.cast_ofNat, chi4_two, zero_mul, sub_zero, Complex.log_one, neg_zero, zero_add,
    neg_log_one_sub_chi4_mul_cpow_neg _ h0]
  rw [(summable_primePart hs).tsum_add (summable_primePowerPart (by linarith))]
  rfl

/-- `primePowerPart` is holomorphic on each half-plane `σ₀ < s.re` with `1 / 2 < σ₀`. -/
private theorem differentiableOn_primePowerPart_of_lt {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) :
    DifferentiableOn ℂ primePowerPart {s : ℂ | σ₀ < s.re} := by
  have hU : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  set z : ℕ → ℂ → ℂ := fun k s ↦ chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-s)
  have hz : ∀ k, ∀ s ∈ {s : ℂ | σ₀ < s.re}, ‖z k s‖ < 1 := fun k s hs ↦ by
    simp only [Set.mem_ofPred_eq] at hs
    simp only [z, norm_mul, norm_chi4_oddPrime, one_mul]
    exact norm_oddPrime_cpow_neg_lt_one (by linarith)
  have hzd : ∀ k s, DifferentiableAt ℂ (z k) s := fun k s ↦
    ((differentiableAt_id.neg).const_cpow
      (Or.inl (by exact_mod_cast (prime_oddPrime k).ne_zero))).const_mul _
  have heq : Set.EqOn primePowerPart (fun s ↦ ∑' k, (-log (1 - z k s) - z k s))
      {s : ℂ | σ₀ < s.re} := fun s hs ↦ by
    simp only [Set.mem_ofPred_eq] at hs
    refine tsum_congr fun k ↦ ?_
    simp only [z, neg_log_one_sub_chi4_mul_cpow_neg k (by linarith : 0 < s.re)]
    ring
  refine DifferentiableOn.congr ?_ heq
  refine differentiableOn_tsum_of_summable_norm
    (u := fun k ↦ 2 * (oddPrime k : ℝ) ^ (-2 * σ₀))
    ((summable_oddPrime_rpow (by linarith)).mul_left 2) (fun k s hs ↦ ?_) hU (fun k s hs ↦ ?_)
  · have hmem : 1 - z k s ∈ slitPlane := by
      simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one (z := -z k s)
        (by rw [norm_neg]; exact hz k s hs)
    exact ((((hzd k s).const_sub 1).clog hmem).neg.sub (hzd k s)).differentiableWithinAt
  · simp only [Set.mem_ofPred_eq] at hs
    simp only [z, neg_log_one_sub_chi4_mul_cpow_neg k (by linarith : 0 < s.re), add_sub_cancel_left]
    refine (norm_tsum_primePowerPart_le k (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_cast_oddPrime k) (by linarith)) zero_le_two

/-- `primePowerPart` is holomorphic on the half-plane `1 / 2 < re s`. -/
theorem differentiableOn_primePowerPart :
    DifferentiableOn ℂ primePowerPart {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs
  have hσ : 1 / 2 < (1 / 2 + s.re) / 2 := by linarith
  have hU : IsOpen {w : ℂ | (1 / 2 + s.re) / 2 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : s ∈ {w : ℂ | (1 / 2 + s.re) / 2 < w.re} := by
    simp only [Set.mem_ofPred_eq]
    linarith
  exact ((differentiableOn_primePowerPart_of_lt hσ).differentiableAt
    (hU.mem_nhds hmem)).differentiableWithinAt

/-- `primePowerPart` is bounded on the closed half-plane `1 ≤ re s`. -/
theorem exists_norm_primePowerPart_le : ∃ M : ℝ, ∀ s : ℂ, 1 ≤ s.re → ‖primePowerPart s‖ ≤ M := by
  refine ⟨∑' k : ℕ, 2 * (oddPrime k : ℝ) ^ (-2 : ℝ), fun s hs ↦ ?_⟩
  have hs' : 1 / 2 < s.re := by linarith
  have hsum := (summable_oddPrime_rpow (r := -2) (by norm_num)).mul_left 2
  refine (norm_tsum_le_tsum_norm (summable_norm_primePowerPart hs')).trans ?_
  refine (summable_norm_primePowerPart hs').tsum_le_tsum (fun k ↦ ?_) hsum
  refine (norm_tsum_primePowerPart_le k hs').trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (one_le_cast_oddPrime k) (by linarith)) zero_le_two

/-- For `‖w‖ ≤ 3 / 4`, the real part of `∑' m : ℕ, w ^ (m + 2) / (m + 2)` is at least
`(w ^ 2 / 2).re - 2 * ‖w‖ ^ 3`. -/
private theorem le_re_tsum_pow_add_two_div {w : ℂ} (hw : ‖w‖ ≤ 3 / 4) :
    (w ^ 2 / 2).re - 2 * ‖w‖ ^ 3 ≤ (∑' m : ℕ, w ^ (m + 2) / (m + 2)).re := by
  have hsum := (hasSum_pow_add_two_div (by linarith : ‖w‖ < 1)).summable
  rw [hsum.tsum_eq_zero_add]
  have hR : ∑' m : ℕ, w ^ (m + 1 + 2) / (((m + 1 : ℕ) : ℂ) + 2) =
      ∑' m : ℕ, w ^ (m + 3) / ((m : ℂ) + (3 : ℕ)) :=
    tsum_congr fun m ↦ by push_cast; ring
  have hle := norm_tsum_pow_add_div_le hw (n := 3) (by norm_num)
  rw [← hR] at hle
  have := (abs_le.mp (abs_re_le_norm (∑' m : ℕ, w ^ (m + 1 + 2) / (((m + 1 : ℕ) : ℂ) + 2)))).1
  rw [add_re]
  simp only [zero_add, Nat.cast_zero]
  linarith

/-- For real `σ > 1 / 2`, the real part of `primePowerPart σ` is at least
`∑ₖ pₖ₊₂ ^ (-2σ) / 2` minus a constant, because `χ₄ p ^ 2 = 1`. -/
theorem le_re_primePowerPart {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' k : ℕ, (oddPrime k : ℝ) ^ (-2 * σ)) / 2 - 2 * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-3 / 2 : ℝ) ≤
      (primePowerPart σ).re := by
  have hs : 1 / 2 < (σ : ℂ).re := by simpa using hσ
  have h1 := summable_oddPrime_rpow (r := -2 * σ) (by linarith)
  have h2 := summable_oddPrime_rpow (r := -3 / 2) (by norm_num)
  have hterm : ∀ k : ℕ, (oddPrime k : ℝ) ^ (-2 * σ) / 2 - 2 * (oddPrime k : ℝ) ^ (-3 / 2 : ℝ) ≤
      (∑' m : ℕ, chi4 (oddPrime k) ^ (m + 2) *
        ((oddPrime k : ℂ) ^ (-(σ : ℂ))) ^ (m + 2) / (m + 2)).re := fun k ↦ by
    set w := chi4 (oddPrime k) * (oddPrime k : ℂ) ^ (-(σ : ℂ)) with hw_def
    have hnw : ‖w‖ = ‖(oddPrime k : ℂ) ^ (-(σ : ℂ))‖ := by
      rw [hw_def, norm_mul, norm_chi4_oddPrime, one_mul]
    have h := le_re_tsum_pow_add_two_div (w := w) (hnw ▸ norm_oddPrime_cpow_le hs)
    simp_rw [hw_def, mul_pow] at h
    rw [← hw_def] at h
    have hz : (oddPrime k : ℂ) ^ (-(σ : ℂ)) = (((oddPrime k : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (cast_oddPrime_pos k).le]
      push_cast
      rfl
    have hre : (chi4 (oddPrime k) ^ 2 * ((oddPrime k : ℂ) ^ (-(σ : ℂ))) ^ 2 / 2).re =
        (oddPrime k : ℝ) ^ (-2 * σ) / 2 := by
      have h4 : ((((oddPrime k : ℝ) ^ (-σ) : ℝ) : ℂ)) ^ 2 / 2 =
          ((((oddPrime k : ℝ) ^ (-σ)) ^ 2 / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [chi4_oddPrime_sq, one_mul, hz, h4, Complex.ofReal_re, ← Real.rpow_natCast,
        ← Real.rpow_mul (cast_oddPrime_pos k).le]
      congr 2
      push_cast
      ring
    have h3 : ‖w‖ ^ 3 ≤ (oddPrime k : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [hnw, ← Real.rpow_natCast, norm_oddPrime_cpow_rpow]
      refine Real.rpow_le_rpow_of_exponent_le (one_le_cast_oddPrime k) ?_
      simp only [Complex.ofReal_re]
      push_cast
      linarith
    linarith
  calc _ = ∑' k : ℕ, ((oddPrime k : ℝ) ^ (-2 * σ) / 2 - 2 * (oddPrime k : ℝ) ^ (-3 / 2 : ℝ)) := by
        rw [(h1.div_const 2).tsum_sub (h2.mul_left 2), tsum_div_const, tsum_mul_left]
    _ ≤ ∑' k : ℕ, (∑' m : ℕ, chi4 (oddPrime k) ^ (m + 2) *
          ((oddPrime k : ℂ) ^ (-(σ : ℂ))) ^ (m + 2) / (m + 2)).re :=
        Summable.tsum_le_tsum hterm ((h1.div_const 2).sub (h2.mul_left 2))
          (Complex.reCLM.summable (summable_primePowerPart hs))
    _ = _ := (Complex.re_tsum (summable_primePowerPart hs)).symm

/-- The real part of `primePowerPart σ` tends to `+∞` as `σ → 1 / 2⁺`. -/
theorem tendsto_re_primePowerPart :
    Tendsto (fun σ : ℝ ↦ (primePowerPart σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop := by
  have h2 : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝[>] (1 / 2)) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝 (1 / 2)) (𝓝 (2 * (1 / 2))) :=
        (continuous_const.mul continuous_id).tendsto _
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      rw [Set.mem_Ioi] at hσ ⊢
      linarith
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _
    (-(2 * ∑' k : ℕ, (oddPrime k : ℝ) ^ (-3 / 2 : ℝ)))
    ((tendsto_tsum_oddPrime_rpow_neg.comp h2).atTop_div_const two_pos))
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have := le_re_primePowerPart (Set.mem_Ioi.mp hσ)
  simp only [Function.comp_apply, neg_mul] at this ⊢
  linarith

end EulerProduct

end RokickiConstant
