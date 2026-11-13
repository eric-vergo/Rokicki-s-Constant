/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import PrimeNumberTheoremAnd.Wiener
import RokickiConstant.Chi4

/-!
# The character sums `∑ χ₄ p` over primes are not linear, by the prime number theorem

Writing `3 = p₂ < p₃ < ⋯` for the odd primes and `χ₄` for the nontrivial Dirichlet character
modulo `4`, this file gives a second proof that the partial sums `S n = ∑_{k < n} χ₄ pₖ₊₂` are not
of the form `c · n + O(1)` with `c ≠ 0`. The first proof, `RokickiConstant.CharacterSums`, lets
`s → 1⁺` in the Euler product of `L(s, χ₄)`. The proof here uses instead the prime number theorem
in arithmetic progressions, in the form `WeakPNT_AP` of the PrimeNumberTheoremAnd project:
`∑_{n < N, n ≡ a (mod q)} Λ n = N / φ(q) + o(N)` for `a` coprime to `q`.

* Removing the proper prime powers, which contribute at most `ψ N - θ N = O(√N)`, gives
  `ϑ(N; q, a) = ∑_{p < N, p ≡ a (mod q)} log p = N / φ(q) + o(N)`
  (`RokickiConstant.PNT.tendsto_thetaAP_div`).
* If `S n = c · n + O(1)`, summation by parts against the increasing weights `log pₖ₊₂` gives
  `∑_{k < m} (χ₄ pₖ₊₂ - c) log pₖ₊₂ = O(log pₘ₊₂)`. The left side is
  `(1 - c) ϑ(pₘ₊₂; 4, 1) - (1 + c) ϑ(pₘ₊₂; 4, 3) = -c · pₘ₊₂ + o(pₘ₊₂)`, so `c = 0`.

The prime number theorem says nothing about the case `c = 0` of bounded partial sums, which is
still handled by `RokickiConstant.not_exists_abs_sum_chi4_le`.

## Main definitions

* `RokickiConstant.PNT.thetaAP q a N`: the Chebyshev function
  `ϑ(N; q, a) = ∑_{p < N, p ≡ a (mod q)} log p`.

## Main statements

* `RokickiConstant.PNT.tendsto_thetaAP_div`: `ϑ(N; q, a) / N → 1 / φ(q)` for `a` coprime to `q`.
* `RokickiConstant.PNT.not_exists_abs_sum_chi4_sub_mul_le`: the partial sums of `χ₄` over the odd
  primes are not `c · n + O(1)` with `c ≠ 0`.

## Tags

Dirichlet character, prime number theorem, arithmetic progression, Chebyshev function
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset
open ArithmeticFunction (vonMangoldt vonMangoldt_nonneg vonMangoldt_apply_prime)

namespace RokickiConstant.PNT

section SummationByParts

/-- **Summation by parts against increasing weights.** If the partial sums of `e` are bounded by
`C` and `w` is nonnegative and monotone, then `|∑ k ∈ range n, e k * w k| ≤ 2 * C * w n`. -/
theorem abs_sum_range_mul_le_of_abs_sum_le_of_monotone {e w : ℕ → ℝ} {C : ℝ}
    (he : ∀ n, |∑ k ∈ range n, e k| ≤ C) (hw₀ : 0 ≤ w 0) (hw : Monotone w) (n : ℕ) :
    |∑ k ∈ range n, e k * w k| ≤ 2 * C * w n := by
  have hC : 0 ≤ C := by simpa using he 0
  rcases n with _ | n
  · simpa using mul_nonneg (mul_nonneg zero_le_two hC) hw₀
  have hwn : 0 ≤ w n := hw₀.trans (hw n.zero_le)
  rw [sum_range_succ_mul_eq_sum_mul_sub]
  have h1 : |(∑ j ∈ range (n + 1), e j) * w n| ≤ C * w n := by
    rw [abs_mul, abs_of_nonneg hwn]
    exact mul_le_mul_of_nonneg_right (he _) hwn
  have h2 : |∑ k ∈ range n, (∑ j ∈ range (k + 1), e j) * (w k - w (k + 1))| ≤
      C * (w n - w 0) :=
    calc _ ≤ ∑ k ∈ range n, |(∑ j ∈ range (k + 1), e j) * (w k - w (k + 1))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range n, C * (w (k + 1) - w k) := sum_le_sum fun k _ ↦ by
          rw [abs_mul, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hw k.le_succ))]
          exact mul_le_mul_of_nonneg_right (he _) (sub_nonneg.2 (hw k.le_succ))
      _ = C * (w n - w 0) := by rw [← mul_sum, sum_range_sub]
  have hmono := hw n.le_succ
  calc _ ≤ C * w n + C * (w n - w 0) := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ ≤ 2 * C * w (n + 1) := by nlinarith

end SummationByParts

section Enumeration

/-- A sum over the primes below the `m`-th prime is a sum over the first `m` primes. -/
theorem sum_range_nth_prime (f : ℕ → ℝ) (m : ℕ) :
    ∑ n ∈ range (Nat.nth Nat.Prime m) with n.Prime, f n =
      ∑ k ∈ range m, f (Nat.nth Nat.Prime k) := by
  induction m with
  | zero => simp [Nat.nth_prime_zero_eq_two, sum_filter, Finset.sum_range_succ,
      Nat.not_prime_zero, Nat.not_prime_one]
  | succ m ih =>
    rw [Nat.filter_range_nth_eq_insert fun hf ↦ (Nat.infinite_setOfPred_prime hf).elim,
      sum_insert (by simp), ih, Finset.sum_range_succ, add_comm]

/-- A sum over the primes below the odd prime `pₘ₊₂` is the term at `2` plus a sum over the
first `m` odd primes. -/
theorem sum_range_oddPrime (f : ℕ → ℝ) (m : ℕ) :
    ∑ n ∈ range (oddPrime m) with n.Prime, f n = f 2 + ∑ k ∈ range m, f (oddPrime k) := by
  rw [oddPrime, sum_range_nth_prime, sum_range_succ', Nat.nth_prime_zero_eq_two, add_comm]
  rfl

end Enumeration

section ThetaAP

/-- The Chebyshev function of an arithmetic progression,
`ϑ(N; q, a) = ∑_{p < N, p ≡ a (mod q)} log p`, the sum running over primes `p`. -/
noncomputable def thetaAP (q a N : ℕ) : ℝ := ∑ n ∈ range N with n.Prime ∧ n % q = a, Real.log n

/-- The proper prime powers below `N` in a residue class contribute at most `ψ N - θ N` to the
sum of the von Mangoldt function: `0 ≤ ∑_{n < N, n ≡ a (mod q)} Λ n - ϑ(N; q, a) ≤ ψ N - θ N`. -/
theorem sum_vonMangoldt_sub_thetaAP_mem_Icc (q a N : ℕ) :
    (∑ n ∈ range N, if n % q = a then vonMangoldt n else 0) - thetaAP q a N ∈
      Set.Icc 0 (Chebyshev.psi N - Chebyshev.theta N) := by
  have hterm : ∀ n : ℕ, (if n % q = a then vonMangoldt n else 0) -
      (if n.Prime ∧ n % q = a then Real.log n else 0) ∈
        Set.Icc 0 (if ¬ n.Prime then vonMangoldt n else 0) := fun n ↦ by
    by_cases hp : n.Prime <;> by_cases ha : n % q = a <;>
      simp [hp, ha, vonMangoldt_apply_prime, vonMangoldt_nonneg]
  rw [thetaAP, sum_filter, ← sum_sub_distrib]
  refine ⟨sum_nonneg fun n _ ↦ (hterm n).1, (sum_le_sum fun n _ ↦ (hterm n).2).trans ?_⟩
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter,
    ← sum_erase (range N) (a := 0) (by simp)]
  refine sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_) fun n _ _ ↦ ?_
  · simp only [mem_erase, mem_range, mem_Ioc] at hn ⊢
    omega
  · split_ifs
    exacts [le_rfl, vonMangoldt_nonneg]

/-- `(ψ N - θ N) / N → 0`: the proper prime powers are negligible. -/
theorem tendsto_psi_sub_theta_div :
    Tendsto (fun N : ℕ ↦ (Chebyshev.psi N - Chebyshev.theta N) / N) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hlim : Tendsto (fun N : ℕ ↦ C * (√(N : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun N ↦ div_nonneg
    (sub_nonneg.2 (Chebyshev.theta_le_psi _)) N.cast_nonneg) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hN', mul_assoc]
  refine (hC N).trans_eq ?_
  rw [inv_mul_eq_div, Real.div_sqrt]

/-- **The prime number theorem in arithmetic progressions**, for the Chebyshev function `ϑ`:
`ϑ(N; q, a) / N → 1 / φ(q)` when `a < q` is coprime to `q`. -/
theorem tendsto_thetaAP_div {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun N : ℕ ↦ thetaAP q a N / N) atTop (𝓝 (1 / q.totient)) := by
  have hrem : Tendsto (fun N : ℕ ↦ ((∑ n ∈ range N, if n % q = a then vonMangoldt n else 0) -
      thetaAP q a N) / N) atTop (𝓝 0) :=
    squeeze_zero (fun N ↦ div_nonneg (sum_vonMangoldt_sub_thetaAP_mem_Icc q a N).1 N.cast_nonneg)
      (fun N ↦ div_le_div_of_nonneg_right (sum_vonMangoldt_sub_thetaAP_mem_Icc q a N).2
        N.cast_nonneg) tendsto_psi_sub_theta_div
  have h := (WeakPNT_AP hq ha ha').sub hrem
  rw [sub_zero] at h
  refine h.congr fun N ↦ ?_
  rw [cumsum, ← sub_div, sub_sub_cancel]

/-- The primes congruent to `a` modulo `4` below the odd prime `pₘ₊₂`, for `a = 1` or `a = 3`,
are the odd primes `pₖ₊₂ ≡ a (mod 4)` with `k < m`. -/
theorem thetaAP_four_oddPrime {a : ℕ} (ha : a = 1 ∨ a = 3) (m : ℕ) :
    thetaAP 4 a (oddPrime m) =
      ∑ k ∈ range m, if oddPrime k % 4 = a then Real.log (oddPrime k) else 0 := by
  rw [thetaAP, ← filter_filter, sum_filter, sum_range_oddPrime]
  rcases ha with rfl | rfl <;> simp

end ThetaAP

/-- The partial sums `∑_{k < n} χ₄ pₖ₊₂` are not of the form `c · n + O(1)` with `c ≠ 0`, by the
prime number theorem in arithmetic progressions. -/
theorem not_exists_abs_sum_chi4_sub_mul_le :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n,
      |(∑ k ∈ range n, (ZMod.χ₄ (oddPrime k) : ℝ)) - c * n| ≤ C := by
  rintro ⟨c, hc, C, h⟩
  have hq : Tendsto oddPrime atTop atTop := oddPrime_strictMono.tendsto_atTop
  have hq' : Tendsto (fun m ↦ (oddPrime m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have h4 : ((4 : ℕ).totient : ℝ) = 2 := by
    rw [show (4 : ℕ).totient = 2 by decide]
    norm_num
  -- `B m = ∑_{k < m} (χ₄ pₖ₊₂ - c) log pₖ₊₂` is `O(log pₘ₊₂)` by summation by parts ...
  set B : ℕ → ℝ := fun m ↦
    ∑ k ∈ range m, ((ZMod.χ₄ (oddPrime k) : ℝ) - c) * Real.log (oddPrime k) with hB
  have hbound : ∀ m, |B m| ≤ 2 * C * Real.log (oddPrime m) := fun m ↦
    abs_sum_range_mul_le_of_abs_sum_le_of_monotone
      (fun n ↦ by simpa [Finset.sum_sub_distrib, mul_comm] using h n)
      (Real.log_nonneg (by exact_mod_cast oddPrime_pos 0))
      (fun i j hij ↦ Real.log_le_log (by exact_mod_cast oddPrime_pos i)
        (by exact_mod_cast oddPrime_strictMono.monotone hij)) m
  have hzero : Tendsto (fun m ↦ B m / oddPrime m) atTop (𝓝 0) := by
    have hlog : Tendsto (fun m ↦ 2 * C * (Real.log (oddPrime m) / oddPrime m)) atTop (𝓝 0) := by
      simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hq').const_mul (2 * C)
    refine squeeze_zero_norm (fun m ↦ ?_) hlog
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hbound m) (Nat.cast_nonneg _)
  -- ... and equals `(1 - c) ϑ(pₘ₊₂; 4, 1) - (1 + c) ϑ(pₘ₊₂; 4, 3) = -c pₘ₊₂ + o(pₘ₊₂)`.
  have hsplit : ∀ m, B m = (1 - c) * thetaAP 4 1 (oddPrime m) -
      (1 + c) * thetaAP 4 3 (oddPrime m) := fun m ↦ by
    rw [thetaAP_four_oddPrime (.inl rfl), thetaAP_four_oddPrime (.inr rfl), mul_sum, mul_sum,
      ← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    rcases oddPrime_mod_four k with hk | hk
    · rw [ZMod.χ₄_nat_one_mod_four hk]
      simp [hk]
    · rw [ZMod.χ₄_nat_three_mod_four hk]
      simp [hk]
      ring
  have hlim : Tendsto (fun m ↦ B m / oddPrime m) atTop (𝓝 (-c)) := by
    have h1 := ((tendsto_thetaAP_div (q := 4) (a := 1) (by norm_num) (by norm_num)
      (by norm_num)).comp hq).const_mul (1 - c)
    have h3 := ((tendsto_thetaAP_div (q := 4) (a := 3) (by norm_num) (by norm_num)
      (by norm_num)).comp hq).const_mul (1 + c)
    rw [h4] at h1 h3
    refine ((h1.sub h3).congr fun m ↦ ?_).mono_right (le_of_eq ?_)
    · simp only [Function.comp_apply, hsplit m]
      ring
    · congr 1
      ring
  exact hc (neg_eq_zero.mp (tendsto_nhds_unique hlim hzero))

end RokickiConstant.PNT
