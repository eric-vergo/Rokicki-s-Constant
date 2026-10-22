/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import RokickiConstant.General.Irrational
import RokickiConstant.General.Oscillation

/-!
# Characters of higher order at the primes

Let `χ` be a Dirichlet character modulo `q`, let `p₀ = 2 < p₁ < ⋯` be the primes and
`S n = ∑_{k < n} χ(pₖ)`. `RokickiConstant.General.CharacterSums` shows that for a nonprincipal
*quadratic* `χ` the partial sums are neither bounded nor `c · n + O(1)`. Here we drop
quadraticity.

* **The linear case, every order.** For every nonprincipal `χ`, `S n` is not `c · n + O(1)` with a
  complex `c ≠ 0`. The prime part `G_χ(σ) = ∑ₖ χ(pₖ) pₖ ^ (-σ)` stays bounded as `σ → 1⁺`, since
  the logarithm of `L(σ, χ)` has the bounded derivative `L' / L` on `(1, 2]`
  (`exists_norm_primePart_le`), while summation by parts gives `G_χ(σ) = c ∑ₖ pₖ ^ (-σ) + O(1)`.
* **The order-`m` argument.** Splitting the logarithm of the Euler product by the exponent `j` of
  the prime power, `log L(s, χ) = ∑_{j < m} G_{χ ^ j}(j s) / j + tailPart χ m s`, where the tail
  (the powers `j ≥ m`) is holomorphic on `re s > 1 / m` and, if `χ ^ m = 1`, has real part
  tending to `+∞` as `s → 1 / m⁺`. If every `G_{χ ^ j}`, `0 < j < m`, continues to `re s > 0`,
  the identity theorem continues `L(s, χ) = exp (…)` to `re s > 1 / m` and the blow-up at `1 / m`
  contradicts the continuity of the entire function `L(·, χ)`. The same works for a finite
  product of `L`-functions, and continuation to `re s > θ` with `0 ≤ θ < 1 / m` suffices
  (`not_forall_exists_differentiableOn_primePart_of_lt`).
* **Order 3.** If `χ ^ 3 = 1` then `χ² = χ̄` on the primes, so `re S = O(n ^ θ)` continues both
  `j = 1` and `j = 2` terms of `log (L(s, χ) L(s, χ̄))` to `re s > θ` (the polynomial-growth Abel
  series of `RokickiConstant.General.Oscillation`), and the `j = 3` term blows up at `1 / 3`:
  for `θ < 1 / 3` the partial sums `∑_{k < n} re χ(pₖ)`, a fortiori `S n`, are not `O(n ^ θ)`.
  The bounded case is `θ = 0`.
* **Cubic residue constants.** Consequently `k ↦ χ(pₖ)` is not eventually periodic for a
  nonprincipal cubic `χ`, and the number whose `k`-th digit records whether `pₖ` is a cube modulo
  a prime `ℓ ≡ 1 (mod 3)` is irrational.

For `m ≥ 4` the bounded partial sums of `χ` alone do not continue the terms `G_{χ ^ j}(j s)` with
`2 ≤ j ≤ m - 2`; see `research/higher-order.md`.

## Main definitions

* `Complex.logTail m z`: the tail `∑_{j ≥ m} z ^ j / j` of the series of `-log (1 - z)`.
* `DirichletCharacter.tailPart χ m s`: `∑ₖ logTail m (χ(pₖ) pₖ ^ (-s))`.
* `Real.cubicResidueConstant ℓ b`.

## Main statements

* `DirichletCharacter.exists_norm_primePart_le`
* `DirichletCharacter.not_exists_norm_sum_sub_mul_le`: the linear case, complex slope.
* `DirichletCharacter.not_exists_abs_sum_re_sub_mul_le`: the linear case for the real parts.
* `DirichletCharacter.not_forall_exists_differentiableOn_primePart_of_lt`: the order-`m`
  argument; `DirichletCharacter.not_forall_exists_differentiableOn_primePart` is `θ = 0`.
* `DirichletCharacter.not_forall_exists_norm_sum_pow_le`: the simultaneous order-`m` statement;
  `DirichletCharacter.not_forall_exists_norm_sum_pow_le_of_two_mul_le` needs only `j ≤ m / 2`.
* `DirichletCharacter.not_exists_norm_sum_le_rpow_of_pow_three`: order 3, `S n ≠ O(n ^ θ)` for
  `θ < 1 / 3`; `not_exists_abs_sum_re_le_rpow_of_pow_three` for the real parts;
  `not_isBigO_rpow_of_pow_three`, `not_isBigO_rpow_one_third_sub_of_pow_three`,
  `not_isBigO_sum_re_rpow_of_pow_three`: Landau form;
  `not_exists_norm_sum_primesBelow_le_rpow_of_pow_three`,
  `not_isBigO_primesBelow_rpow_of_pow_three`: the sums `∑_{p < x} χ(p)` against `x ^ θ`.
* `DirichletCharacter.not_exists_norm_sum_le_of_pow_three`: order 3, bounded sums.
* `DirichletCharacter.not_exists_abs_sum_re_le_of_pow_three`: order 3, bounded real parts.
* `DirichletCharacter.irrational_tsum_of_pow_three`
* `Real.irrational_cubicResidueConstant`

## Tags

Dirichlet character, cubic character, Euler product, L-function, irrational
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset Complex

/-- The `k`-th prime `pₖ`, with `p₀ = 2`. -/
local notation "nthPrime" => Nat.nth Nat.Prime

namespace Complex

/-- The tail `-log (1 - z) - ∑_{j < m} z ^ j / j` of the Taylor series of `-log (1 - z)`: the
terms `z ^ j / j` with `j ≥ m`. (The `j = 0` term of the sum is `1 / 0 = 0`.) -/
noncomputable def logTail (m : ℕ) (z : ℂ) : ℂ := -log (1 - z) - ∑ j ∈ range m, z ^ j / j

/-- `logTail (m + 1) z = logTail m z - z ^ m / m`. -/
theorem logTail_succ (m : ℕ) (z : ℂ) : logTail (m + 1) z = logTail m z - z ^ m / m := by
  simp only [logTail, sum_range_succ]
  ring

/-- For `‖z‖ < 1` and `m ≥ 1`, `‖logTail m z‖ ≤ ‖z‖ ^ m (1 - ‖z‖)⁻¹ / m`. -/
theorem norm_logTail_le {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖logTail m z‖ ≤ ‖z‖ ^ m * (1 - ‖z‖)⁻¹ / m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h := norm_log_one_sub_inv_add_logTaylor_neg_le n hz
  have e : log (1 - z)⁻¹ + logTaylor (n + 1) (-z) = logTail (n + 1) z := by
    rw [log_inv _ (slitPlane_arg_ne_pi (RokickiConstant.one_sub_mem_slitPlane hz)), logTail,
      logTaylor, sub_eq_add_neg (-log (1 - z)), ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    have : ((-1 : ℂ) ^ (j + 1)) * (-1) ^ j = -1 := by
      rw [← pow_add, show j + 1 + j = 2 * j + 1 by ring, pow_succ, pow_mul]
      norm_num
    rw [neg_pow z, ← mul_assoc, this]
    ring
  rw [e] at h
  exact_mod_cast h

end Complex

/-- The partial sums of an eventually periodic real sequence are `c · n + O(1)`, where `c` is the
average of the sequence over one period. -/
theorem Function.EventuallyPeriodic.exists_abs_sum_real_sub_mul_le {a : ℕ → ℝ} {p : ℕ}
    (hp : 0 < p) (ha : EventuallyPeriodic a p) :
    ∃ c C : ℝ, ∀ n, |(∑ k ∈ range n, a k) - c * n| ≤ C := by
  obtain ⟨N, hN⟩ := ha.exists_forall_le
  have hblock : ∀ n, N ≤ n → ∑ k ∈ range (n + p), a k - ∑ k ∈ range n, a k =
      ∑ k ∈ range (N + p), a k - ∑ k ∈ range N, a k := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih, Nat.add_right_comm n 1 p, sum_range_succ, sum_range_succ, hN n hn]
      ring
  set c : ℝ := (∑ k ∈ range (N + p), a k - ∑ k ∈ range N, a k) / p
  have hcp : c * p = ∑ k ∈ range (N + p), a k - ∑ k ∈ range N, a k :=
    div_mul_cancel₀ _ (by positivity)
  have hper : EventuallyPeriodic (fun n ↦ ∑ k ∈ range n, a k - c * n) p := by
    refine eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    have := hblock n hn
    push_cast
    linear_combination this - hcp
  exact ⟨c, hper.exists_forall_abs_le hp⟩

namespace DirichletCharacter

variable {q : ℕ} (χ : DirichletCharacter ℂ q)

/-- On the real axis, `zₖ(σ) = χ(pₖ) · pₖ ^ (-σ)` with a real power. -/
theorem primeTerm_ofReal (k : ℕ) (σ : ℝ) :
    χ.primeTerm k σ = χ (nthPrime k) * (((nthPrime k : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [primeTerm, ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

/-- The prime part is holomorphic on `re s > 1`. -/
theorem differentiableOn_primePart : DifferentiableOn ℂ χ.primePart {s : ℂ | 1 < s.re} := by
  intro s₀ (hs₀ : 1 < s₀.re)
  obtain ⟨σ₀, hσ₀, hσ₀s⟩ := exists_between hs₀
  have hU : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const continuous_re
  refine (DifferentiableOn.differentiableAt ?_ (hU.mem_nhds hσ₀s)).differentiableWithinAt
  refine differentiableOn_tsum_of_summable_norm
    (summable_nthPrime_rpow (r := -σ₀) (by linarith)) (fun k s _ ↦ ?_) hU
    fun k s (hs : σ₀ < s.re) ↦ ?_
  · exact (((differentiableAt_id.neg).const_cpow (Or.inl (Nat.cast_ne_zero.2
      (Nat.prime_nth_prime k).ne_zero))).const_mul _).differentiableWithinAt
  · exact (χ.norm_primeTerm_le k s).trans (Real.rpow_le_rpow_of_exponent_le
      (Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le) (by linarith))

variable [NeZero q]

/-- The logarithm `F = primePart χ + primePowerPart χ` of `L(·, χ)` on `re s > 1` has derivative
`L' / L`. -/
theorem hasDerivAt_primePart_add_primePowerPart {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (fun s ↦ χ.primePart s + χ.primePowerPart s)
      (deriv (LFunction χ) s / LFunction χ s) s := by
  set F := fun s ↦ χ.primePart s + χ.primePowerPart s
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hF : DifferentiableAt ℂ F s :=
    (χ.differentiableOn_primePart.add (χ.differentiableOn_primePowerPart.mono
      fun s (hs : 1 < s.re) ↦ show 1 / 2 < s.re by linarith)).differentiableAt
      (hU.mem_nhds hs)
  have hexp : (fun s ↦ exp (F s)) =ᶠ[𝓝 s] LFunction χ :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun s hs ↦ χ.exp_primePart_add_primePowerPart hs
  have hL : HasDerivAt (LFunction χ) (exp (F s) * deriv F s) s :=
    hF.hasDerivAt.cexp.congr_of_eventuallyEq hexp.symm
  have he : exp (F s) = LFunction χ s := hexp.eq_of_nhds
  rw [hL.deriv, ← he, mul_div_cancel_left₀ _ (exp_ne_zero _)]
  exact hF.hasDerivAt

/-- **The prime part stays bounded as `σ → 1⁺`** for a nonprincipal character:
`‖∑ₖ χ(pₖ) pₖ ^ (-σ)‖` is bounded on `1 < σ ≤ 2`. The logarithm of `L(σ, χ)` has the bounded
derivative `L' / L` there, since `L(·, χ)` is entire and does not vanish on `re s ≥ 1`. -/
theorem exists_norm_primePart_le (hχ : χ ≠ 1) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖χ.primePart σ‖ ≤ M := by
  set F := fun s ↦ χ.primePart s + χ.primePowerPart s
  set g : ℝ → ℂ := fun t ↦ deriv (LFunction χ) t / LFunction χ t
  have hg : ContinuousOn g (Set.Icc 1 2) := by
    refine ContinuousOn.div ?_ ?_ fun t ht ↦
      LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simpa using ht.1)
    · exact ((((differentiable_LFunction hχ).contDiff (n := 1)).continuous_deriv le_rfl).comp
        continuous_ofReal).continuousOn
    · exact ((differentiable_LFunction hχ).continuous.comp continuous_ofReal).continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  obtain ⟨M, hM⟩ := χ.exists_norm_primePowerPart_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 ⟨le_rfl, by norm_num⟩)
  have h2 : (2 : ℝ) ∈ Set.Ioc 1 2 := ⟨by norm_num, le_rfl⟩
  refine ⟨‖F 2‖ + B + M, fun σ hσ hσ2 ↦ ?_⟩
  have hmvt := (convex_Ioc (1 : ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ ↦ F t) (f' := g) (fun t ht ↦
      (χ.hasDerivAt_primePart_add_primePowerPart (by simpa using ht.1)).comp_ofReal
        |>.hasDerivWithinAt) (fun t ht ↦ hB t (Set.Ioc_subset_Icc_self ht)) h2 ⟨hσ, hσ2⟩
  have hσ' : ‖σ - 2‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hP := hM σ (by simp [hσ.le])
  have hF : χ.primePart σ = F σ - F 2 + F 2 - χ.primePowerPart σ := by simp [F]
  rw [hF]
  push_cast at hmvt
  calc _ ≤ ‖F σ - F 2‖ + ‖F 2‖ + ‖χ.primePowerPart σ‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ B * 1 + ‖F 2‖ + M := by gcongr; exact hmvt.trans (by gcongr)
    _ = _ := by ring

/-- **The linear case, twisted.** For a nonprincipal character, a complex number `u` and a real
`c ≠ 0`, the real parts `re (u · ∑_{k < n} χ(pₖ))` are not of the form `c · n + O(1)`. By summation
by parts `re (u · primePart χ σ) = c ∑ₖ pₖ ^ (-σ) + O(1)` for `σ > 1`, whose right side is unbounded
as `σ → 1⁺` while the left side is bounded by `exists_norm_primePart_le`. -/
theorem not_exists_abs_re_mul_sum_sub_mul_le (hχ : χ ≠ 1) (u : ℂ) :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n,
      |(u * ∑ k ∈ range n, χ (nthPrime k)).re - c * n| ≤ C := by
  rintro ⟨c, hc, C, h⟩
  obtain ⟨M, hM⟩ := χ.exists_norm_primePart_le hχ
  have hle : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      |c| * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ) ≤ ‖u‖ * M + 2 * C := by
    intro σ hσ hσ2
    have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
    have hfs : Summable fun k ↦ (nthPrime k : ℝ) ^ (-σ) := summable_nthPrime_rpow (by linarith)
    have hs : HasSum (fun k ↦ ((u * χ (nthPrime k)).re - c) * (nthPrime k : ℝ) ^ (-σ))
        ((u * χ.primePart σ).re - c * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ)) := by
      convert (hasSum_re ((χ.summable_primeTerm hσ').hasSum.mul_left u)).sub
        (hfs.hasSum.mul_left c) using 1
      · funext k
        rw [primeTerm_ofReal, ← mul_assoc, re_mul_ofReal]
        ring
      · rfl
    have he : ∀ n, |∑ k ∈ range n, ((u * χ (nthPrime k)).re - c)| ≤ C := fun n ↦ by
      simpa [sum_sub_distrib, mul_sum, re_sum, mul_comm] using h n
    have hC : 0 ≤ C := (abs_nonneg _).trans (h 0)
    have hf0 : (nthPrime 0 : ℝ) ^ (-σ) ≤ 1 := by
      rw [Nat.nth_prime_zero_eq_two]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h1 : |(u * χ.primePart σ).re - c * ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ)| ≤ 2 * C := by
      rw [← hs.tsum_eq]
      calc _ ≤ 2 * C * (nthPrime 0 : ℝ) ^ (-σ) :=
            abs_tsum_mul_le_of_abs_sum_le he (fun _ ↦ by positivity)
              (antitone_natCast_rpow_neg (Nat.prime_nth_prime 0).pos nthPrime_strictMono
                (by linarith)) hs.summable
        _ ≤ 2 * C := mul_le_of_le_one_right (by linarith) hf0
    have h2 : |(u * χ.primePart σ).re| ≤ ‖u‖ * M :=
      (abs_re_le_norm _).trans (by rw [norm_mul]; gcongr; exact hM σ hσ hσ2)
    have hT : 0 ≤ ∑' k : ℕ, (nthPrime k : ℝ) ^ (-σ) := tsum_nonneg fun _ ↦ by positivity
    rw [abs_le] at h1 h2
    rcases abs_cases c with ⟨hc', -⟩ | ⟨hc', -⟩ <;> rw [hc'] <;> nlinarith
  have hT := (tendsto_tsum_nthPrime_rpow_neg.const_mul_atTop (abs_pos.2 hc)).eventually
    (eventually_gt_atTop (‖u‖ * M + 2 * C))
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := (hT.and (Ioc_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num))).exists
  exact absurd (hle σ hσ1 hσ2) (not_le.2 hσ)

/-- **The linear case for every nonprincipal character.** The partial sums
`∑_{k < n} χ(pₖ)` of a nonprincipal Dirichlet character over the primes are not of the form
`c · n + O(1)` with a complex `c ≠ 0`. -/
theorem not_exists_norm_sum_sub_mul_le (hχ : χ ≠ 1) :
    ¬ ∃ c : ℂ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n, ‖(∑ k ∈ range n, χ (nthPrime k)) - c * n‖ ≤ C := by
  rintro ⟨c, hc, C, h⟩
  refine χ.not_exists_abs_re_mul_sum_sub_mul_le hχ (starRingEnd ℂ c)
    ⟨normSq c, (normSq_pos.2 hc).ne', ‖c‖ * C, fun n ↦ ?_⟩
  have he : (starRingEnd ℂ c * ∑ k ∈ range n, χ (nthPrime k)).re - normSq c * n =
      (starRingEnd ℂ c * ((∑ k ∈ range n, χ (nthPrime k)) - c * n)).re := by
    rw [mul_sub, sub_re, ← mul_assoc, ← normSq_eq_conj_mul_self]
    simp
  rw [he]
  refine (abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (h n) (norm_nonneg _)

/-- **The linear case for the real parts.** For a nonprincipal character, the real parts
`∑_{k < n} re χ(pₖ)` are not of the form `c · n + O(1)` with a real `c ≠ 0`. -/
theorem not_exists_abs_sum_re_sub_mul_le (hχ : χ ≠ 1) :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∃ C : ℝ, ∀ n, |(∑ k ∈ range n, (χ (nthPrime k)).re) - c * n| ≤ C := by
  simpa [re_sum] using χ.not_exists_abs_re_mul_sum_sub_mul_le hχ 1

end DirichletCharacter

namespace DirichletCharacter

section TailPart

variable {q : ℕ} (χ : DirichletCharacter ℂ q)

/-- The part `∑ₖ logTail m (zₖ(s))` of the logarithm of the Euler product made of the prime powers
`pₖ ^ j` with `j ≥ m`; it converges absolutely for `re s > 1 / m`. -/
noncomputable def tailPart (m : ℕ) (s : ℂ) : ℂ := ∑' k : ℕ, logTail m (χ.primeTerm k s)

/-- For `0 < σ₀ ≤ re s`, `‖zₖ(s)‖ ≤ 2 ^ (-σ₀) < 1`. -/
theorem norm_primeTerm_le_two_rpow (k : ℕ) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) :
    ‖χ.primeTerm k s‖ ≤ (2 : ℝ) ^ (-σ₀) := by
  refine (χ.norm_primeTerm_le k s).trans ?_
  have h2 : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast (Nat.prime_nth_prime k).two_le
  exact (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith))

/-- For `0 < σ₀ ≤ re s` and `m ≥ 1`, the `k`-th term of `tailPart χ m s` has norm at most
`(1 - 2 ^ (-σ₀))⁻¹ pₖ ^ (-m σ₀)`. -/
theorem norm_tailPart_term_le {m : ℕ} (hm : 0 < m) (k : ℕ) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {s : ℂ}
    (hs : σ₀ ≤ s.re) :
    ‖logTail m (χ.primeTerm k s)‖ ≤ (1 - (2 : ℝ) ^ (-σ₀))⁻¹ * (nthPrime k : ℝ) ^ (-(m * σ₀)) := by
  have hr : (2 : ℝ) ^ (-σ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hz := χ.norm_primeTerm_le_two_rpow k hσ₀ hs
  refine (norm_logTail_le hm (hz.trans_lt hr)).trans ?_
  have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
  have hpow : ‖χ.primeTerm k s‖ ^ m ≤ (nthPrime k : ℝ) ^ (-(m * σ₀)) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) ((χ.norm_primeTerm_le k s).trans
      (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le)
        (by linarith : -s.re ≤ -σ₀))) m).trans (le_of_eq ?_)
    rw [← Real.rpow_mul_natCast (by positivity)]
    ring_nf
  have hinv : (1 - ‖χ.primeTerm k s‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ₀))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  calc _ ≤ ‖χ.primeTerm k s‖ ^ m * (1 - ‖χ.primeTerm k s‖)⁻¹ :=
        div_le_self (by have := hz.trans_lt hr; positivity) hm1
    _ ≤ (nthPrime k : ℝ) ^ (-(m * σ₀)) * (1 - (2 : ℝ) ^ (-σ₀))⁻¹ := by
        gcongr
        have := hz.trans_lt hr
        rw [inv_nonneg]
        linarith
    _ = _ := mul_comm _ _

/-- `tailPart χ m s` converges absolutely for `re s > 1 / m`. -/
theorem summable_tailPart_term {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : 1 / m < s.re) :
    Summable fun k ↦ logTail m (χ.primeTerm k s) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hσ : 1 < m * s.re := by rwa [div_lt_iff₀' hm'] at hs
  exact .of_norm_bounded ((summable_nthPrime_rpow (r := -(m * s.re)) (by linarith)).mul_left _)
    fun k ↦ χ.norm_tailPart_term_le hm k (lt_trans (by positivity) hs) le_rfl

/-- `tailPart χ m` is holomorphic on `re s > 1 / m`. -/
theorem differentiableOn_tailPart {m : ℕ} (hm : 0 < m) :
    DifferentiableOn ℂ (χ.tailPart m) {s : ℂ | 1 / m < s.re} := by
  intro s₀ (hs₀ : 1 / m < s₀.re)
  obtain ⟨σ₀, hσ₀, hσ₀s⟩ := exists_between hs₀
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hσ₀' : 0 < σ₀ := lt_trans (by positivity) hσ₀
  have hmσ : 1 < m * σ₀ := by rwa [div_lt_iff₀' hm'] at hσ₀
  have hU : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const continuous_re
  refine (DifferentiableOn.differentiableAt ?_ (hU.mem_nhds hσ₀s)).differentiableWithinAt
  refine differentiableOn_tsum_of_summable_norm
    ((summable_nthPrime_rpow (r := -(m * σ₀)) (by linarith)).mul_left _)
    (fun k s (hs : σ₀ < s.re) ↦ ?_) hU fun k s (hs : σ₀ < s.re) ↦
      χ.norm_tailPart_term_le hm k hσ₀' hs.le
  have hd : DifferentiableAt ℂ (χ.primeTerm k) s := ((differentiableAt_id.neg).const_cpow
    (Or.inl (Nat.cast_ne_zero.2 (Nat.prime_nth_prime k).ne_zero))).const_mul _
  have hz : ‖χ.primeTerm k s‖ < 1 := (χ.norm_primeTerm_le_two_rpow k hσ₀' hs.le).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  refine DifferentiableAt.differentiableWithinAt ?_
  simp only [logTail]
  refine ((hd.const_sub 1).clog (RokickiConstant.one_sub_mem_slitPlane hz)).neg.sub ?_
  exact DifferentiableAt.fun_sum fun j _ ↦ (hd.pow j).div_const _

/-- **Splitting the logarithm of the Euler product by the exponent of the prime power.** For
`re s > 1`, `primePart χ s + primePowerPart χ s` is the sum of `primePart (χ ^ j) (j s) / j` over
`j < m` and of `tailPart χ m s`. -/
theorem primePart_add_primePowerPart_eq {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : 1 < s.re) :
    χ.primePart s + χ.primePowerPart s =
      ∑ j ∈ range m, (χ ^ j).primePart (j * s) / j + χ.tailPart m s := by
  have hterm (j k : ℕ) : (χ ^ j).primeTerm k (j * s) / j = χ.primeTerm k s ^ j / j := by
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · rw [primeTerm, primeTerm, MulChar.pow_apply' χ hj, mul_pow, ← cpow_nat_mul, mul_neg]
  have hsum : ∀ j ∈ range m, Summable fun k ↦ χ.primeTerm k s ^ j / j := by
    intro j _
    simp_rw [← hterm]
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · refine ((χ ^ j).summable_primeTerm ?_).div_const _
      have hj' : (1 : ℝ) ≤ j := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hj)
      simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
      nlinarith
  have hpart (j : ℕ) : (χ ^ j).primePart (j * s) / j = ∑' k, χ.primeTerm k s ^ j / j := by
    rw [primePart, ← tsum_div_const]
    exact tsum_congr fun k ↦ hterm j k
  simp_rw [hpart]
  rw [primePart, primePowerPart, tailPart, ← (χ.summable_primeTerm hs).tsum_add
    (χ.summable_primePowerPart_term (by linarith)), ← Summable.tsum_finsetSum hsum,
    ← Summable.tsum_add (summable_sum hsum) (χ.summable_tailPart_term hm ?_)]
  · refine tsum_congr fun k ↦ ?_
    simp only [logTail]
    ring
  · have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
    calc 1 / (m : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hm1
      _ < s.re := hs

/-- If `χ ^ m = 1`, then `χ(a) ^ m = 1` at every unit `a`. -/
theorem apply_pow_eq_one_of_isUnit {m : ℕ} (hχm : χ ^ m = 1) {a : ZMod q} (ha : IsUnit a) :
    χ a ^ m = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [← MulChar.pow_apply_coe, hχm, MulChar.one_apply_coe]

variable [NeZero q] in
/-- If `χ ^ m = 1` with `m ≥ 1`, then for real `σ > 1 / m` the real part of `tailPart χ m σ` is at
least `∑ₖ pₖ ^ (-m σ) / m` minus a constant independent of `σ`: the `j = m` terms
`χ(p) ^ m p ^ (-m σ) / m = p ^ (-m σ) / m` (for `p ∤ q`) dominate. -/
theorem le_re_tailPart {m : ℕ} (hm : 0 < m) (hχm : χ ^ m = 1) {σ : ℝ} (hσ : 1 / m < σ) :
    (∑' k : ℕ, (nthPrime k : ℝ) ^ (-(m * σ))) / m - q / m -
        (1 - (2 : ℝ) ^ (-(1 / m : ℝ)))⁻¹ *
          ∑' k : ℕ, (nthPrime k : ℝ) ^ (-((m + 1 : ℕ) * (1 / m : ℝ))) ≤
      (χ.tailPart m σ).re := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hmσ : 1 < m * σ := by rwa [div_lt_iff₀' hm'] at hσ
  set K := (1 - (2 : ℝ) ^ (-(1 / m : ℝ)))⁻¹
  set a : ℕ → ℝ := fun k ↦ (nthPrime k : ℝ) ^ (-(m * σ))
  set c : ℕ → ℝ := fun k ↦ (nthPrime k : ℝ) ^ (-((m + 1 : ℕ) * (1 / m : ℝ)))
  set d : ℕ → ℝ := fun k ↦ if k < q then 1 / m else 0
  have ha : Summable a := summable_nthPrime_rpow (by linarith)
  have hc : Summable c := summable_nthPrime_rpow (by
    have : (m + 1 : ℕ) * (1 / m : ℝ) = 1 + 1 / m := by push_cast; field_simp
    rw [this]
    have : (0 : ℝ) < 1 / m := by positivity
    linarith)
  have hd : HasSum d (q / m) := by
    have h : HasSum d (∑ k ∈ range q, d k) := hasSum_sum_of_ne_finset_zero
      (fun k hk ↦ by simp only [mem_range] at hk; simp [d, hk])
    have e : ∑ k ∈ range q, d k = q / m := by
      rw [sum_congr rfl fun k hk ↦ (ite_eq_left_iff.2 fun h ↦ absurd (mem_range.1 hk) h)]
      simp [div_eq_mul_inv]
    rwa [e] at h
  refine hasSum_le (fun k ↦ ?_) (((ha.hasSum.div_const m).sub hd).sub (hc.hasSum.mul_left K))
    (hasSum_re (χ.summable_tailPart_term hm (by simpa using hσ)).hasSum)
  have hsplit : logTail m (χ.primeTerm k σ) =
      χ.primeTerm k σ ^ m / m + logTail (m + 1) (χ.primeTerm k σ) := by
    rw [logTail_succ]
    ring
  have hR : ‖logTail (m + 1) (χ.primeTerm k σ)‖ ≤ K * c k :=
    χ.norm_tailPart_term_le (Nat.succ_pos m) k (by positivity) (by simpa using hσ.le)
  have hzm : χ.primeTerm k σ ^ m / m = χ (nthPrime k) ^ m * ((a k / m : ℝ) : ℂ) := by
    rw [primeTerm_ofReal, mul_pow, ← ofReal_pow, ← Real.rpow_mul_natCast (by positivity),
      show -σ * (m : ℝ) = -(m * σ) by ring]
    simp only [a, ofReal_div, ofReal_natCast]
    ring
  have ha1 : a k ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le) (by linarith)
  have hz : a k / m - d k ≤ (χ.primeTerm k σ ^ m / m).re := by
    rw [hzm]
    by_cases hu : IsUnit ((nthPrime k : ℕ) : ZMod q)
    · rw [χ.apply_pow_eq_one_of_isUnit hχm hu, one_mul, ofReal_re]
      have : 0 ≤ d k := by simp only [d]; split_ifs <;> positivity
      linarith
    · rw [χ.map_nonunit hu, zero_pow hm.ne', zero_mul, zero_re]
      have hk : k < q := by
        have hdvd : nthPrime k ∣ q := by
          by_contra h
          exact hu ((ZMod.isUnit_prime_iff_not_dvd (Nat.prime_nth_prime k)).2 h)
        have := Nat.le_of_dvd (NeZero.pos q) hdvd
        have := Nat.add_two_le_nth_prime k
        omega
      simp only [d, hk, ite_true]
      rw [div_sub_div_same]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hm'.le
  have := abs_le.1 ((abs_re_le_norm _).trans hR)
  rw [hsplit, add_re]
  linarith

variable [NeZero q] in
/-- If `χ ^ m = 1` with `m ≥ 1`, then `re (tailPart χ m σ) → +∞` as `σ → 1 / m⁺`. -/
theorem tendsto_re_tailPart {m : ℕ} (hm : 0 < m) (hχm : χ ^ m = 1) :
    Tendsto (fun σ : ℝ ↦ (χ.tailPart m σ).re) (𝓝[>] (1 / m : ℝ)) atTop := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have h2 : Tendsto (fun σ : ℝ ↦ m * σ) (𝓝[>] (1 / m)) (𝓝[>] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const_mul (m : ℝ)).tendsto' _ _
      (by field_simp)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun σ (hσ : 1 / m < σ) ↦
        show 1 < m * σ by rwa [div_lt_iff₀' hm'] at hσ⟩
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-(q / m +
    (1 - (2 : ℝ) ^ (-(1 / m : ℝ)))⁻¹ *
      ∑' k : ℕ, (nthPrime k : ℝ) ^ (-((m + 1 : ℕ) * (1 / m : ℝ)))))
    ((tendsto_tsum_nthPrime_rpow_neg.comp h2).atTop_div_const hm'))
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 / m < σ)
  have := χ.le_re_tailPart hm hχm hσ
  simp only [Function.comp_apply] at this ⊢
  linarith

end TailPart

/-- A finite nonempty sum of functions tending to `+∞` tends to `+∞`. -/
theorem _root_.Filter.Tendsto.finsetSum_atTop {ι α : Type*} {l : Filter α} {X : Finset ι}
    (hX : X.Nonempty) {f : ι → α → ℝ} (h : ∀ i ∈ X, Tendsto (f i) l atTop) :
    Tendsto (fun a ↦ ∑ i ∈ X, f i a) l atTop := by
  induction hX using Finset.Nonempty.cons_induction with
  | singleton i => simp [h i (mem_singleton_self i)]
  | cons i s hi hs ih =>
    simp only [sum_cons]
    exact (h i (mem_cons_self i s)).atTop_add_atTop (ih fun j hj ↦ h j (mem_cons_of_mem hj))

section Engine

variable {q : ℕ} [NeZero q]

/-- **The order-`m` argument, with a continuation to `re s > θ`.** Let `X` be a nonempty finite
set of nonprincipal Dirichlet characters with `ψ ^ m = 1` for all `ψ ∈ X`, and let
`0 ≤ θ < 1 / m`. Then it is impossible that for every `0 < j < m` the sum
`∑_{ψ ∈ X} ∑ₖ ψ(pₖ) ^ j pₖ ^ (-s)` of prime parts continues holomorphically from `re s > 1` to
`re s > θ`.

Otherwise `∏_{ψ ∈ X} L(s, ψ) = exp Φ(s)` with
`Φ(s) = ∑_{0 < j < m} B_j(j s) / j + ∑_{ψ ∈ X} tailPart ψ m s` holomorphic on `re s > 1 / m`
(identity theorem), and as `σ → 1 / m⁺` the terms `B_j(j σ)` stay bounded (as `θ < 1 / m`) while
`re (tailPart ψ m σ) → +∞`, contradicting the continuity of the entire function `∏ L(·, ψ)` at
`1 / m`. -/
theorem not_forall_exists_differentiableOn_primePart_of_lt {X : Finset (DirichletCharacter ℂ q)}
    (hX : X.Nonempty) (hX₁ : ∀ ψ ∈ X, ψ ≠ 1) {m : ℕ} (hm : 0 < m) (hXm : ∀ ψ ∈ X, ψ ^ m = 1)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθm : θ < 1 / m) :
    ¬ ∀ j, 0 < j → j < m → ∃ B : ℂ → ℂ, DifferentiableOn ℂ B {s : ℂ | θ < s.re} ∧
      ∀ s : ℂ, 1 < s.re → B s = ∑ ψ ∈ X, (ψ ^ j).primePart s := by
  intro h
  choose! B hB hBeq using h
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set V : Set ℂ := {s | θ < s.re}
  set U : Set ℂ := {s | 1 / m < s.re}
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_re
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUV : U ⊆ V := fun s (hs : 1 / m < s.re) ↦ show θ < s.re from hθm.trans hs
  set A : ℂ → ℂ := fun s ↦ ∑ j ∈ range m, B j (j * s) / j
  set Φ : ℂ → ℂ := fun s ↦ A s + ∑ ψ ∈ X, ψ.tailPart m s
  set Lp : ℂ → ℂ := fun s ↦ ∏ ψ ∈ X, LFunction ψ s
  have hA : DifferentiableOn ℂ A V := by
    refine DifferentiableOn.fun_sum fun j hj ↦ ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · have hmaps : Set.MapsTo (fun s : ℂ ↦ (j : ℂ) * s) V V := fun s (hs : θ < s.re) ↦ by
        change θ < ((j : ℂ) * s).re
        simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
        have hj' : (1 : ℝ) ≤ j := Nat.one_le_cast.2 hj0
        nlinarith
      exact ((hB j hj0 (mem_range.1 hj)).comp (differentiableOn_id.const_mul (j : ℂ))
        hmaps).div_const _
  have hΦ : DifferentiableOn ℂ Φ U :=
    (hA.mono hUV).add (DifferentiableOn.fun_sum fun ψ _ ↦ ψ.differentiableOn_tailPart hm)
  have hLp : Differentiable ℂ Lp := by
    have := Differentiable.finsetProd (u := X) (f := fun ψ ↦ LFunction ψ)
      fun ψ hψ ↦ differentiable_LFunction (hX₁ ψ hψ)
    convert this using 1
    ext s
    simp [Lp]
  -- the Euler product
  have hEuler : ∀ s : ℂ, 1 < s.re → exp (Φ s) = Lp s := by
    intro s hs
    have hj : ∀ j ∈ range m, B j (j * s) / j = ∑ ψ ∈ X, (ψ ^ j).primePart (j * s) / j := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
      · have hj' : (1 : ℝ) ≤ j := Nat.one_le_cast.2 hj0
        rw [hBeq j hj0 (mem_range.1 hj) _ (by
          simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
          nlinarith), sum_div]
    have e : ∑ ψ ∈ X, (ψ.primePart s + ψ.primePowerPart s) = ∑ ψ ∈ X,
        (∑ j ∈ range m, (ψ ^ j).primePart (j * s) / j + ψ.tailPart m s) :=
      sum_congr rfl fun ψ _ ↦ ψ.primePart_add_primePowerPart_eq hm hs
    have hΦs : Φ s = ∑ ψ ∈ X, (ψ.primePart s + ψ.primePowerPart s) := by
      rw [e, sum_add_distrib]
      simp only [Φ, A]
      rw [sum_congr rfl hj, sum_comm]
    rw [hΦs, exp_sum]
    exact prod_congr rfl fun ψ _ ↦ ψ.exp_primePart_add_primePowerPart hs
  -- the identity theorem extends it to `re s > 1 / m`
  have hU2 : (2 : ℂ) ∈ U := by
    change 1 / (m : ℝ) < (2 : ℂ).re
    have : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one hm']; exact Nat.one_le_cast.2 hm
    have h2 : (2 : ℂ).re = 2 := by norm_num
    rw [h2]
    linarith
  have hEq : Set.EqOn (fun s ↦ exp (Φ s)) Lp U := by
    refine (hΦ.cexp.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
      (hLp.differentiableOn.analyticOnNhd hUo) (convex_halfSpace_re_gt _).isPreconnected hU2 ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
    exact hEuler s hs
  -- `exp (re Φ σ) = ‖∏ L(σ, ψ)‖` converges as `σ → 1 / m⁺` ...
  have hlim : Tendsto (fun σ : ℝ ↦ Real.exp (Φ σ).re) (𝓝[>] (1 / m)) (𝓝 ‖Lp (1 / m : ℝ)‖) :=
    (tendsto_nhdsWithin_of_tendsto_nhds ((hLp.continuous.comp continuous_ofReal).norm.tendsto
      _)).congr' (eventually_nhdsWithin_of_forall fun σ (hσ : 1 / m < σ) ↦ by
        have := hEq (show (σ : ℂ) ∈ U by simpa [U] using hσ)
        simp only at this
        simp [← this, Complex.norm_exp])
  -- ... but `re A σ` converges (as `θ < 1 / m`) and `re (tailPart ψ m σ) → +∞`
  have hAc : ContinuousAt (fun σ : ℝ ↦ (A σ).re) (1 / m) :=
    continuous_re.continuousAt.comp ((hA.continuousOn.continuousAt (hVo.mem_nhds
      (show θ < ((1 / m : ℝ) : ℂ).re by rw [ofReal_re]; exact hθm))).comp
      continuous_ofReal.continuousAt)
  have htail : Tendsto (fun σ : ℝ ↦ (∑ ψ ∈ X, ψ.tailPart m σ).re) (𝓝[>] (1 / m)) atTop := by
    simp only [re_sum]
    exact Tendsto.finsetSum_atTop hX fun ψ hψ ↦ ψ.tendsto_re_tailPart hm (hXm ψ hψ)
  have hinf : Tendsto (fun σ : ℝ ↦ Real.exp (Φ σ).re) (𝓝[>] (1 / m)) atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    simp only [Φ, add_re]
    exact (hAc.tendsto.mono_left nhdsWithin_le_nhds).add_atTop htail
  exact not_tendsto_atTop_of_tendsto_nhds hlim hinf

/-- **The order-`m` argument.** Let `X` be a nonempty finite set of nonprincipal Dirichlet
characters with `ψ ^ m = 1` for all `ψ ∈ X`. Then it is impossible that for every `0 < j < m` the
sum `∑_{ψ ∈ X} ∑ₖ ψ(pₖ) ^ j pₖ ^ (-s)` of prime parts continues holomorphically from `re s > 1`
to `re s > 0`. This is `not_forall_exists_differentiableOn_primePart_of_lt` with `θ = 0`. -/
theorem not_forall_exists_differentiableOn_primePart {X : Finset (DirichletCharacter ℂ q)}
    (hX : X.Nonempty) (hX₁ : ∀ ψ ∈ X, ψ ≠ 1) {m : ℕ} (hm : 0 < m) (hXm : ∀ ψ ∈ X, ψ ^ m = 1) :
    ¬ ∀ j, 0 < j → j < m → ∃ B : ℂ → ℂ, DifferentiableOn ℂ B {s : ℂ | 0 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → B s = ∑ ψ ∈ X, (ψ ^ j).primePart s :=
  not_forall_exists_differentiableOn_primePart_of_lt hX hX₁ hm hXm le_rfl
    (by have : (0 : ℝ) < m := Nat.cast_pos.2 hm; positivity)

/-- **Simultaneous version for characters of order `m`.** If `χ ≠ 1` and `χ ^ m = 1`, the partial
sums `∑_{k < n} χ(pₖ) ^ j` cannot all be bounded for `0 < j < m`. For `m = 2` this is
`DirichletCharacter.IsQuadratic.not_exists_norm_sum_le`. -/
theorem not_forall_exists_norm_sum_pow_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {m : ℕ}
    (hm : 0 < m) (hχm : χ ^ m = 1) :
    ¬ ∀ j, 0 < j → j < m → ∃ C : ℝ, ∀ n, ‖∑ k ∈ range n, (χ ^ j) (nthPrime k)‖ ≤ C := by
  intro h
  refine not_forall_exists_differentiableOn_primePart (X := {χ}) (singleton_nonempty χ)
    (by simpa using hχ) hm (by simpa using hχm) fun j hj hjm ↦ ?_
  obtain ⟨C, hC⟩ := h j hj hjm
  refine ⟨abelSeries (fun k ↦ (χ ^ j) (nthPrime k)) nthPrime,
    differentiableOn_abelSeries hC (Nat.prime_nth_prime 0).pos nthPrime_strictMono,
    fun s hs ↦ ?_⟩
  rw [sum_singleton, abelSeries_eq_tsum hC (Nat.prime_nth_prime 0).pos nthPrime_strictMono hs]
  rfl

omit [NeZero q] in
/-- If `χ ^ m = 1` and `j ≤ m`, then `χ ^ (m - j)` is the complex conjugate of `χ ^ j`. -/
theorem pow_sub_apply_eq_conj {χ : DirichletCharacter ℂ q} {m : ℕ} (hχm : χ ^ m = 1) {j : ℕ}
    (hjm : j ≤ m) (a : ZMod q) :
    (χ ^ (m - j)) a = starRingEnd ℂ ((χ ^ j) a) := by
  by_cases ha : IsUnit a
  · have h1 : (χ ^ j) a * (χ ^ (m - j)) a = 1 := by
      rw [← MulChar.mul_apply, ← pow_add, Nat.add_sub_cancel' hjm, hχm]
      obtain ⟨u, rfl⟩ := ha
      exact MulChar.one_apply_coe u
    have h2 : (χ ^ j) a * starRingEnd ℂ ((χ ^ j) a) = 1 := by
      obtain ⟨u, rfl⟩ := ha
      rw [mul_conj, normSq_eq_norm_sq, (χ ^ j).unit_norm_eq_one u]
      norm_num
    have hz : (χ ^ j) a ≠ 0 := left_ne_zero_of_mul_eq_one h1
    exact mul_left_cancel₀ hz (h1.trans h2.symm)
  · rw [(χ ^ (m - j)).map_nonunit ha, (χ ^ j).map_nonunit ha, map_zero]

/-- **Simultaneous version, half the range.** If `χ ≠ 1` and `χ ^ m = 1`, the partial sums
`∑_{k < n} χ(pₖ) ^ j` cannot all be bounded for `0 < j ≤ m / 2`: the sums for `j` and `m - j` are
complex conjugate. For a character of order `5`, the sums of `χ` and of `χ²` are not both
bounded. -/
theorem not_forall_exists_norm_sum_pow_le_of_two_mul_le {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {m : ℕ} (hm : 0 < m) (hχm : χ ^ m = 1) :
    ¬ ∀ j, 0 < j → 2 * j ≤ m → ∃ C : ℝ, ∀ n, ‖∑ k ∈ range n, (χ ^ j) (nthPrime k)‖ ≤ C := by
  intro h
  refine not_forall_exists_norm_sum_pow_le hχ hm hχm fun j hj hjm ↦ ?_
  by_cases h2 : 2 * j ≤ m
  · exact h j hj h2
  · obtain ⟨C, hC⟩ := h (m - j) (by omega) (by omega)
    refine ⟨C, fun n ↦ ?_⟩
    have e : ∑ k ∈ range n, (χ ^ j) (nthPrime k) =
        starRingEnd ℂ (∑ k ∈ range n, (χ ^ (m - j)) (nthPrime k)) := by
      rw [map_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [pow_sub_apply_eq_conj hχm hjm.le, Complex.conj_conj]
    rw [e, Complex.norm_conj]
    exact hC n

end Engine

section Cubic

/-- A cube root of unity `z` satisfies `z ^ 2 = conj z`. -/
theorem _root_.Complex.sq_eq_conj_of_pow_three_eq_one {z : ℂ} (hz : z ^ 3 = 1) :
    z ^ 2 = starRingEnd ℂ z := by
  have hn : ‖z‖ = 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  have h2 : z * starRingEnd ℂ z = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hn]
    norm_num
  linear_combination starRingEnd ℂ z * hz - z ^ 2 * h2

/-- A cube root of unity other than `1` has real part `-1 / 2`. -/
theorem _root_.Complex.re_eq_of_pow_three_eq_one {z : ℂ} (hz : z ^ 3 = 1) (h1 : z ≠ 1) :
    z.re = -1 / 2 := by
  have h : z ^ 2 + z + 1 = 0 := by
    have : (z - 1) * (z ^ 2 + z + 1) = 0 := by linear_combination hz
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  rw [sq_eq_conj_of_pow_three_eq_one hz] at h
  have := congrArg re h
  simp only [add_re, conj_re, one_re, zero_re] at this
  linarith

variable {q : ℕ} {χ : DirichletCharacter ℂ q}

/-- For a character with `χ ^ 3 = 1`, `χ(a) ^ 2 = conj χ(a)`. -/
theorem apply_sq_eq_conj_of_pow_three (h3 : χ ^ 3 = 1) (a : ZMod q) :
    χ a ^ 2 = starRingEnd ℂ (χ a) := by
  by_cases ha : IsUnit a
  · exact sq_eq_conj_of_pow_three_eq_one (χ.apply_pow_eq_one_of_isUnit h3 ha)
  · simp [χ.map_nonunit ha]

/-- For a character with `χ ^ 3 = 1`, `χ(a) + χ²(a) = 2 re χ(a)`. -/
theorem apply_add_sq_apply_eq_of_pow_three (h3 : χ ^ 3 = 1) (a : ZMod q) :
    χ a + (χ ^ 2) a = ((2 * (χ a).re : ℝ) : ℂ) := by
  rw [MulChar.pow_apply' χ two_ne_zero, apply_sq_eq_conj_of_pow_three h3, add_conj]

variable [NeZero q]

/-- **Characters of order 3, prime-scale form.** For a nonprincipal `χ` with `χ ^ 3 = 1` and
`θ < 1 / 3`, there is no constant `C` with `|∑_{j ≤ k} re χ(pⱼ)| ≤ C pₖ ^ θ` for all `k`.

Apply `not_forall_exists_differentiableOn_primePart_of_lt` with `X = {χ, χ²}`, `m = 3` and the
exponent `max θ 0 < 1 / 3`: since `χ² = χ̄` on the primes, both `j = 1` and `j = 2` require only
the continuation of `G_χ + G_{χ̄} = 2 ∑ₖ re χ(pₖ) pₖ ^ (-s)` to `re s > max θ 0`, which the Abel
series under polynomially bounded partial sums provides. The bounded case is `θ = 0`. -/
theorem not_exists_abs_sum_succ_re_le_nthPrime_rpow_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1)
    {θ : ℝ} (hθ : θ < 1 / 3) :
    ¬ ∃ C : ℝ, ∀ k, |∑ j ∈ range (k + 1), (χ (nthPrime j)).re| ≤ C * (nthPrime k : ℝ) ^ θ := by
  classical
  rintro ⟨C, hC⟩
  have hθ' : max θ 0 < 1 / ((3 : ℕ) : ℝ) := max_lt (by simpa using hθ) (by norm_num)
  have hne : χ ≠ χ ^ 2 := fun h ↦ hχ (by rw [pow_two] at h; exact mul_eq_left.1 h.symm)
  have h21 : χ ^ 2 ≠ 1 := fun h ↦ hχ (by rwa [pow_succ, h, one_mul] at h3)
  have h23 : (χ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  have h4 : (χ ^ 2) ^ 2 = χ := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, h3, one_mul]
  set a : ℕ → ℂ := fun k ↦ χ (nthPrime k) + (χ ^ 2) (nthPrime k)
  have ha : ∀ k, ‖∑ j ∈ range (k + 1), a j‖ ≤ 2 * |C| * (nthPrime k : ℝ) ^ max θ 0 := by
    intro k
    have : ∑ j ∈ range (k + 1), a j =
        ((2 * ∑ j ∈ range (k + 1), (χ (nthPrime j)).re : ℝ) : ℂ) := by
      rw [mul_sum]
      push_cast
      exact sum_congr rfl fun j _ ↦ by
        simpa only [ofReal_mul, ofReal_ofNat] using apply_add_sq_apply_eq_of_pow_three h3 _
    rw [this, norm_real, Real.norm_eq_abs, abs_mul, abs_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hC k).trans (mul_rpow_le_abs_mul_rpow_max
      (Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le) le_rfl)) zero_le_two
  have hb : ∀ k, ‖a k‖ ≤ 2 := fun k ↦ (norm_add_le _ _).trans (by
    linarith [χ.norm_le_one (nthPrime k), (χ ^ 2).norm_le_one (nthPrime k)])
  refine not_forall_exists_differentiableOn_primePart_of_lt (X := {χ, χ ^ 2})
    (insert_nonempty _ _) (by simp [hχ, h21]) (m := 3) (by norm_num) (by simp [h3, h23])
    (le_max_right θ 0) hθ' fun j hj hj3 ↦ ⟨abelSeries a nthPrime,
      differentiableOn_abelSeries_of_le_rpow (le_max_right θ 0) ha (Nat.prime_nth_prime 0).pos
        nthPrime_strictMono, fun s hs ↦ ?_⟩
  have e : ∑' k, a k * (nthPrime k : ℂ) ^ (-s) = χ.primePart s + (χ ^ 2).primePart s := by
    rw [primePart, primePart, ← Summable.tsum_add (χ.summable_primeTerm hs)
      ((χ ^ 2).summable_primeTerm hs)]
    exact tsum_congr fun k ↦ by simp only [a, primeTerm]; ring
  have hθs : max θ 0 < s.re := hθ'.trans (by norm_num; linarith)
  rw [abelSeries_eq_tsum_of_le_rpow (le_max_right θ 0) ha hb (Nat.prime_nth_prime 0).pos
    nthPrime_strictMono hs hθs, e, sum_pair hne]
  interval_cases j
  · simp only [pow_one]
  · rw [h4, add_comm]

/-- **Characters of order 3: the real parts are not `O(n ^ θ)` for `θ < 1 / 3`.** For a
nonprincipal `χ` with `χ ^ 3 = 1` and `θ < 1 / 3`, there is no constant `C` with
`|∑_{k < n} re χ(pₖ)| ≤ C n ^ θ` for all `n`. -/
theorem not_exists_abs_sum_re_le_rpow_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {θ : ℝ}
    (hθ : θ < 1 / 3) :
    ¬ ∃ C : ℝ, ∀ n, |∑ k ∈ range n, (χ (nthPrime k)).re| ≤ C * (n : ℝ) ^ θ := by
  rintro ⟨C, hC⟩
  refine not_exists_abs_sum_succ_re_le_nthPrime_rpow_of_pow_three hχ h3
    (max_lt hθ (by norm_num : (0 : ℝ) < 1 / 3))
    ⟨|C|, fun k ↦ (hC (k + 1)).trans (mul_rpow_le_abs_mul_rpow_max (by simp) ?_)⟩
  exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)

/-- **Characters of order 3: quantitative oscillation.** For a nonprincipal `χ` with `χ ^ 3 = 1`
and `θ < 1 / 3`, the partial sums `∑_{k < n} χ(pₖ)` are not bounded by `C n ^ θ`. -/
theorem not_exists_norm_sum_le_rpow_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {θ : ℝ}
    (hθ : θ < 1 / 3) :
    ¬ ∃ C : ℝ, ∀ n, ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C * (n : ℝ) ^ θ := by
  rintro ⟨C, hC⟩
  exact not_exists_abs_sum_re_le_rpow_of_pow_three hχ h3 hθ
    ⟨C, fun n ↦ by simpa [re_sum] using (abs_re_le_norm _).trans (hC n)⟩

/-- **Characters of order 3: the real parts of the partial sums are unbounded.** For a
nonprincipal `χ` with `χ ^ 3 = 1`, the sums `∑_{k < n} re χ(pₖ)` are unbounded. This is the case
`θ = 0` of `not_exists_abs_sum_re_le_rpow_of_pow_three`. -/
theorem not_exists_abs_sum_re_le_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) :
    ¬ ∃ C : ℝ, ∀ n, |∑ k ∈ range n, (χ (nthPrime k)).re| ≤ C := by
  rintro ⟨C, hC⟩
  exact not_exists_abs_sum_re_le_rpow_of_pow_three hχ h3 (θ := 0) (by norm_num)
    ⟨C, fun n ↦ by simpa using hC n⟩

/-- **Characters of order 3: bounded partial sums are impossible.** For a nonprincipal `χ` with
`χ ^ 3 = 1`, the partial sums `∑_{k < n} χ(pₖ)` are unbounded. -/
theorem not_exists_norm_sum_le_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) :
    ¬ ∃ C : ℝ, ∀ n, ‖∑ k ∈ range n, χ (nthPrime k)‖ ≤ C := by
  rintro ⟨C, hC⟩
  exact not_exists_abs_sum_re_le_of_pow_three hχ h3
    ⟨C, fun n ↦ by simpa [re_sum] using (abs_re_le_norm _).trans (hC n)⟩

/-- **Characters of order 3, Landau form.** For a nonprincipal `χ` with `χ ^ 3 = 1` and
`θ < 1 / 3`, `∑_{k < n} χ(pₖ)` is not `O(n ^ θ)`. -/
theorem not_isBigO_rpow_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {θ : ℝ} (hθ : θ < 1 / 3) :
    ¬ (fun n : ℕ ↦ ∑ k ∈ range n, χ (nthPrime k)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ θ :=
  fun h ↦ not_exists_norm_sum_le_rpow_of_pow_three hχ h3 (max_lt hθ (by norm_num))
    (exists_forall_norm_le_rpow_of_isBigO (by simp) h)

/-- For a nonprincipal `χ` with `χ ^ 3 = 1` and every `ε > 0`, `∑_{k < n} χ(pₖ)` is not
`O(n ^ (1 / 3 - ε))`. -/
theorem not_isBigO_rpow_one_third_sub_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {ε : ℝ}
    (hε : 0 < ε) :
    ¬ (fun n : ℕ ↦ ∑ k ∈ range n, χ (nthPrime k)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 - ε) :=
  not_isBigO_rpow_of_pow_three hχ h3 (by linarith)

/-- For a nonprincipal `χ` with `χ ^ 3 = 1` and `θ < 1 / 3`, the real parts
`∑_{k < n} re χ(pₖ)` are not `O(n ^ θ)`. -/
theorem not_isBigO_sum_re_rpow_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {θ : ℝ}
    (hθ : θ < 1 / 3) :
    ¬ (fun n : ℕ ↦ ∑ k ∈ range n, (χ (nthPrime k)).re) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ θ :=
  fun h ↦ not_exists_abs_sum_re_le_rpow_of_pow_three hχ h3 (max_lt hθ (by norm_num))
    (exists_forall_norm_le_rpow_of_isBigO (by simp) h)

/-- **Characters of order 3, over the primes below `x`.** For a nonprincipal `χ` with
`χ ^ 3 = 1` and `θ < 1 / 3`, `∑_{p < x} χ(p)` is not bounded by `C x ^ θ`. -/
theorem not_exists_norm_sum_primesBelow_le_rpow_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1)
    {θ : ℝ} (hθ : θ < 1 / 3) :
    ¬ ∃ C : ℝ, ∀ x : ℕ, ‖∑ p ∈ Nat.primesBelow x, χ p‖ ≤ C * (x : ℝ) ^ θ := by
  rintro ⟨C, hC⟩
  refine not_exists_abs_sum_succ_re_le_nthPrime_rpow_of_pow_three hχ h3
    (max_lt hθ (by norm_num : (0 : ℝ) < 1 / 3)) ⟨|C| * 2 ^ max θ 0, fun k ↦ ?_⟩
  have hp : (1 : ℝ) ≤ nthPrime k := Nat.one_le_cast.2 (Nat.prime_nth_prime k).one_le
  have hcount : Nat.primeCounting' (nthPrime k + 1) = k + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k
  have h := hC (nthPrime k + 1)
  rw [χ.sum_primesBelow_eq, hcount] at h
  have hre : |∑ j ∈ range (k + 1), (χ (nthPrime j)).re| ≤
      ‖∑ j ∈ range (k + 1), χ (nthPrime j)‖ := by
    simpa [re_sum] using abs_re_le_norm (∑ j ∈ range (k + 1), χ (nthPrime j))
  refine hre.trans (h.trans ((mul_rpow_le_abs_mul_rpow_max (by push_cast; linarith)
    le_rfl).trans ?_))
  rw [mul_assoc, ← Real.mul_rpow (by norm_num) (by positivity)]
  gcongr
  push_cast
  linarith

/-- For a nonprincipal `χ` with `χ ^ 3 = 1` and `θ < 1 / 3`, `∑_{p < x} χ(p)` is not
`O(x ^ θ)`. -/
theorem not_isBigO_primesBelow_rpow_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {θ : ℝ}
    (hθ : θ < 1 / 3) :
    ¬ (fun x : ℕ ↦ ∑ p ∈ Nat.primesBelow x, χ p) =O[atTop] fun x : ℕ ↦ (x : ℝ) ^ θ :=
  fun h ↦ not_exists_norm_sum_primesBelow_le_rpow_of_pow_three hχ h3 (max_lt hθ (by norm_num))
    (exists_forall_norm_le_rpow_of_isBigO (by simp [Nat.primesBelow_zero]) h)

/-- **Characters of order 3: the values at the primes are not eventually periodic**, not even
their real parts. -/
theorem not_eventuallyPeriodic_re_apply_nthPrime (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {p : ℕ}
    (hp : 0 < p) : ¬ Function.EventuallyPeriodic (fun k ↦ (χ (nthPrime k)).re) p := by
  intro h
  obtain ⟨c, C, hC⟩ := h.exists_abs_sum_real_sub_mul_le hp
  by_cases hc : c = 0
  · exact not_exists_abs_sum_re_le_of_pow_three hχ h3 ⟨C, fun n ↦ by simpa [hc] using hC n⟩
  · exact χ.not_exists_abs_sum_re_sub_mul_le hχ ⟨c, hc, C, hC⟩

/-- If `χ ^ 3 = 1` and the digits `f (χ pₖ)` are eventually periodic, where `f` separates `1` from
the other cube roots of unity, then `k ↦ re χ(pₖ)` is eventually periodic with the same period:
eventually `χ(pₖ)` is a cube root of unity, and `re χ(pₖ)` is `1` or `-1 / 2` according to whether
`f (χ pₖ) = f 1`. -/
theorem eventuallyPeriodic_re_apply_nthPrime (h3 : χ ^ 3 = 1) {f : ℂ → ℕ}
    (hf : ∀ z : ℂ, z ^ 3 = 1 → f z = f 1 → z = 1) {p : ℕ}
    (h : Function.EventuallyPeriodic (fun k ↦ f (χ (nthPrime k))) p) :
    Function.EventuallyPeriodic (fun k ↦ (χ (nthPrime k)).re) p := by
  have hv : ∀ᶠ k in atTop,
      (χ (nthPrime k)).re = if f (χ (nthPrime k)) = f 1 then 1 else -1 / 2 :=
    χ.eventually_apply_nthPrime_ne_zero.mono fun k hk ↦ by
      have hu : IsUnit ((nthPrime k : ℕ) : ZMod q) := by
        by_contra hu
        exact hk (χ.map_nonunit hu)
      have h1 := χ.apply_pow_eq_one_of_isUnit h3 hu
      split_ifs with he
      · rw [hf _ h1 he, one_re]
      · exact re_eq_of_pow_three_eq_one h1 fun h ↦ he (by rw [h])
  filter_upwards [h, hv, (tendsto_add_atTop_nat p).eventually hv] with k hk h₁ h₂
  rw [h₁, h₂, hk]

/-- **Irrationality from a character of order 3.** For a nonprincipal `χ` with `χ ^ 3 = 1`, a base
`b ≥ 2` and digits `f (χ pₖ) < b` such that `f z ≠ f 1` for the cube roots of unity `z ≠ 1`, the
number `∑ₖ f (χ pₖ) / b ^ (k + 1)` is irrational. -/
theorem irrational_tsum_of_pow_three (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {b : ℕ} (hb : 2 ≤ b)
    {f : ℂ → ℕ} (hfb : ∀ z, f z < b) (hf : ∀ z : ℂ, z ^ 3 = 1 → f z = f 1 → z = 1) :
    Irrational (∑' k : ℕ, (f (χ (nthPrime k)) : ℝ) / b ^ (k + 1)) :=
  irrational_tsum_div_pow hb (fun _ ↦ hfb _) fun _ hp hper ↦
    not_eventuallyPeriodic_re_apply_nthPrime hχ h3 hp
      (eventuallyPeriodic_re_apply_nthPrime h3 hf hper)

/-- **Cubic residue constants are irrational** (digits injective on the cube roots of unity). For
a nonprincipal `χ` with `χ ^ 3 = 1` and digits `f (χ pₖ) < b` that distinguish the three cube
roots of unity, `∑ₖ f (χ pₖ) / b ^ (k + 1)` is irrational. -/
theorem irrational_tsum_of_pow_three' (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {b : ℕ} (hb : 2 ≤ b)
    {f : ℂ → ℕ} (hfb : ∀ z, f z < b)
    (hf : ∀ z w : ℂ, z ^ 3 = 1 → w ^ 3 = 1 → f z = f w → z = w) :
    Irrational (∑' k : ℕ, (f (χ (nthPrime k)) : ℝ) / b ^ (k + 1)) :=
  irrational_tsum_of_pow_three hχ h3 hb hfb fun z hz h ↦ hf z 1 hz (one_pow 3) h

end Cubic

section CubicResidue

/-- For a prime `ℓ ≡ 1 (mod 3)` there is a nonprincipal Dirichlet character `χ` modulo `ℓ` with
`χ ^ 3 = 1`, a *cubic residue character*. -/
theorem exists_ne_one_pow_three_eq_one (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ % 3 = 1) :
    ∃ χ : DirichletCharacter ℂ ℓ, χ ≠ 1 ∧ χ ^ 3 = 1 := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod ℓ) (R := ℂ) (n := 3)
    (by rw [ZMod.card]; omega) (Complex.isPrimitiveRoot_exp 3 (by norm_num))
  refine ⟨χ, fun h1 ↦ ?_, hχ ▸ pow_orderOf_eq_one χ⟩
  rw [h1, orderOf_one] at hχ
  norm_num at hχ

/-- For a nonprincipal `χ` modulo a prime `ℓ` with `χ ^ 3 = 1`, a nonzero `a` has `χ(a) = 1` if
and only if `a` is a cube modulo `ℓ`. -/
theorem apply_eq_one_iff_exists_pow_three {ℓ : ℕ} [Fact ℓ.Prime] {χ : DirichletCharacter ℂ ℓ}
    (hχ : χ ≠ 1) (h3 : χ ^ 3 = 1) {a : ZMod ℓ} (ha : a ≠ 0) :
    χ a = 1 ↔ ∃ x : ZMod ℓ, x ^ 3 = a := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (ZMod ℓ)ˣ)
    have hpow (n : ℕ) : χ ((g ^ n : (ZMod ℓ)ˣ) : ZMod ℓ) = χ (g : ZMod ℓ) ^ n := by
      rw [Units.val_pow_eq_pow_val, map_pow]
    have hg1 : χ (g : ZMod ℓ) ≠ 1 := by
      intro hg1
      refine hχ (MulChar.ext fun u ↦ ?_)
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hg u)
      rw [hpow, hg1, one_pow, MulChar.one_apply_coe]
    have hg3 : χ (g : ZMod ℓ) ^ 3 = 1 := χ.apply_pow_eq_one_of_isUnit h3 g.isUnit
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 (hg (Units.mk0 a ha))
    have hgn : χ (g : ZMod ℓ) ^ n = 1 := by rw [← hpow, hn, Units.val_mk0, h]
    have hr : χ (g : ZMod ℓ) ^ (n % 3) = 1 := by
      rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hg3, one_pow, mul_one] at hgn
      exact hgn
    have h0 : n % 3 = 0 := by
      have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases hm : n % 3
      · rfl
      · exact absurd (by simpa using hr) hg1
      · exact absurd (by rw [pow_succ, hr, one_mul] at hg3; exact hg3) hg1
    refine ⟨((g ^ (n / 3) : (ZMod ℓ)ˣ) : ZMod ℓ), ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h0),
      hn, Units.val_mk0]
  · rintro ⟨x, rfl⟩
    have hx : IsUnit x := isUnit_iff_ne_zero.2 fun h ↦ ha (by rw [h]; norm_num)
    rw [map_pow]
    exact χ.apply_pow_eq_one_of_isUnit h3 hx

end CubicResidue

end DirichletCharacter

namespace Real

open Classical in
/-- The **cubic residue constant** of a prime `ℓ` in base `b`: the number whose `k`-th base-`b`
digit is `1` if the `k`-th prime `pₖ` is a nonzero cube modulo `ℓ`, and `0` otherwise. For
`ℓ ≡ 1 (mod 3)` the cubes form a subgroup of index `3` in `(ZMod ℓ)ˣ`; for `ℓ ≢ 1 (mod 3)` every
residue is a cube and the constant is rational. -/
noncomputable def cubicResidueConstant (ℓ b : ℕ) : ℝ :=
  ∑' k : ℕ, (if (nthPrime k : ZMod ℓ) ≠ 0 ∧ ∃ x : ZMod ℓ, x ^ 3 = nthPrime k then (1 : ℝ) else 0) /
    b ^ (k + 1)

/-- **Cubic residue constants are irrational** for every prime `ℓ ≡ 1 (mod 3)` and every base
`b ≥ 2`. -/
theorem irrational_cubicResidueConstant (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ % 3 = 1) {b : ℕ}
    (hb : 2 ≤ b) : Irrational (cubicResidueConstant ℓ b) := by
  classical
  obtain ⟨χ, hχ, h3⟩ := DirichletCharacter.exists_ne_one_pow_three_eq_one ℓ hℓ
  have h := DirichletCharacter.irrational_tsum_of_pow_three hχ h3 hb
    (f := fun z ↦ if z = 1 then 1 else 0) (fun z ↦ by split_ifs <;> omega)
    (fun z _ h ↦ by by_contra hz; simp [hz] at h)
  have e : cubicResidueConstant ℓ b =
      ∑' k : ℕ, ((if χ (nthPrime k) = 1 then 1 else 0 : ℕ) : ℝ) / b ^ (k + 1) := by
    unfold cubicResidueConstant
    refine tsum_congr fun k ↦ ?_
    congr 1
    by_cases hp : ((nthPrime k : ℕ) : ZMod ℓ) = 0
    · simp [hp, MulChar.map_zero]
    · rw [← DirichletCharacter.apply_eq_one_iff_exists_pow_three hχ h3 hp]
      split_ifs <;> simp_all
  rw [e]
  exact h

end Real
