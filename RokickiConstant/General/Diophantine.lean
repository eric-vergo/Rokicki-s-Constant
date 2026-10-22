/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import RokickiConstant.Defs

/-!
# Dyadic approximations to Rokicki's constant

A rational number `a / q` close to a binary expansion `x = ∑ₖ d k / 2 ^ (k + 1)` forces the digits
of `x` to repeat the eventually periodic digits of `a / q` over a long stretch. For dyadic
denominators `q = 2 ^ m` the stretch is a run of equal digits. This file proves both directions
of that dictionary for general binary digit sequences, and then bounds the dyadic approximations
of Rokicki's constant `ρ` conditionally on Breusch's Bertrand postulate for primes `≡ 1, 3 (mod 4)`:
a run of equal digits of `ρ` is a string of consecutive primes in one class modulo `4`, and
Breusch's theorem bounds its length by the number of primes in `(p, 2p]`.

## Main definitions

* `RokickiConstant.BreuschFour`: Breusch's theorem (1932) that for every `x ≥ 7` both classes
  `1` and `3` modulo `4` contain a prime in `(x, 2x]`, stated as a hypothesis.

## Main statements

* `one_div_two_pow_le_abs_tsum_sub_div_two_pow`: if `d m ≠ d (m + k)`, then
  `|x - a / 2 ^ m| ≥ 1 / 2 ^ (m + k + 1)` for every integer `a`.
* `exists_abs_tsum_sub_div_le_of_periodic`: conversely, a `P`-periodic stretch of excess `E`
  starting at `n` gives a rational `a / (2 ^ n (2 ^ P - 1))` within
  `1 / (2 ^ (n + E) (2 ^ P - 1))` of `x`.
* `Nat.primeCounting_two_mul_le`: `π (2 x) ≤ 28 π x` for `x ≥ 6`, from Mathlib's Chebyshev
  bounds.
* `RokickiConstant.exists_rokickiDigit_ne_of_breuschFour`: under Breusch's theorem, the run of
  equal digits of `ρ` starting at index `n` ends after at most `π (2 pₙ₊₂) - π pₙ₊₂` digits.
* `RokickiConstant.one_div_two_pow_le_abs_rokickiConstant_sub_of_breuschFour`: under Breusch's
  theorem, `|ρ - a / 2 ^ m| ≥ 1 / 2 ^ (28 m + 55)`; in particular
  `|ρ - a / 2 ^ m| ≥ (2 ^ m) ^ (-83)` for `m ≥ 1`
  (`RokickiConstant.one_div_two_pow_pow_le_abs_rokickiConstant_sub_of_breuschFour`), so `ρ`
  has no dyadic approximations of Liouville type.

## References

* R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates, daß zwischen x und 2x stets
  Primzahlen liegen*, Math. Z. 34 (1932), 505–526.

## Tags

Rokicki's constant, Diophantine approximation, dyadic rationals, Bertrand's postulate,
primes in arithmetic progressions
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Finset

section BinaryTail

variable {d : ℕ → ℕ}

/-- A digit `1` at position `n + j` contributes at least `1 / 2 ^ (j + 1)` to the tail at `n`. -/
theorem one_div_two_pow_le_binaryTail (hd : ∀ k, d k ≤ 1) {n j : ℕ} (h : d (n + j) = 1) :
    1 / 2 ^ (j + 1) ≤ binaryTail d n := by
  have := (summable_binaryTail hd n).le_tsum j fun _ _ ↦ by positivity
  rwa [h, Nat.cast_one] at this

/-- The tails of `d` and of the complementary digits `1 - d` add up to `1`. -/
theorem binaryTail_add_binaryTail_one_sub (hd : ∀ k, d k ≤ 1) (n : ℕ) :
    binaryTail d n + binaryTail (fun k ↦ 1 - d k) n = 1 := by
  have hd' : ∀ k, (fun k ↦ 1 - d k) k ≤ 1 := fun k ↦ Nat.sub_le 1 (d k)
  rw [binaryTail, binaryTail, ← (summable_binaryTail hd n).tsum_add (summable_binaryTail hd' n),
    ← tsum_geometric_two' 1]
  refine tsum_congr fun k ↦ ?_
  rw [Nat.cast_sub (hd (n + k)), Nat.cast_one, pow_succ]
  ring

/-- A digit `0` at position `n + j` keeps the tail at `n` at least `1 / 2 ^ (j + 1)` below `1`. -/
theorem binaryTail_le_one_sub_one_div_two_pow (hd : ∀ k, d k ≤ 1) {n j : ℕ}
    (h : d (n + j) = 0) : binaryTail d n ≤ 1 - 1 / 2 ^ (j + 1) := by
  have := one_div_two_pow_le_binaryTail (d := fun k ↦ 1 - d k) (fun k ↦ Nat.sub_le 1 (d k))
    (n := n) (j := j) (by simp [h])
  linarith [binaryTail_add_binaryTail_one_sub hd n]

/-- If the digits `d m` and `d (m + k)` differ, the tail at `m` lies in
`[1 / 2 ^ (k + 1), 1 - 1 / 2 ^ (k + 1)]`. -/
theorem binaryTail_mem_Icc_of_ne (hd : ∀ k, d k ≤ 1) {m k : ℕ} (hk : d (m + k) ≠ d m) :
    binaryTail d m ∈ Set.Icc (1 / 2 ^ (k + 1)) (1 - 1 / 2 ^ (k + 1)) := by
  have hle : (1 : ℝ) / 2 ^ (k + 1) ≤ 1 / 2 ^ (0 + 1) :=
    one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)
  rcases (by have := hd m; have := hd (m + k); omega :
      d m = 0 ∧ d (m + k) = 1 ∨ d m = 1 ∧ d (m + k) = 0) with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · refine ⟨one_div_two_pow_le_binaryTail hd h1, ?_⟩
    linarith [binaryTail_le_one_sub_one_div_two_pow hd (n := m) (j := 0) (by simpa using h0)]
  · refine ⟨?_, binaryTail_le_one_sub_one_div_two_pow hd h0⟩
    linarith [one_div_two_pow_le_binaryTail hd (n := m) (j := 0) (by simpa using h1)]

/-- `2 ^ n · x` is an integer plus the tail at `n`. -/
theorem exists_two_pow_mul_tsum_sub_binaryTail_eq_intCast (hd : ∀ k, d k ≤ 1) (n : ℕ) :
    ∃ N : ℤ, 2 ^ n * (∑' i, (d i : ℝ) / 2 ^ (i + 1)) - binaryTail d n = N :=
  ⟨∑ i ∈ range n, (d i : ℤ) * 2 ^ (n - 1 - i), by
    rw [two_pow_mul_tsum_sub_binaryTail hd]
    push_cast
    rfl⟩

/-- **Non-constant blocks separate a binary expansion from the dyadic rationals.** If the digits
`d m` and `d (m + k)` of `x = ∑ᵢ d i / 2 ^ (i + 1)` differ, then `x` is at distance at least
`1 / 2 ^ (m + k + 1)` from every dyadic rational `a / 2 ^ m`. Contrapositively, an approximation
`|x - a / 2 ^ m| < 1 / 2 ^ (m + L)` forces the `L` digits `d m, …, d (m + L - 1)` to be equal. -/
theorem one_div_two_pow_le_abs_tsum_sub_div_two_pow (hd : ∀ k, d k ≤ 1) {m k : ℕ}
    (hk : d (m + k) ≠ d m) (a : ℤ) :
    1 / 2 ^ (m + k + 1) ≤ |∑' i, (d i : ℝ) / 2 ^ (i + 1) - a / 2 ^ m| := by
  obtain ⟨N, hN⟩ := exists_two_pow_mul_tsum_sub_binaryTail_eq_intCast hd m
  have hT := binaryTail_mem_Icc_of_ne hd hk
  set x := ∑' i, (d i : ℝ) / 2 ^ (i + 1)
  set T := binaryTail d m
  have hpos : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
  have key : 1 / 2 ^ (k + 1) ≤ |((N - a : ℤ) : ℝ) + T| := by
    rcases le_or_gt 0 (N - a) with h | h
    · have : (0 : ℝ) ≤ ((N - a : ℤ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith [hT.1])]
      linarith [hT.1]
    · have : ((N - a : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : N - a ≤ -1)
      rw [abs_of_neg (by linarith [hT.2])]
      linarith [hT.2]
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hx : x - a / 2 ^ m = (((N - a : ℤ) : ℝ) + T) / 2 ^ m := by
    rw [eq_div_iff h2.ne', sub_mul, div_mul_cancel₀ _ h2.ne']
    push_cast
    linarith
  rw [hx, abs_div, abs_of_pos h2, show (2 : ℝ) ^ (m + k + 1) = 2 ^ (k + 1) * 2 ^ m by ring,
    ← div_div]
  gcongr

/-- Two tails `P` positions apart whose first `E` digits agree are within `1 / 2 ^ E`. -/
theorem abs_binaryTail_sub_binaryTail_add_le (hd : ∀ k, d k ≤ 1) {P E : ℕ} :
    ∀ {n : ℕ}, (∀ i < E, d (n + i + P) = d (n + i)) →
      |binaryTail d n - binaryTail d (n + P)| ≤ 1 / 2 ^ E := by
  induction E with
  | zero =>
    intro n _
    have h1 := binaryTail_mem_Icc hd n
    have h2 := binaryTail_mem_Icc hd (n + P)
    rw [pow_zero, div_one, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  | succ E ih =>
    intro n h
    have h0 : d (n + P) = d n := by simpa using h 0 (by omega)
    have h' : ∀ i < E, d (n + 1 + i + P) = d (n + 1 + i) := fun i hi ↦ by
      simpa [add_assoc, add_comm 1 i] using h (i + 1) (by omega)
    have hn := binaryTail_succ hd n
    have hnP := binaryTail_succ hd (n + P)
    rw [show n + P + 1 = n + 1 + P by omega, h0] at hnP
    have : binaryTail d n - binaryTail d (n + P) =
        (binaryTail d (n + 1) - binaryTail d (n + 1 + P)) / 2 := by
      linarith
    rw [this, abs_div, abs_two, pow_succ, ← div_div]
    gcongr
    exact ih h'

/-- **Periodic stretches give rational approximations.** If the digits of
`x = ∑ᵢ d i / 2 ^ (i + 1)` satisfy `d (n + i + P) = d (n + i)` for `i < E` (a `P`-periodic stretch
of length `P + E` starting at `n`), then `x` is within `1 / (2 ^ (n + E) (2 ^ P - 1))` of a
rational number with denominator `2 ^ n (2 ^ P - 1)`. -/
theorem exists_abs_tsum_sub_div_le_of_periodic (hd : ∀ k, d k ≤ 1) {n P E : ℕ} (hP : 0 < P)
    (h : ∀ i < E, d (n + i + P) = d (n + i)) :
    ∃ a : ℤ, |∑' i, (d i : ℝ) / 2 ^ (i + 1) - a / (2 ^ n * (2 ^ P - 1))| ≤
      1 / (2 ^ (n + E) * (2 ^ P - 1)) := by
  obtain ⟨N₁, h₁⟩ := exists_two_pow_mul_tsum_sub_binaryTail_eq_intCast hd n
  obtain ⟨N₂, h₂⟩ := exists_two_pow_mul_tsum_sub_binaryTail_eq_intCast hd (n + P)
  have hT := abs_binaryTail_sub_binaryTail_add_le hd h
  set x := ∑' i, (d i : ℝ) / 2 ^ (i + 1)
  have hP' : (1 : ℝ) < 2 ^ P := one_lt_pow₀ (by norm_num) hP.ne'
  have hQ : (0 : ℝ) < 2 ^ n * (2 ^ P - 1) := mul_pos (by positivity) (by linarith)
  refine ⟨N₂ - N₁, ?_⟩
  have e : 2 ^ n * (2 ^ P - 1) * x - ((N₂ - N₁ : ℤ) : ℝ) =
      binaryTail d (n + P) - binaryTail d n := by
    push_cast
    rw [pow_add] at h₂
    linear_combination h₂ - h₁
  have hx : x - ((N₂ - N₁ : ℤ) : ℝ) / (2 ^ n * (2 ^ P - 1)) =
      (2 ^ n * (2 ^ P - 1) * x - ((N₂ - N₁ : ℤ) : ℝ)) / (2 ^ n * (2 ^ P - 1)) := by
    rw [sub_div, mul_div_cancel_left₀ x hQ.ne']
  rw [hx, e, abs_div, abs_of_pos hQ, abs_sub_comm,
    show (1 : ℝ) / (2 ^ (n + E) * (2 ^ P - 1)) = 1 / 2 ^ E / (2 ^ n * (2 ^ P - 1)) by
      rw [div_div, pow_add]
      ring]
  gcongr

end BinaryTail

namespace Nat

/-- `(n + 1) ^ 2 ≤ 2 ^ n` for `n ≥ 6`. -/
private theorem sq_succ_le_two_pow {n : ℕ} (hn : 6 ≤ n) : (n + 1) ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show 2 ^ (n + 1) = 2 * 2 ^ n by ring]
    nlinarith

/-- **A Chebyshev-type doubling bound**: `π (2 x) ≤ 28 π x` for `x ≥ 6`. It follows from
Mathlib's explicit bounds `π y ≤ log 4 · y / log √y + √y` (`Chebyshev.pi_le_log4_mul_div`) and
`π x ≥ (x log 2 - log (x + 1)) / log x` (`Chebyshev.pi_ge`); the constant is not optimized
(the prime number theorem gives `π (2 x) / π x → 2`). -/
theorem primeCounting_two_mul_le {x : ℕ} (hx : 6 ≤ x) :
    primeCounting (2 * x) ≤ 28 * primeCounting x := by
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hy1 : (1 : ℝ) < ((2 * x : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 * x)
  set y : ℝ := ((2 * x : ℕ) : ℝ) with hy
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hc : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- the upper bound: `π (2 x) · log y ≤ (4 log 2 + 2) y`
  have hU := Chebyshev.pi_le_log4_mul_div hy1
  rw [floor_natCast, Real.log_sqrt (by positivity)] at hU
  have hs : √y * Real.log y ≤ 2 * y := by
    have h1 : Real.log y = 2 * Real.log √y := by rw [Real.log_sqrt (by positivity)]; ring
    have h2 : Real.log √y ≤ √y - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
    have h3 : √y * √y = y := Real.mul_self_sqrt (by linarith)
    have h4 : 0 ≤ √y := Real.sqrt_nonneg y
    nlinarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hU' : (primeCounting (2 * x) : ℝ) * Real.log y ≤ (4 * Real.log 2 + 2) * y := by
    have h := mul_le_mul_of_nonneg_right hU hly.le
    have e : Real.log 4 * y / (Real.log y / 2) * Real.log y = 2 * Real.log 4 * y := by
      field_simp
    rw [add_mul, e, hlog4] at h
    linarith
  have hxy : Real.log x ≤ Real.log y :=
    Real.log_le_log (by linarith) (by rw [hy]; push_cast; linarith)
  have hA : (primeCounting (2 * x) : ℝ) * Real.log x ≤ (8 * Real.log 2 + 4) * x := by
    have h3 : (4 * Real.log 2 + 2) * y = (8 * Real.log 2 + 4) * x := by
      rw [hy]
      push_cast
      ring
    linarith [mul_le_mul_of_nonneg_left hxy (by positivity : (0 : ℝ) ≤ primeCounting (2 * x))]
  -- the lower bound: `x log 2 ≤ 2 π x · log x`
  have hL := Chebyshev.pi_ge x
  rw [div_le_iff₀ hl] at hL
  have hsq : 2 * Real.log ((x : ℝ) + 1) ≤ x * Real.log 2 := by
    have := Real.log_le_log (by positivity) (by exact_mod_cast sq_succ_le_two_pow hx :
      (((x : ℝ) + 1) ^ 2) ≤ (2 : ℝ) ^ x)
    rwa [Real.log_pow, Real.log_pow] at this
  have hB : (x : ℝ) * Real.log 2 ≤ 2 * (primeCounting x * Real.log x) := by linarith
  -- combine: `π (2 x) · log x · log 2 ≤ 28 π x · log x · log 2`
  have hA0 : (0 : ℝ) ≤ primeCounting (2 * x) := by positivity
  have hB0 : (0 : ℝ) ≤ primeCounting x * Real.log x := by positivity
  have key : (primeCounting (2 * x) : ℝ) * (Real.log x * Real.log 2) ≤
      28 * primeCounting x * (Real.log x * Real.log 2) := by
    have e1 : (primeCounting (2 * x) : ℝ) * Real.log x * Real.log 2 ≤
        (8 * Real.log 2 + 4) * (x * Real.log 2) := by
      nlinarith
    have e2 : (8 * Real.log 2 + 4) * (x * Real.log 2) ≤
        (8 * Real.log 2 + 4) * (2 * (primeCounting x * Real.log x)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    nlinarith
  exact_mod_cast le_of_mul_le_mul_right key (mul_pos hl (by linarith))

end Nat

namespace RokickiConstant

open Real

/-- **Breusch's theorem** (R. Breusch, Math. Z. 34 (1932)), Bertrand's postulate for the primes
`≡ 1` and `≡ 3 (mod 4)`: for every `x ≥ 7` each of the two classes contains a prime in
`(x, 2x]`. It is stated here as a hypothesis since Mathlib has Bertrand's postulate
(`Nat.exists_prime_lt_and_le_two_mul`) but not its versions in arithmetic progressions. -/
def BreuschFour : Prop :=
  ∀ x : ℕ, 7 ≤ x → (∃ p, p.Prime ∧ p % 4 = 3 ∧ x < p ∧ p ≤ 2 * x) ∧
    (∃ p, p.Prime ∧ p % 4 = 1 ∧ x < p ∧ p ≤ 2 * x)

/-- The odd prime `pₙ₊₂ = oddPrime n` is the `(n + 2)`-nd prime: `π pₙ₊₂ = n + 2`. -/
theorem primeCounting_oddPrime (n : ℕ) : Nat.primeCounting (oddPrime n) = n + 2 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_succ,
    ← Nat.primeCounting', oddPrime, Nat.primeCounting'_nth_eq]
  simp [Nat.prime_nth_prime]

/-- A prime `p` larger than `oddPrime n` is `oddPrime (n + k)` for some `k ≥ 1`, and `k` is the
number of primes in `(oddPrime n, p]`. -/
theorem exists_oddPrime_add_eq {n p : ℕ} (hp : p.Prime) (h : oddPrime n < p) :
    ∃ k, 0 < k ∧ oddPrime (n + k) = p ∧
      k + Nat.primeCounting (oddPrime n) = Nat.primeCounting p := by
  have hc : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  have hlt : n + 1 < Nat.count Nat.Prime p := by
    rw [oddPrime, ← hc] at h
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).lt_iff_lt.mp h
  refine ⟨Nat.count Nat.Prime p - (n + 1), by omega, ?_, ?_⟩
  · rw [oddPrime, show n + (Nat.count Nat.Prime p - (n + 1)) + 1 = Nat.count Nat.Prime p by
      omega, hc]
  · rw [primeCounting_oddPrime, Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting',
      Nat.count_succ]
    simp only [hp, ↓reduceIte]
    omega

/-- The digit of `ρ` at index `n` is determined by the class of `oddPrime n` modulo `4`. -/
theorem rokickiDigit_ne_of_mod_four_ne {i j : ℕ} (h : oddPrime i % 4 ≠ oddPrime j % 4) :
    rokickiDigit i ≠ rokickiDigit j := by
  have hi := oddPrime_mod_four i
  have hj := oddPrime_mod_four j
  simp only [oddPrime] at hi hj h
  simp only [rokickiDigit]
  split_ifs <;> omega

/-- A prime of the other class modulo `4` in `(oddPrime n, 2 oddPrime n]` ends the run of equal
digits of `ρ` starting at `n` within `π (2 pₙ₊₂) - π pₙ₊₂` digits. -/
theorem exists_rokickiDigit_ne_of_prime {n p : ℕ} (hp : p.Prime) (h₁ : oddPrime n < p)
    (h₂ : p ≤ 2 * oddPrime n) (h₄ : p % 4 ≠ oddPrime n % 4) :
    ∃ k, 0 < k ∧ k ≤ Nat.primeCounting (2 * oddPrime n) - Nat.primeCounting (oddPrime n) ∧
      rokickiDigit (n + k) ≠ rokickiDigit n := by
  obtain ⟨k, hk, hkp, hπ⟩ := exists_oddPrime_add_eq hp h₁
  refine ⟨k, hk, ?_, rokickiDigit_ne_of_mod_four_ne (by rwa [hkp])⟩
  have := Nat.monotone_primeCounting h₂
  omega

/-- **Runs of congruent primes, conditionally on Breusch.** If Breusch's theorem holds, the run
of equal digits of `ρ` starting at index `n` (a string of consecutive primes `pₙ₊₂, pₙ₊₃, …` in
one class modulo `4`) ends within `π (2 pₙ₊₂) - π pₙ₊₂` digits. -/
theorem exists_rokickiDigit_ne_of_breuschFour (hB : BreuschFour) (n : ℕ) :
    ∃ k, 0 < k ∧ k ≤ Nat.primeCounting (2 * oddPrime n) - Nat.primeCounting (oddPrime n) ∧
      rokickiDigit (n + k) ≠ rokickiDigit n := by
  have h0 : oddPrime 0 = 3 := oddPrime_zero
  have h1 : oddPrime 1 = 5 := Nat.nth_prime_two_eq_five
  have h2 : oddPrime 2 = 7 := Nat.nth_prime_three_eq_seven
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
  · exact exists_rokickiDigit_ne_of_prime Nat.prime_five (by omega) (by omega) (by omega)
  · exact exists_rokickiDigit_ne_of_prime Nat.prime_seven (by omega) (by omega) (by omega)
  have h7 : 7 ≤ oddPrime n := h2 ▸ oddPrime_strictMono.monotone hn
  obtain ⟨⟨p₃, hp₃, h₃, hl₃, hu₃⟩, ⟨p₁, hp₁, h₁, hl₁, hu₁⟩⟩ := hB _ h7
  rcases oddPrime_mod_four n with h | h
  · exact exists_rokickiDigit_ne_of_prime hp₃ hl₃ hu₃ (by omega)
  · exact exists_rokickiDigit_ne_of_prime hp₁ hl₁ hu₁ (by omega)

/-- Under Breusch's theorem, every run of equal digits of `ρ` starting at index `n` has length at
most `27 (n + 2)`: by `Nat.primeCounting_two_mul_le`, `π (2 pₙ₊₂) - π pₙ₊₂ ≤ 27 π pₙ₊₂`. -/
theorem exists_rokickiDigit_ne_le_of_breuschFour (hB : BreuschFour) (n : ℕ) :
    ∃ k, 0 < k ∧ k ≤ 27 * (n + 2) ∧ rokickiDigit (n + k) ≠ rokickiDigit n := by
  have h0 : oddPrime 0 = 3 := oddPrime_zero
  have h1 : oddPrime 1 = 5 := Nat.nth_prime_two_eq_five
  have h2 : oddPrime 2 = 7 := Nat.nth_prime_three_eq_seven
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
  · exact ⟨1, one_pos, by omega, rokickiDigit_ne_of_mod_four_ne (by rw [h1, h0]; omega)⟩
  · exact ⟨1, one_pos, by omega, rokickiDigit_ne_of_mod_four_ne (by rw [h2, h1]; omega)⟩
  have h7 : 7 ≤ oddPrime n := h2 ▸ oddPrime_strictMono.monotone hn
  obtain ⟨k, hk, hkB, hne⟩ := exists_rokickiDigit_ne_of_breuschFour hB n
  have := Nat.primeCounting_two_mul_le (by omega : 6 ≤ oddPrime n)
  rw [primeCounting_oddPrime] at this hkB
  exact ⟨k, hk, by omega, hne⟩

/-- **Dyadic approximations to `ρ`, conditionally on Breusch, in terms of `π`.** If Breusch's
theorem holds, then for every `m` and every integer `a`,
`|ρ - a / 2 ^ m| ≥ 1 / 2 ^ (m + (π (2 pₘ₊₂) - π pₘ₊₂) + 1)`. -/
theorem one_div_two_pow_le_abs_rokickiConstant_sub_of_breuschFour' (hB : BreuschFour) (m : ℕ)
    (a : ℤ) :
    1 / 2 ^ (m + (Nat.primeCounting (2 * oddPrime m) - Nat.primeCounting (oddPrime m)) + 1) ≤
      |ρ - a / 2 ^ m| := by
  obtain ⟨k, -, hkB, hne⟩ := exists_rokickiDigit_ne_of_breuschFour hB m
  refine le_trans ?_ (one_div_two_pow_le_abs_tsum_sub_div_two_pow rokickiDigit_le_one hne a)
  exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)

/-- **Dyadic approximations to `ρ`, conditionally on Breusch.** If Breusch's theorem holds, then
`|ρ - a / 2 ^ m| ≥ 1 / 2 ^ (28 m + 55)` for every `m` and every integer `a`. -/
theorem one_div_two_pow_le_abs_rokickiConstant_sub_of_breuschFour (hB : BreuschFour) (m : ℕ)
    (a : ℤ) : 1 / 2 ^ (28 * m + 55) ≤ |ρ - a / 2 ^ m| := by
  obtain ⟨k, -, hk, hne⟩ := exists_rokickiDigit_ne_le_of_breuschFour hB m
  refine le_trans ?_ (one_div_two_pow_le_abs_tsum_sub_div_two_pow rokickiDigit_le_one hne a)
  exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)

/-- **`ρ` has no dyadic approximations of Liouville type, conditionally on Breusch.** If
Breusch's theorem holds, then `|ρ - a / 2 ^ m| ≥ 1 / (2 ^ m) ^ 83` for all `m ≥ 1` and all
integers `a`: the irrationality exponent of `ρ` restricted to the denominators `2 ^ m` is at
most `83` (and at most `28` asymptotically, by the same proof). -/
theorem one_div_two_pow_pow_le_abs_rokickiConstant_sub_of_breuschFour (hB : BreuschFour)
    {m : ℕ} (hm : 1 ≤ m) (a : ℤ) : 1 / ((2 : ℝ) ^ m) ^ 83 ≤ |ρ - a / 2 ^ m| := by
  refine le_trans ?_ (one_div_two_pow_le_abs_rokickiConstant_sub_of_breuschFour hB m a)
  rw [← pow_mul]
  exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)

end RokickiConstant
