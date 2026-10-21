/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.PrimeCounting
import RokickiConstant.BinaryExpansion

/-!
# Rokicki's constant

Let `3 = p₂ < p₃ < p₄ < ⋯` be the odd primes in increasing order (so `p₁ = 2`). **Rokicki's
constant** is the real number
$$
  ρ = \sum_{k ≥ 2} \frac{[p_k ≡ 3 \pmod 4]}{2^{k-1}} = 0.70040013796579773…,
$$
whose binary expansion `0.1011001101…` records, prime by prime, whether `pₖ ≡ 3 (mod 4)`.
The sequence OEIS A362583 lists the integers `aₙ` with binary digits `[p₂ ≡ 3], …, [pₙ ≡ 3]`;
Tom Rokicki observed that `aₙ / 2 ^ (n - 1)` converges, and `ρ` is its limit.

## Main definitions

* `Real.rokickiDigit k`: the `k`-th binary digit of `ρ` (indexed from `0`), namely `1` if the
  odd prime `Nat.nth Nat.Prime (k + 1)` is `3` modulo `4` and `0` otherwise.
* `Real.rokickiConstant`: Rokicki's constant `ρ = ∑ₖ rokickiDigit k / 2 ^ (k + 1)`, with scoped
  notation `ρ` in the `RokickiConstant` namespace.
* `Real.oeisA362583 n`: the integer with binary digits `rokickiDigit 0, …, rokickiDigit (n - 1)`,
  that is, the term `A362583 (n + 1)` of the OEIS sequence.
* `RokickiConstant.oddPrime k`: the `k`-th odd prime `pₖ₊₂`, counting from `oddPrime 0 = 3`.

## Main statements

* `Real.rokickiConstant_mem_Icc`: `0 ≤ ρ ≤ 1`.
* `Real.tendsto_oeisA362583_div_two_pow`: `A362583 n / 2 ^ (n - 1) → ρ`.
* `RokickiConstant.χ₄_oddPrime`: the `k`-th digit is encoded by the value of the nontrivial
  Dirichlet character modulo `4` at the corresponding odd prime, `χ₄ pₖ₊₂ = 1 - 2 · rokickiDigit k`.

The irrationality of `ρ` is proved in `RokickiConstant.Irrational`.

## References

* OEIS A362583, <https://oeis.org/A362583>

## Tags

Rokicki's constant, primes modulo 4, binary expansion, irrational
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology

namespace Real

/-- The `k`-th binary digit (indexed from `k = 0`) of Rokicki's constant: `1` if the odd prime
`Nat.nth Nat.Prime (k + 1)` (that is, `pₖ₊₂` in the usual numbering `p₁ = 2, p₂ = 3, …`) is
congruent to `3` modulo `4`, and `0` otherwise. -/
noncomputable def rokickiDigit (k : ℕ) : ℕ := if Nat.nth Nat.Prime (k + 1) % 4 = 3 then 1 else 0

/-- **Rokicki's constant** `ρ = 0.70040013796579773…`: the real number whose binary expansion
`0.b₀ b₁ b₂ …` has `bₖ = 1` exactly when the odd prime `pₖ₊₂` is `3` modulo `4`. It is the limit of
`A362583 n / 2 ^ (n - 1)`, as observed by Tom Rokicki. -/
noncomputable def rokickiConstant : ℝ := ∑' k : ℕ, (rokickiDigit k : ℝ) / 2 ^ (k + 1)

@[inherit_doc] scoped[RokickiConstant] notation "ρ" => Real.rokickiConstant

/-- The primes after `2` are odd. -/
private theorem odd_nth_prime_succ (k : ℕ) : Odd (Nat.nth Nat.Prime (k + 1)) := by
  refine (Nat.prime_nth_prime _).eq_two_or_odd'.resolve_left fun h ↦ k.succ_ne_zero ?_
  rw [← Nat.nth_prime_zero_eq_two] at h
  exact Nat.nth_injective Nat.infinite_setOfPred_prime h

private theorem nth_prime_succ_mod_four (k : ℕ) :
    Nat.nth Nat.Prime (k + 1) % 4 = 1 ∨ Nat.nth Nat.Prime (k + 1) % 4 = 3 :=
  Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (odd_nth_prime_succ k))

/-- The digits of Rokicki's constant are binary digits. -/
theorem rokickiDigit_le_one (k : ℕ) : rokickiDigit k ≤ 1 := by
  rw [rokickiDigit]
  split_ifs <;> simp

theorem rokickiDigit_eq_one_iff {k : ℕ} :
    rokickiDigit k = 1 ↔ Nat.nth Nat.Prime (k + 1) % 4 = 3 := by
  rw [rokickiDigit]
  split_ifs with h <;> simp [h]

theorem rokickiDigit_eq_zero_iff {k : ℕ} :
    rokickiDigit k = 0 ↔ Nat.nth Nat.Prime (k + 1) % 4 = 1 := by
  rw [rokickiDigit]
  have := nth_prime_succ_mod_four k
  split_ifs with h <;> simp only [false_iff, true_iff] <;> omega

/-- The series defining Rokicki's constant converges. -/
theorem summable_rokickiDigit_div_two_pow :
    Summable fun k : ℕ ↦ (rokickiDigit k : ℝ) / 2 ^ (k + 1) := by
  simpa only [zero_add] using summable_binaryTail rokickiDigit_le_one 0

/-- Rokicki's constant lies in `[0, 1]`. -/
theorem rokickiConstant_mem_Icc : rokickiConstant ∈ Set.Icc (0 : ℝ) 1 := by
  rw [rokickiConstant, ← binaryTail_zero]
  exact binaryTail_mem_Icc rokickiDigit_le_one 0

/-- The integer whose binary digits are `rokickiDigit 0, …, rokickiDigit (n - 1)`. This is the
term `A362583 (n + 1)` of the OEIS sequence, whose offset is `2`. -/
noncomputable def oeisA362583 (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, rokickiDigit k * 2 ^ (n - 1 - k)

/-- Tom Rokicki's observation: `A362583 (n + 1) / 2 ^ n` converges, and its limit is `ρ`. -/
theorem tendsto_oeisA362583_div_two_pow :
    Tendsto (fun n : ℕ ↦ (oeisA362583 n : ℝ) / 2 ^ n) atTop (𝓝 rokickiConstant) := by
  refine summable_rokickiDigit_div_two_pow.hasSum.tendsto_sum_nat.congr fun n ↦ ?_
  rw [oeisA362583, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  push_cast
  rw [mul_assoc, div_eq_mul_one_div (rokickiDigit k : ℝ)]
  congr 1
  rw [← div_eq_mul_inv, div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
  congr 1
  omega

end Real

namespace RokickiConstant

open Real

/-- The `k`-th odd prime, counting from `oddPrime 0 = 3`; that is, `pₖ₊₂` in the usual
numbering of the primes. -/
noncomputable def oddPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1)

theorem prime_oddPrime (k : ℕ) : (oddPrime k).Prime :=
  Nat.prime_nth_prime _

theorem oddPrime_pos (k : ℕ) : 0 < oddPrime k :=
  (prime_oddPrime k).pos

/-- The odd primes are enumerated in increasing order. -/
theorem oddPrime_strictMono : StrictMono oddPrime := fun _ _ h ↦
  Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.succ_lt_succ h)

theorem oddPrime_zero : oddPrime 0 = 3 :=
  Nat.nth_prime_one_eq_three

theorem odd_oddPrime (k : ℕ) : Odd (oddPrime k) :=
  odd_nth_prime_succ k

/-- Every odd prime is `1` or `3` modulo `4`. -/
theorem oddPrime_mod_four (k : ℕ) : oddPrime k % 4 = 1 ∨ oddPrime k % 4 = 3 :=
  nth_prime_succ_mod_four k

/-- The `k`-th odd prime is at least `k + 2`. -/
theorem add_two_le_oddPrime (k : ℕ) : k + 2 ≤ oddPrime k :=
  (Nat.le_succ _).trans (Nat.add_two_le_nth_prime (k + 1))

/-- The quadratic character modulo `4` encodes the digits of `ρ`:
`χ₄ pₖ₊₂ = 1 - 2 · rokickiDigit k`. -/
theorem χ₄_oddPrime (k : ℕ) : (ZMod.χ₄ (oddPrime k) : ℤ) = 1 - 2 * rokickiDigit k := by
  rcases oddPrime_mod_four k with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, rokickiDigit_eq_zero_iff.mpr h]
    simp
  · rw [ZMod.χ₄_nat_three_mod_four h, rokickiDigit_eq_one_iff.mpr h]
    simp

end RokickiConstant
