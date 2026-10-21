/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

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

theorem rokickiDigit_le_one (k : ℕ) : rokickiDigit k ≤ 1 := by
  sorry

theorem rokickiDigit_eq_one_iff {k : ℕ} :
    rokickiDigit k = 1 ↔ Nat.nth Nat.Prime (k + 1) % 4 = 3 := by
  sorry

theorem rokickiDigit_eq_zero_iff {k : ℕ} :
    rokickiDigit k = 0 ↔ Nat.nth Nat.Prime (k + 1) % 4 = 1 := by
  sorry

theorem summable_rokickiDigit_div_two_pow :
    Summable fun k : ℕ ↦ (rokickiDigit k : ℝ) / 2 ^ (k + 1) := by
  sorry

theorem rokickiConstant_mem_Icc : rokickiConstant ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- The integer whose binary digits are `rokickiDigit 0, …, rokickiDigit (n - 1)`. This is the
term `A362583 (n + 1)` of the OEIS sequence, whose offset is `2`. -/
noncomputable def oeisA362583 (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, rokickiDigit k * 2 ^ (n - 1 - k)

/-- Tom Rokicki's observation: `A362583 (n + 1) / 2 ^ n` converges, and its limit is `ρ`. -/
theorem tendsto_oeisA362583_div_two_pow :
    Tendsto (fun n : ℕ ↦ (oeisA362583 n : ℝ) / 2 ^ n) atTop (𝓝 rokickiConstant) := by
  sorry

end Real

namespace RokickiConstant

open Real

/-- The `k`-th odd prime, counting from `oddPrime 0 = 3`; that is, `pₖ₊₂` in the usual
numbering of the primes. -/
noncomputable def oddPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1)

theorem oddPrime_prime (k : ℕ) : (oddPrime k).Prime := by
  sorry

theorem oddPrime_strictMono : StrictMono oddPrime := by
  sorry

theorem oddPrime_zero : oddPrime 0 = 3 := by
  sorry

theorem odd_oddPrime (k : ℕ) : Odd (oddPrime k) := by
  sorry

theorem oddPrime_mod_four (k : ℕ) : oddPrime k % 4 = 1 ∨ oddPrime k % 4 = 3 := by
  sorry

theorem add_two_le_oddPrime (k : ℕ) : k + 2 ≤ oddPrime k := by
  sorry

/-- The quadratic character modulo `4` encodes the digits of `ρ`:
`χ₄ pₖ₊₂ = 1 - 2 · rokickiDigit k`. -/
theorem χ₄_oddPrime (k : ℕ) : (ZMod.χ₄ (oddPrime k) : ℤ) = 1 - 2 * rokickiDigit k := by
  sorry

end RokickiConstant
