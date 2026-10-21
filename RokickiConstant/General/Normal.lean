/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import RokickiConstant.Defs

/-!
# Normality of Rokicki's constant, conditionally on equidistribution of consecutive primes

A real number in `[0, 1]` is *normal in base `b`* if every word of length `L` over the digits
`0, …, b - 1` occurs among its base-`b` digits with limiting frequency `b ^ (-L)`. We define this
for digit sequences (`IsNormalSeq`) and for real numbers (`Real.IsNormal`, through a digit
expansion; a normal digit sequence is never eventually constant, so the expansion is the
canonical one).

The digits of Rokicki's constant are the residues of the consecutive odd primes modulo `4`.
So `ρ` is normal in base `2` as soon as the residue patterns of consecutive primes modulo `4` are
equidistributed: for every word `a` of reduced residues, the proportion of `m` with
`pₘ₊ᵢ ≡ aᵢ (mod 4)` for all `i` tends to `2 ^ (-L)`. This equidistribution
(`ConsecutivePrimesEquidistributed 4`) is a consequence of the Hardy–Littlewood prime tuples
conjecture (Lemke Oliver–Soundararajan, 2016), and is open. The theorem here is the
unconditional implication.

## Main definitions

* `wordCount d w n`: the number of positions `m < n` at which the word `w` occurs in `d`.
* `IsNormalSeq b d`, `Real.IsNormal x b`: normality of a digit sequence, of a real number.
* `ConsecutivePrimesEquidistributed q`: the equidistribution conjecture for residue patterns of
  consecutive primes modulo `q`.

## Main statements

* `Real.isNormal_rokickiConstant_of_consecutivePrimesEquidistributed`: if the residue patterns
  of consecutive primes modulo `4` are equidistributed, then Rokicki's constant is normal in
  base `2`.

## Tags

normal number, consecutive primes, Hardy–Littlewood conjecture
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Topology Finset

/-- The number of positions `m < n` at which the word `w` occurs in the sequence `d`, counting
overlapping occurrences. -/
def wordCount (d : ℕ → ℕ) {L : ℕ} (w : Fin L → ℕ) (n : ℕ) : ℕ :=
  ((range n).filter fun m ↦ ∀ i : Fin L, d (m + i) = w i).card

/-- A digit sequence `d` with digits `< b` is *normal in base `b`* if every word of length `L`
over the digits `0, …, b - 1` occurs with limiting frequency `b ^ (-L)`. -/
def IsNormalSeq (b : ℕ) (d : ℕ → ℕ) : Prop :=
  ∀ (L : ℕ) (w : Fin L → ℕ), (∀ i, w i < b) →
    Tendsto (fun n ↦ (wordCount d w n : ℝ) / n) atTop (𝓝 ((1 : ℝ) / b ^ L))

/-- A real number `x ∈ [0, 1]` is *normal in base `b`* if it has a base-`b` digit expansion
whose digit sequence is normal. A normal digit sequence is never eventually constant, so such an
expansion is the canonical one, and this agrees with Borel's definition. -/
def Real.IsNormal (x : ℝ) (b : ℕ) : Prop :=
  ∃ d : ℕ → ℕ, (∀ k, d k < b) ∧ x = ∑' k : ℕ, (d k : ℝ) / b ^ (k + 1) ∧ IsNormalSeq b d

/-- **Equidistribution of residue patterns of consecutive primes modulo `q`**: for every word
`a` of units of `ZMod q`, the proportion of `m < n` with `pₘ₊ᵢ ≡ aᵢ (mod q)` for all `i` tends to
`φ(q) ^ (-L)`, where `p₀ = 2 < p₁ < ⋯` are the primes. This is predicted by the Hardy–Littlewood
prime tuples conjecture (Lemke Oliver–Soundararajan, 2016) and is open for every `q ≥ 3`. -/
def ConsecutivePrimesEquidistributed (q : ℕ) : Prop :=
  ∀ (L : ℕ) (a : Fin L → ZMod q), (∀ i, IsUnit (a i)) →
    Tendsto
      (fun n ↦ (((range n).filter fun m ↦ ∀ i : Fin L,
        ((Nat.nth Nat.Prime (m + i) : ℕ) : ZMod q) = a i).card : ℝ) / n)
      atTop (𝓝 ((1 : ℝ) / (Nat.totient q) ^ L))

/-- A word `w` of Rokicki digits occurs at position `m` exactly when the odd primes
`pₘ₊₂, …, pₘ₊L₊₁` have the residues `3` or `1` modulo `4` prescribed by `w`. -/
theorem Real.rokickiDigit_word_iff {L : ℕ} (w : Fin L → ℕ) (hw : ∀ i, w i < 2) (m : ℕ) :
    (∀ i : Fin L, rokickiDigit (m + i) = w i) ↔
      ∀ i : Fin L, ((Nat.nth Nat.Prime (m + 1 + i) : ℕ) : ZMod 4) = if w i = 1 then 3 else 1 := by
  sorry

/-- Shifting the start of the count by one changes it by at most one. -/
theorem wordCount_le_succ_and (d : ℕ → ℕ) {L : ℕ} (w : Fin L → ℕ) (n : ℕ) :
    ((range (n + 1)).filter fun m ↦ ∀ i : Fin L, d (m + i) = w i).card ≤
        wordCount (fun k ↦ d (k + 1)) w n + 1 ∧
      wordCount (fun k ↦ d (k + 1)) w n ≤
        ((range (n + 1)).filter fun m ↦ ∀ i : Fin L, d (m + i) = w i).card := by
  sorry

/-- **Conditional normality.** If the residue patterns of consecutive primes modulo `4` are
equidistributed, then Rokicki's constant is normal in base `2`. -/
theorem Real.isNormal_rokickiConstant_of_consecutivePrimesEquidistributed
    (h : ConsecutivePrimesEquidistributed 4) : rokickiConstant.IsNormal 2 := by
  sorry
