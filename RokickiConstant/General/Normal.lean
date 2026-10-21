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
  refine forall_congr' fun i ↦ ?_
  have hwi := hw i
  generalize w i = c at hwi ⊢
  rw [Nat.add_right_comm]
  interval_cases c
  · simp only [zero_ne_one, ↓reduceIte]
    rw [rokickiDigit_eq_zero_iff, show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by
      norm_num, ZMod.natCast_eq_natCast_iff']
  · simp only [↓reduceIte]
    rw [rokickiDigit_eq_one_iff, show (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) by
      norm_num, ZMod.natCast_eq_natCast_iff']

/-- Removing the position `0` from a count over `range (n + 1)` and shifting the remaining
positions down by one changes the count by at most one. -/
theorem card_filter_range_succ_le (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    ((range (n + 1)).filter P).card ≤ ((range n).filter fun k ↦ P (k + 1)).card + 1 ∧
      ((range n).filter fun k ↦ P (k + 1)).card ≤ ((range (n + 1)).filter P).card := by
  set B := (range n).filter fun k ↦ P (k + 1)
  have hcard : (B.image (· + 1)).card = B.card := card_image_of_injective _ (add_left_injective 1)
  have himage : B.image (· + 1) ⊆ (range (n + 1)).filter P := by
    intro x hx
    simp only [B, mem_image, mem_filter, mem_range] at hx ⊢
    obtain ⟨k, ⟨hk, hP⟩, rfl⟩ := hx
    exact ⟨by omega, hP⟩
  have hsub : (range (n + 1)).filter P ⊆ insert 0 (B.image (· + 1)) := by
    intro m hm
    simp only [B, mem_insert, mem_image, mem_filter, mem_range] at hm ⊢
    obtain ⟨hm, hP⟩ := hm
    rcases m with _ | k
    · exact Or.inl rfl
    · exact Or.inr ⟨k, ⟨by omega, hP⟩, rfl⟩
  exact ⟨(card_le_card hsub).trans ((card_insert_le _ _).trans (by rw [hcard])),
    hcard ▸ card_le_card himage⟩

/-- Shifting the start of the count by one changes it by at most one. -/
theorem wordCount_le_succ_and (d : ℕ → ℕ) {L : ℕ} (w : Fin L → ℕ) (n : ℕ) :
    ((range (n + 1)).filter fun m ↦ ∀ i : Fin L, d (m + i) = w i).card ≤
        wordCount (fun k ↦ d (k + 1)) w n + 1 ∧
      wordCount (fun k ↦ d (k + 1)) w n ≤
        ((range (n + 1)).filter fun m ↦ ∀ i : Fin L, d (m + i) = w i).card := by
  have h := card_filter_range_succ_le (fun m ↦ ∀ i : Fin L, d (m + i) = w i) n
  have hw : wordCount (fun k ↦ d (k + 1)) w n =
      ((range n).filter fun k ↦ ∀ i : Fin L, d (k + 1 + i) = w i).card := by
    simp only [wordCount, Nat.add_right_comm _ 1]
  exact hw ▸ h

/-- **Conditional normality.** If the residue patterns of consecutive primes modulo `4` are
equidistributed, then Rokicki's constant is normal in base `2`. -/
theorem Real.isNormal_rokickiConstant_of_consecutivePrimesEquidistributed
    (h : ConsecutivePrimesEquidistributed 4) : rokickiConstant.IsNormal 2 := by
  refine ⟨rokickiDigit, fun k ↦ Nat.lt_succ_of_le (rokickiDigit_le_one k), by
    simp [rokickiConstant], fun L w hw ↦ ?_⟩
  set a : Fin L → ZMod 4 := fun i ↦ if w i = 1 then 3 else 1
  have ha : ∀ i, IsUnit (a i) := by
    intro i
    simp only [a]
    split_ifs
    · exact ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
    · exact isUnit_one
  have hlim := h L a ha
  have htot : Nat.totient 4 = 2 := by decide
  rw [htot] at hlim
  set P : ℕ → Prop := fun m ↦ ∀ i : Fin L, ((Nat.nth Nat.Prime (m + i) : ℕ) : ZMod 4) = a i
  set c : ℕ → ℕ := fun n ↦ ((range n).filter P).card
  have hwc (n : ℕ) : wordCount rokickiDigit w n = ((range n).filter fun k ↦ P (k + 1)).card := by
    unfold wordCount
    congr 1
    exact filter_congr fun m _ ↦ rokickiDigit_word_iff w hw m
  set ℓ : ℝ := 1 / (2 : ℕ) ^ L
  have hg : Tendsto (fun n : ℕ ↦ (c (n + 1) : ℝ) / (n + 1 : ℕ)) atTop (𝓝 ℓ) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hu : Tendsto (fun n : ℕ ↦ (c (n + 1) : ℝ) / (n + 1 : ℕ) * (1 + 1 / n)) atTop
      (𝓝 (ℓ * (1 + 0))) :=
    hg.mul (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat)
  have hl : Tendsto (fun n : ℕ ↦ (c (n + 1) : ℝ) / (n + 1 : ℕ) * (1 + 1 / n) - 1 / n) atTop
      (𝓝 (ℓ * (1 + 0) - 0)) :=
    hu.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero, mul_one] at hu
  rw [add_zero, mul_one, sub_zero] at hl
  have hform (n : ℕ) (hn : 1 ≤ n) :
      (c (n + 1) : ℝ) / (n + 1 : ℕ) * (1 + 1 / n) = (c (n + 1) : ℝ) / n := by
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hle (n : ℕ) := card_filter_range_succ_le P n
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hform n hn, ← sub_div, hwc]
    gcongr
    have := (hle n).1
    rw [sub_le_iff_le_add]
    exact_mod_cast this
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hform n hn, hwc]
    gcongr
    exact_mod_cast (hle n).2
