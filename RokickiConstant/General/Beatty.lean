/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import RokickiConstant.General.Expansion

/-!
# Beatty residue constants are irrational

For an irrational real `α`, a modulus `m ≥ 2` and a residue `a`, the *Beatty digit sequence*
`dₖ = [⌊k α⌋ ≡ a (mod m)]` is not eventually periodic, so the *Beatty constant*
`∑ₖ dₖ / b ^ (k + 1)` is irrational in every base `b ≥ 2`.

The proof is the rotation picture. Write `β = α / m`. Then `⌊y⌋ mod m = ⌊m · {y / m}⌋`, so
`⌊k α⌋ ≡ j (mod m)` exactly when the fractional part `{k β}` lies in the arc `[j / m, (j + 1) / m)`.
If `d (n + P) = d n` for all `n ≥ N`, then `d` is constant along the progression `N + t P`. The
points `{N β + t · P β}`, `t ∈ ℕ`, form a forward orbit of the irrational rotation by `P β`, and
by Dirichlet's approximation theorem this forward orbit meets every arc of length `1 / m`: some
multiple `k · P β` lies within `1 / (m + 1)` of a nonzero integer distance, and stepping by that
small nonzero amount cannot jump over an arc of length `1 / m`. So the progression contains both
an index with residue `a mod m` and one with residue `a + 1 mod m`, which differ since `m ≥ 2`.

For rational `α = p / q` the sequence is periodic with period `q m`, and the constant is rational.

## Main definitions

* `Real.beattyDigit α m a`: the digit sequence `k ↦ [⌊k α⌋ ≡ a (mod m)]`.
* `Real.beattyConstant α m a b`: the number `∑ₖ [⌊k α⌋ ≡ a (mod m)] / b ^ (k + 1)`.

## Main statements

* `Int.floor_emod_natCast_eq_floor_mul_fract`: `⌊y⌋ mod m = ⌊m · {y / m}⌋`.
* `Irrational.exists_nat_fract_add_mul_mem_Ico`: the forward orbit of an irrational rotation
  meets every arc.
* `Int.not_eventuallyPeriodic_floor_mul_emod`: for irrational `α` and `m ≥ 2` the Beatty digit
  sequence is not eventually periodic.
* `Real.irrational_beattyConstant`: the Beatty constants of irrational `α` are irrational.
* `Real.beattyDigit_ratCast_add`, `Real.not_irrational_beattyConstant_ratCast`: for rational
  `α` the digits are periodic and the constant is rational.

## Tags

Beatty sequence, irrational rotation, Dirichlet approximation, eventually periodic, irrational
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Function

namespace Int

/-- The residue of `⌊y⌋` modulo `m > 0` is `⌊m · {y / m}⌋`. -/
theorem floor_emod_natCast_eq_floor_mul_fract (y : ℝ) {m : ℕ} (hm : 0 < m) :
    ⌊y⌋ % (m : ℤ) = ⌊(m : ℝ) * fract (y / m)⌋ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : y = ((⌊y / m⌋ * m : ℤ) : ℝ) + m * fract (y / m) := by
    rw [fract]
    push_cast
    field_simp
    ring
  have h0 : 0 ≤ ⌊(m : ℝ) * fract (y / m)⌋ :=
    floor_nonneg.mpr (mul_nonneg hmR.le (fract_nonneg _))
  have h1 : ⌊(m : ℝ) * fract (y / m)⌋ < m := by
    rw [floor_lt]
    push_cast
    nlinarith [fract_lt_one (y / m)]
  conv_lhs => rw [hy, floor_intCast_add, add_comm, add_mul_emod_self_right]
  exact emod_eq_of_lt h0 h1

/-- `⌊y⌋ ≡ j (mod m)` exactly when `m · {y / m} ∈ [j, j + 1)`. -/
theorem floor_emod_natCast_eq_iff {y : ℝ} {m : ℕ} (hm : 0 < m) {j : ℤ} :
    ⌊y⌋ % (m : ℤ) = j ↔ (j : ℝ) ≤ m * fract (y / m) ∧ (m : ℝ) * fract (y / m) < j + 1 := by
  rw [floor_emod_natCast_eq_floor_mul_fract y hm, floor_eq_iff]

end Int

namespace Irrational

/-- **The forward orbit of an irrational rotation meets every arc.** For irrational `γ`, every
starting point `x` and every arc `[c, c + L) ⊆ [0, 1)` of positive length, some `n : ℕ` has
`{x + n γ} ∈ [c, c + L)`. By Dirichlet, some `k > 0` has `δ = k γ - round (k γ)` of size less
than `L`; `δ ≠ 0` by irrationality, and the points `x + s δ`, `s ∈ ℕ`, step by `|δ| < L` and so
cannot jump over a translate of the arc. -/
theorem exists_nat_fract_add_mul_mem_Ico {γ : ℝ} (hγ : Irrational γ) (x : ℝ) {c L : ℝ}
    (hL : 0 < L) (hc : 0 ≤ c) (hcL : c + L ≤ 1) :
    ∃ n : ℕ, c ≤ Int.fract (x + n * γ) ∧ Int.fract (x + n * γ) < c + L := by
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hL
  obtain ⟨k, hk, -, hδ⟩ := Real.exists_nat_abs_mul_sub_round_le γ (Nat.succ_pos M)
  set δ := (k : ℝ) * γ - round ((k : ℝ) * γ) with hδdef
  have hδL : |δ| < L := by
    refine hδ.trans_lt ((one_div_le_one_div_of_le (by positivity) ?_).trans_lt hM)
    push_cast
    linarith
  have hδ0 : δ ≠ 0 := fun h ↦ (hγ.natCast_mul hk.ne').ne_int (round ((k : ℝ) * γ)) (by linarith)
  -- The points `x + n γ` with `n = s k` are `x + s δ` up to an integer.
  have hfract (s : ℕ) : Int.fract (x + ((s * k : ℕ) : ℝ) * γ) = Int.fract (x + s * δ) := by
    rw [← Int.fract_add_intCast (x + s * δ) (s * round ((k : ℝ) * γ))]
    congr 1
    push_cast
    ring
  -- It suffices to land `x + s δ` in the arc `[T, T + L)` for an integer translate `T` of `c`.
  have key (s : ℕ) (z : ℤ) (h1 : z + c ≤ x + s * δ) (h2 : x + s * δ < z + c + L) :
      ∃ n : ℕ, c ≤ Int.fract (x + n * γ) ∧ Int.fract (x + n * γ) < c + L := by
    have hfl : ⌊x + s * δ⌋ = z := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith
    refine ⟨s * k, ?_⟩
    rw [hfract, Int.fract, hfl]
    constructor <;> linarith
  rcases hδ0.lt_or_gt with hneg | hpos
  · -- Step downwards from `x` into `[⌊x⌋ - 1 + c, ⌊x⌋ - 1 + c + L)`.
    have he : 0 < -δ := by linarith
    have hδL' : -δ < L := by rw [abs_of_neg hneg] at hδL; exact hδL
    set T : ℝ := ((⌊x⌋ - 1 : ℤ) : ℝ) + c
    have hT : 0 ≤ x - T := by
      simp only [T]
      push_cast
      linarith [Int.floor_le x]
    set s := ⌊(x - T) / -δ⌋₊
    have hs1 : (s : ℝ) * -δ ≤ x - T := (le_div_iff₀ he).mp (Nat.floor_le (div_nonneg hT he.le))
    have hs2 : x - T < ((s : ℝ) + 1) * -δ := (div_lt_iff₀ he).mp (Nat.lt_floor_add_one _)
    exact key s (⌊x⌋ - 1) (by linarith) (by linarith)
  · -- Step upwards from `x` into `[⌊x⌋ + 1 + c, ⌊x⌋ + 1 + c + L)`.
    have hδL' : δ < L := by rw [abs_of_pos hpos] at hδL; exact hδL
    set T : ℝ := ((⌊x⌋ + 1 : ℤ) : ℝ) + c
    have hT : 0 ≤ T - x := by
      simp only [T]
      push_cast
      linarith [Int.lt_floor_add_one x]
    set s := ⌈(T - x) / δ⌉₊
    have hs1 : T - x ≤ (s : ℝ) * δ := (div_le_iff₀ hpos).mp (Nat.le_ceil _)
    have hs2 : ((s : ℝ) - 1) * δ < T - x :=
      (lt_div_iff₀ hpos).mp (by linarith [Nat.ceil_lt_add_one (div_nonneg hT hpos.le)])
    exact key s (⌊x⌋ + 1) (by linarith) (by linarith)

end Irrational

namespace Real

/-- The **Beatty digit sequence** `k ↦ [⌊k α⌋ ≡ a (mod m)]`. -/
noncomputable def beattyDigit (α : ℝ) (m : ℕ) (a : ℤ) (k : ℕ) : ℕ :=
  if ⌊(k : ℝ) * α⌋ % (m : ℤ) = a % m then 1 else 0

/-- Beatty digits are binary. -/
theorem beattyDigit_lt_two (α : ℝ) (m : ℕ) (a : ℤ) (k : ℕ) : beattyDigit α m a k < 2 := by
  unfold beattyDigit
  split_ifs <;> omega

/-- **Beatty digit sequences of irrational slope are not eventually periodic.** If they were,
with period `P` from `N` on, the digit would be constant along `N + t P`; but along this
progression `⌊k α⌋ mod m` takes every value, by `Irrational.exists_nat_fract_add_mul_mem_Ico`
applied to the irrational rotation by `P α / m`. -/
theorem not_eventuallyPeriodic_beattyDigit {α : ℝ} (hα : Irrational α) {m : ℕ} (hm : 2 ≤ m)
    (a : ℤ) {P : ℕ} (hP : 0 < P) : ¬ EventuallyPeriodic (beattyDigit α m a) P := by
  intro h
  obtain ⟨N, hN⟩ := h.exists_forall_le
  have hconst (t : ℕ) : beattyDigit α m a (N + t * P) = beattyDigit α m a N := by
    induction t with
    | zero => simp
    | succ t ih => rw [show N + (t + 1) * P = N + t * P + P by ring, hN _ (by omega), ih]
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hγ : Irrational (P * α / m) := (hα.natCast_mul hP.ne').div_natCast hm0.ne'
  -- Every residue `j` occurs along the progression `N + t P`.
  have hit (j : ℤ) (hj0 : 0 ≤ j) (hjm : j < m) :
      ∃ t : ℕ, ⌊((N + t * P : ℕ) : ℝ) * α⌋ % (m : ℤ) = j := by
    have hjm' : (j : ℝ) + 1 ≤ m := by exact_mod_cast hjm
    obtain ⟨t, h1, h2⟩ := hγ.exists_nat_fract_add_mul_mem_Ico (N * α / m) (c := j / m)
      (L := 1 / m) (by positivity) (by positivity)
      (by rw [← add_div, div_le_one hmR]; exact hjm')
    refine ⟨t, (Int.floor_emod_natCast_eq_iff hm0).mpr ?_⟩
    have he : ((N + t * P : ℕ) : ℝ) * α / m = N * α / m + t * (P * α / m) := by
      push_cast
      ring
    rw [he]
    constructor
    · calc (j : ℝ) = m * (j / m) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 hmR.le
    · calc (m : ℝ) * Int.fract (N * α / m + t * (P * α / m)) < m * (j / m + 1 / m) :=
            mul_lt_mul_of_pos_left h2 hmR
        _ = j + 1 := by field_simp
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm0
  obtain ⟨t₁, ht₁⟩ := hit (a % m) (Int.emod_nonneg _ hmZ.ne') (Int.emod_lt_of_pos _ hmZ)
  obtain ⟨t₂, ht₂⟩ := hit ((a + 1) % m) (Int.emod_nonneg _ hmZ.ne') (Int.emod_lt_of_pos _ hmZ)
  have hne : (a + 1) % (m : ℤ) ≠ a % m := by
    intro hmod
    have hdvd : (m : ℤ) ∣ 1 := by
      have := (Int.ModEq.dvd hmod).neg_right
      simpa using this
    have := Int.le_of_dvd one_pos hdvd
    omega
  have e₁ : beattyDigit α m a (N + t₁ * P) = 1 := by simp only [beattyDigit, ht₁, ↓reduceIte]
  have e₂ : beattyDigit α m a (N + t₂ * P) = 0 := by
    simp only [beattyDigit, ht₂, hne, ↓reduceIte]
  rw [hconst] at e₁ e₂
  omega

/-- The **Beatty constant** `∑ₖ [⌊k α⌋ ≡ a (mod m)] / b ^ (k + 1)`. -/
noncomputable def beattyConstant (α : ℝ) (m : ℕ) (a : ℤ) (b : ℕ) : ℝ :=
  ∑' k : ℕ, (beattyDigit α m a k : ℝ) / b ^ (k + 1)

/-- **Beatty constants of irrational slope are irrational** in every base `b ≥ 2`. -/
theorem irrational_beattyConstant {α : ℝ} (hα : Irrational α) {m : ℕ} (hm : 2 ≤ m) (a : ℤ)
    {b : ℕ} (hb : 2 ≤ b) : Irrational (beattyConstant α m a b) :=
  irrational_tsum_div_pow hb (fun k ↦ (beattyDigit_lt_two α m a k).trans_le hb)
    fun _ hP ↦ not_eventuallyPeriodic_beattyDigit hα hm a hP

/-- The Beatty constant, written with the indicator digits as real numbers. -/
theorem beattyConstant_eq (α : ℝ) (m : ℕ) (a : ℤ) (b : ℕ) :
    beattyConstant α m a b =
      ∑' k : ℕ, (if ⌊(k : ℝ) * α⌋ % (m : ℤ) = a % m then (1 : ℝ) else 0) / b ^ (k + 1) := by
  unfold beattyConstant beattyDigit
  congr 1
  ext k
  split_ifs <;> simp

/-- **Rational slope gives periodic digits**: for `α = r` rational the Beatty digits have period
`r.den * m`, since `⌊(k + q m) p / q⌋ = ⌊k p / q⌋ + p m`. -/
theorem beattyDigit_ratCast_add (r : ℚ) (m : ℕ) (a : ℤ) (k : ℕ) :
    beattyDigit r m a (k + r.den * m) = beattyDigit r m a k := by
  have he : ((k + r.den * m : ℕ) : ℝ) * (r : ℝ) = k * r + ((r.num * m : ℤ) : ℝ) := by
    have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
    push_cast
    rw [Rat.cast_def]
    field_simp
  unfold beattyDigit
  rw [he, Int.floor_add_intCast, Int.add_mul_emod_self_right]

end Real

namespace Int

/-- **Beatty residues are not eventually periodic**: for irrational `α`, `m ≥ 2` and any residue
`a`, the sequence `k ↦ [⌊k α⌋ ≡ a (mod m)]` is not eventually periodic. -/
theorem not_eventuallyPeriodic_floor_mul_emod {α : ℝ} (hα : Irrational α) {m : ℕ} (hm : 2 ≤ m)
    (a : ℤ) {P : ℕ} (hP : 0 < P) :
    ¬ EventuallyPeriodic (fun k : ℕ ↦ if ⌊(k : ℝ) * α⌋ % m = a % m then 1 else 0) P :=
  Real.not_eventuallyPeriodic_beattyDigit hα hm a hP

end Int

/-- A base-`b` expansion whose digits are periodic from the start is rational: with period `p`,
its value `S` satisfies `S = ∑_{k < p} d k / b ^ (k + 1) + S / b ^ p`. -/
theorem not_irrational_tsum_div_pow_of_periodic {b : ℕ} {d : ℕ → ℕ} (hb : 2 ≤ b)
    (hd : ∀ k, d k < b) {p : ℕ} (hp : 0 < p) (hper : ∀ k, d (k + p) = d k) :
    ¬ Irrational (∑' k : ℕ, (d k : ℝ) / b ^ (k + 1)) := by
  set S := ∑' k : ℕ, (d k : ℝ) / b ^ (k + 1) with hS
  set A := ∑ k ∈ Finset.range p, (d k : ℝ) / b ^ (k + 1) with hA
  have hs : Summable fun k : ℕ ↦ (d k : ℝ) / b ^ (k + 1) := by
    simpa using summable_expansionTail hb hd 0
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have htail : ∑' k : ℕ, (d (k + p) : ℝ) / b ^ (k + p + 1) = S / b ^ p := by
    rw [hS, ← tsum_div_const]
    refine tsum_congr fun k ↦ ?_
    rw [hper, show k + p + 1 = k + 1 + p by ring, pow_add, div_div]
  have key : S = A + S / b ^ p := by
    rw [← htail, hA]
    exact (hs.sum_add_tsum_nat_add p).symm
  have hbp : (1 : ℝ) < b ^ p := one_lt_pow₀ (by exact_mod_cast (show 1 < b by omega)) hp.ne'
  have hSA : S = A * b ^ p / (b ^ p - 1) := by
    rw [eq_div_iff (by linarith)]
    have : S / b ^ p * b ^ p = S := div_mul_cancel₀ _ (by positivity)
    nlinarith [key]
  rw [Irrational, not_not]
  refine ⟨(∑ k ∈ Finset.range p, (d k : ℚ) / b ^ (k + 1)) * b ^ p / (b ^ p - 1), ?_⟩
  rw [hSA, hA]
  push_cast
  rfl

namespace Real

/-- **Rational slope gives rational Beatty constants.** -/
theorem not_irrational_beattyConstant_ratCast (r : ℚ) {m : ℕ} (hm : 0 < m) (a : ℤ) {b : ℕ}
    (hb : 2 ≤ b) : ¬ Irrational (beattyConstant r m a b) :=
  not_irrational_tsum_div_pow_of_periodic hb (fun k ↦ (beattyDigit_lt_two _ m a k).trans_le hb)
    (Nat.mul_pos r.pos hm) (beattyDigit_ratCast_add r m a)

end Real
