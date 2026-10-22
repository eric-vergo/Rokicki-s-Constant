/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SumTwoSquares
import RokickiConstant.General.Expansion
import RokickiConstant.PartialSums

/-!
# Rokicki-type constants of the sums of two squares and of the squarefree numbers

Replace the primes in Rokicki's constant by another arithmetic sequence `a₀ < a₁ < ⋯` and a
digit rule `dₖ = g (aₖ)`; the constant `∑ₖ dₖ / b ^ (k + 1)` is irrational exactly when `(dₖ)` is
not eventually periodic (`irrational_tsum_div_pow`). This file settles this for two sequences
with elementary, unconditional proofs, and for a third digit conditionally on Landau's theorem.

**Runs.** An eventually periodic sequence with period `p` that has a run of `p` equal values `v`
beyond the onset of periodicity is constant `v` from there on
(`Function.not_eventuallyPeriodic_of_runs`). Runs in the enumeration `nth p` come from windows
`[M, M + W)` of integers in which every element of `p` has the desired property
(`Nat.exists_run_nth_of_window`).

**Sums of two squares** `s₀ = 1 < s₁ = 2 < 4 < 5 < ⋯`.

* `[sₖ is a square]`: between `t ^ 2` and `(t + 1) ^ 2` lie the sums of two squares
  `t ^ 2 + b ^ 2`, `b ^ 2 < 2 t`, and no square.
* `[sₖ is prime]`: for `t` a multiple of `R !`, every `t ^ 2 + j`, `2 ≤ j ≤ R`, is divisible by
  `j`; the window contains the sums of two squares `t ^ 2 + b ^ 2`, `2 ≤ b ≤ √R`. The value `1`
  recurs at the primes `p ≡ 1 (mod 4)` (Fermat).
* `sₖ mod 2` (equivalently `[sₖ ≡ 1 (mod 4)]`), conditionally. The doubling self-similarity
  `n ∈ S ↔ 2 n ∈ S` gives `B(2 n) = #{odd s ≤ 2 n} + B(n)` for the counting function `B`. An
  eventually periodic parity sequence makes `#{odd s ≤ x} = c B(x) + O(1)`, so
  `B(n) = (1 - c) B(2 n) + O(1)`. If `B(n) / B(2 n) → 1 / 2` this forces `c = 1 / 2`, then
  `B(2 ^ j n₀) ≥ 2 ^ j`, contradicting density zero. Both inputs follow from Landau's asymptotic
  `B(n) ~ K n / √(log n)`, which is not in Mathlib; it is a hypothesis here.

**Squarefree numbers** `u₀ = 1 < u₁ = 2 < 3 < 5 < ⋯`. *Every word of nonzero residues mod `4`
occurs among consecutive squarefree numbers, arbitrarily late*
(`Nat.exists_squarefreeNth_mod_four_eq`). The candidates sit at `M + t G + rₜ` with
`G = ((4 L + 2) !) ^ 2` and `M ≡ 0 (mod G)`, so no `p ^ 2` with `p ≤ 4 L + 2` divides them; every
other integer of the window is made non-squarefree by the Chinese remainder theorem with a square
of its own large prime; and along the resulting progression of `M` a union bound over the primes
`p > 4 L + 2`, using only `∑_{n > K} 1 / n ^ 2 ≤ 2 / (K + 1)`, leaves at least half of the `M`
with all candidates squarefree. This is an elementary substitute for Mirsky's pattern count.

## Main definitions

* `Nat.IsSumTwoSq`, `Nat.sumTwoSq`, `Nat.sumTwoSqCount`: the positive sums of two squares, their
  enumeration and their counting function.
* `Nat.sumTwoSqSquareDigit`, `Nat.sumTwoSqPrimeDigit`: the digits `[sₖ is a square]` and
  `[sₖ is prime]`.
* `Nat.squarefreeNth`: the enumeration of the squarefree numbers.
* `Real.sumTwoSqSquareConstant`, `Real.sumTwoSqPrimeConstant`, `Real.sumTwoSqParityConstant`,
  `Real.squarefreeConstant`: the corresponding constants in base `b`.

## Main statements

* `Function.not_eventuallyPeriodic_of_runs`, `Nat.exists_run_nth_of_window`: runs and windows.
* `Real.irrational_sumTwoSqSquareConstant`, `Real.irrational_sumTwoSqPrimeConstant`:
  unconditional irrationality for the sums of two squares.
* `Nat.isSumTwoSq_two_mul_iff`, `Nat.sum_mod_two_add_count`: doubling.
* `Nat.not_eventuallyPeriodic_sumTwoSq_mod_two_of_tendsto`: the parity digit, from density zero
  and `B(n) / B(2 n) → 1 / 2`; `Real.irrational_sumTwoSqParityConstant_of_landau`: the parity
  constant is irrational if Landau's asymptotic holds.
* `Nat.exists_squarefreeNth_mod_four_eq`: every word over the residues `{1, 2, 3}` occurs.
* `Real.irrational_tsum_squarefreeNth_mod_four`, `Real.irrational_squarefreeConstant`,
  `Real.irrational_tsum_squarefreeNth_mod_four_div_four_pow`: squarefree residue constants are
  irrational.

## References

* E. Landau, *Über die Einteilung der positiven ganzen Zahlen in vier Klassen nach der Mindestzahl
  der zu ihrer additiven Zusammensetzung erforderlichen Quadrate*, Arch. Math. Phys. (3) 13
  (1908), 305–312.
* L. Mirsky, *Arithmetical pattern problems relating to divisibility by rth powers*, Proc. London
  Math. Soc. (2) 50 (1949), 497–508.

## Tags

sums of two squares, squarefree numbers, eventually periodic, irrational, sieve
-/

set_option doc.verso true
set_option doc.verso.suggestions false

open Filter Function Finset Topology

-- Runs and windows

namespace Function

/-- An eventually periodic sequence with period `p > 0` that has a run of `p` equal values `v`
starting beyond the onset of periodicity is constant `v` from there on. So a sequence with
arbitrarily late runs of every length of the value `v`, and with infinitely many values `≠ v`, is
not eventually periodic. -/
theorem not_eventuallyPeriodic_of_runs {α : Type*} {d : ℕ → α} {v : α}
    (hrun : ∀ L N, ∃ k, N ≤ k ∧ ∀ i < L, d (k + i) = v) (hne : ∀ N, ∃ n, N ≤ n ∧ d n ≠ v)
    {p : ℕ} (hp : 0 < p) : ¬ EventuallyPeriodic d p := by
  intro h
  obtain ⟨N, hN⟩ := h.exists_forall_le
  obtain ⟨k, hk, hrun⟩ := hrun p N
  have key (n : ℕ) : d (k + n) = v := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < p
      · exact hrun n hn
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + p := ⟨n - p, by omega⟩
        rw [← add_assoc, hN _ (by omega)]
        exact ih m (by omega)
  obtain ⟨n, hn, hne⟩ := hne k
  exact hne (by simpa [Nat.add_sub_cancel' hn] using key (n - k))

end Function

namespace Nat

variable {p : ℕ → Prop} [DecidablePred p]

/-- **Windows give runs.** If `p` holds infinitely often and, arbitrarily far out, there are
windows `[M, M + W)` containing at least `L` elements of `p`, all of which satisfy `B`, then the
enumeration `nth p` has arbitrarily late runs of length `L` inside `B`. -/
theorem exists_run_nth_of_window (hp : (Set.ofPred p).Infinite) {B : ℕ → Prop}
    (h : ∀ L N, ∃ M W, N ≤ M ∧ L ≤ count (fun i ↦ p (M + i)) W ∧
      ∀ i < W, p (M + i) → B (M + i))
    (L K : ℕ) : ∃ k, K ≤ k ∧ ∀ i < L, B (nth p (k + i)) := by
  obtain ⟨M, W, hM, hL, hB⟩ := h L (nth p K)
  refine ⟨count p M, ?_, fun i hi ↦ ?_⟩
  · calc K = count p (nth p K) := (count_nth_of_infinite hp K).symm
      _ ≤ count p M := count_monotone p hM
  · have h1 : M ≤ nth p (count p M + i) :=
      (le_nth_count hp M).trans (nth_monotone hp (Nat.le_add_right _ _))
    have h2 : nth p (count p M + i) < M + W := by
      apply nth_lt_of_lt_count
      rw [count_add]
      omega
    have := hB (nth p (count p M + i) - M) (by omega)
    rw [Nat.add_sub_cancel' h1] at this
    exact this (nth_mem_of_infinite hp _)

omit [DecidablePred p] in
/-- If `p` holds infinitely often and `A` holds at arbitrarily large elements of `p`, then
`A (nth p k)` holds for arbitrarily large `k`. -/
theorem exists_nth_of_frequently (hp : (Set.ofPred p).Infinite) {A : ℕ → Prop}
    (h : ∀ N, ∃ n, N ≤ n ∧ p n ∧ A n) (K : ℕ) : ∃ k, K ≤ k ∧ A (nth p k) := by
  classical
  obtain ⟨n, hn, hpn, hAn⟩ := h (nth p K)
  refine ⟨count p n, ?_, by rwa [nth_count hpn]⟩
  calc K = count p (nth p K) := (count_nth_of_infinite hp K).symm
    _ ≤ count p n := count_monotone p hn

/-- A lower bound for a count: if `f` maps `[0, L)` injectively into `[0, W) ∩ q`, then
`L ≤ count q W`. -/
theorem le_count_of_strictMono {q : ℕ → Prop} [DecidablePred q] {L W : ℕ} {f : ℕ → ℕ}
    (hf : StrictMono f) (hfW : ∀ c < L, f c < W ∧ q (f c)) : L ≤ count q W := by
  rw [count_eq_card_filter_range]
  simpa using card_le_card_of_injOn f (s := range L)
    (fun c hc ↦ by
      have := hfW c (mem_range.mp hc)
      simp [this.1, this.2])
    (hf.injective.injOn)

end Nat

-- Sums of two squares

namespace Nat

/-- The positive sums of two squares `1, 2, 4, 5, 8, 9, 10, 13, …`. -/
def IsSumTwoSq (n : ℕ) : Prop := 0 < n ∧ ∃ x y : ℕ, n = x ^ 2 + y ^ 2

noncomputable instance : DecidablePred IsSumTwoSq := Classical.decPred _

/-- Every positive square is a sum of two squares. -/
theorem isSumTwoSq_sq {t : ℕ} (ht : 0 < t) : IsSumTwoSq (t ^ 2) :=
  ⟨by positivity, t, 0, by ring⟩

/-- `t ^ 2 + b ^ 2` is a sum of two squares when `b > 0`. -/
theorem isSumTwoSq_sq_add_sq (t : ℕ) {b : ℕ} (hb : 0 < b) : IsSumTwoSq (t ^ 2 + b ^ 2) :=
  ⟨by positivity, t, b, rfl⟩

/-- There are infinitely many sums of two squares. -/
theorem infinite_setOf_isSumTwoSq : (Set.ofPred IsSumTwoSq).Infinite :=
  Set.infinite_of_forall_exists_gt fun n ↦
    ⟨(n + 1) ^ 2, isSumTwoSq_sq n.succ_pos, by nlinarith⟩

/-- The `k`-th positive sum of two squares: `sumTwoSq 0 = 1`, `sumTwoSq 1 = 2`,
`sumTwoSq 2 = 4`, `sumTwoSq 3 = 5`, … -/
noncomputable def sumTwoSq (k : ℕ) : ℕ := nth IsSumTwoSq k

/-- Every prime `p ≢ 3 (mod 4)` is a sum of two squares (Fermat). -/
theorem Prime.isSumTwoSq {p : ℕ} (hp : p.Prime) (h4 : p % 4 ≠ 3) : IsSumTwoSq p := by
  have := Fact.mk hp
  obtain ⟨x, y, h⟩ := Nat.Prime.sq_add_sq h4
  exact ⟨hp.pos, x, y, h.symm⟩

end Nat

-- Unconditional digits: squares and primes among the sums of two squares

namespace Nat

/-- A number strictly between two consecutive squares is not a square. -/
theorem not_isSquare_of_sq_lt_of_lt_sq {t n : ℕ} (h1 : t ^ 2 < n) (h2 : n < (t + 1) ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  have : t < r := by nlinarith
  have : r < t + 1 := by nlinarith
  omega

/-- **Windows without squares.** For `t = L ^ 2 + N + 1`, the window `(t ^ 2, (t + 1) ^ 2)`
contains the `L` sums of two squares `t ^ 2 + b ^ 2`, `1 ≤ b ≤ L`, and no square at all. -/
theorem exists_window_isSumTwoSq_not_isSquare (L N : ℕ) :
    ∃ M W, N ≤ M ∧ L ≤ count (fun i ↦ IsSumTwoSq (M + i)) W ∧
      ∀ i < W, IsSumTwoSq (M + i) → ¬ IsSquare (M + i) := by
  set t := L ^ 2 + N + 1 with ht
  refine ⟨t ^ 2 + 1, 2 * t, by nlinarith, ?_, fun i hi _ ↦ ?_⟩
  · refine le_count_of_strictMono (f := fun c ↦ c * (c + 2))
      (fun a b hab ↦ by dsimp only; nlinarith) fun c hc ↦ ⟨?_, ?_⟩
    · have : (c + 1) ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hc 2
      nlinarith
    · convert isSumTwoSq_sq_add_sq t (b := c + 1) c.succ_pos using 1
      ring
  · exact not_isSquare_of_sq_lt_of_lt_sq (t := t) (by nlinarith) (by nlinarith)

/-- The **square digit** `[sumTwoSq k is a perfect square]`. -/
noncomputable def sumTwoSqSquareDigit (k : ℕ) : ℕ := if IsSquare (sumTwoSq k) then 1 else 0

/-- **The square digit is not eventually periodic.** By
`exists_window_isSumTwoSq_not_isSquare` it has arbitrarily late runs of `0`s of every length,
while it is `1` at every square. -/
theorem not_eventuallyPeriodic_sumTwoSqSquareDigit {P : ℕ} (hP : 0 < P) :
    ¬ EventuallyPeriodic sumTwoSqSquareDigit P := by
  refine not_eventuallyPeriodic_of_runs (v := 0) (fun L N ↦ ?_) (fun N ↦ ?_) hP
  · obtain ⟨k, hk, hrun⟩ := exists_run_nth_of_window infinite_setOf_isSumTwoSq
      (B := fun n ↦ ¬ IsSquare n) exists_window_isSumTwoSq_not_isSquare L N
    exact ⟨k, hk, fun i hi ↦ by simp [sumTwoSqSquareDigit, sumTwoSq, hrun i hi]⟩
  · obtain ⟨k, hk, hA⟩ := exists_nth_of_frequently infinite_setOf_isSumTwoSq
      (A := IsSquare) (fun N ↦ ⟨(N + 1) ^ 2, by nlinarith, isSumTwoSq_sq N.succ_pos,
        ⟨N + 1, by ring⟩⟩) N
    exact ⟨k, hk, by simp [sumTwoSqSquareDigit, sumTwoSq, hA]⟩

/-- **Windows without primes.** Let `R = (L + 2) ^ 2` and let `t` be a multiple of `R !`. Every
`t ^ 2 + j` with `2 ≤ j ≤ R` is divisible by `j`, hence composite, and the window
`[t ^ 2 + 2, t ^ 2 + R]` contains the `L` sums of two squares `t ^ 2 + b ^ 2`, `2 ≤ b ≤ L + 1`. -/
theorem exists_window_isSumTwoSq_not_prime (L N : ℕ) :
    ∃ M W, N ≤ M ∧ L ≤ count (fun i ↦ IsSumTwoSq (M + i)) W ∧
      ∀ i < W, IsSumTwoSq (M + i) → ¬ (M + i).Prime := by
  set R := (L + 2) ^ 2 with hR
  set t := R ! * (N + 1) with ht
  have ht1 : N + 1 ≤ t := Nat.le_mul_of_pos_left _ (factorial_pos R)
  refine ⟨t ^ 2 + 2, R - 1, by nlinarith, ?_, fun i hi _ hpr ↦ ?_⟩
  · refine le_count_of_strictMono (f := fun c ↦ c * (c + 4) + 2)
      (fun a b hab ↦ by dsimp only; nlinarith) fun c hc ↦ ⟨?_, ?_⟩
    · have : (c + 2) ^ 2 ≤ (L + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have : (L + 1) ^ 2 + 3 ≤ R := by rw [hR]; nlinarith
      have : c * (c + 4) + 2 + 2 = (c + 2) ^ 2 := by ring
      omega
    · convert isSumTwoSq_sq_add_sq t (b := c + 2) (by omega) using 1
      ring
  · have hdvd : i + 2 ∣ t ^ 2 + 2 + i := by
      have : i + 2 ∣ t := Dvd.dvd.mul_right (Nat.dvd_factorial (by omega) (by omega)) _
      have : i + 2 ∣ t ^ 2 := Dvd.dvd.pow this two_ne_zero
      rw [show t ^ 2 + 2 + i = t ^ 2 + (i + 2) by ring]
      exact Nat.dvd_add this dvd_rfl
    rcases hpr.eq_one_or_self_of_dvd _ hdvd with h | h
    · omega
    · have : 0 < t ^ 2 := by positivity
      omega

/-- The **prime digit** `[sumTwoSq k is prime]`. It marks, among the sums of two squares, the
norms of the Gaussian primes of degree one. -/
noncomputable def sumTwoSqPrimeDigit (k : ℕ) : ℕ := if (sumTwoSq k).Prime then 1 else 0

/-- **The prime digit is not eventually periodic.** By `exists_window_isSumTwoSq_not_prime` it
has arbitrarily late runs of `0`s of every length, while it is `1` at the infinitely many primes
`p ≡ 1 (mod 4)`, which are sums of two squares by Fermat's theorem. -/
theorem not_eventuallyPeriodic_sumTwoSqPrimeDigit {P : ℕ} (hP : 0 < P) :
    ¬ EventuallyPeriodic sumTwoSqPrimeDigit P := by
  refine not_eventuallyPeriodic_of_runs (v := 0) (fun L N ↦ ?_) (fun N ↦ ?_) hP
  · obtain ⟨k, hk, hrun⟩ := exists_run_nth_of_window infinite_setOf_isSumTwoSq
      (B := fun n ↦ ¬ n.Prime) exists_window_isSumTwoSq_not_prime L N
    exact ⟨k, hk, fun i hi ↦ by simp [sumTwoSqPrimeDigit, sumTwoSq, hrun i hi]⟩
  · obtain ⟨k, hk, hA⟩ := exists_nth_of_frequently infinite_setOf_isSumTwoSq
      (A := Nat.Prime) (fun N ↦ by
        obtain ⟨p, hp, hNp, hp1⟩ := exists_prime_gt_modEq_one N (k := 4) (by norm_num)
        have h4 : p % 4 = 1 := hp1
        exact ⟨p, hNp.le, hp.isSumTwoSq (by omega), hp⟩) N
    exact ⟨k, hk, by simp [sumTwoSqPrimeDigit, sumTwoSq, hA]⟩

end Nat

namespace Real

open Nat

/-- The **square constant** `∑ₖ [sₖ is a square] / b ^ (k + 1)` of the sums of two squares. -/
noncomputable def sumTwoSqSquareConstant (b : ℕ) : ℝ :=
  ∑' k : ℕ, (sumTwoSqSquareDigit k : ℝ) / b ^ (k + 1)

/-- The **prime constant** `∑ₖ [sₖ is prime] / b ^ (k + 1)` of the sums of two squares. -/
noncomputable def sumTwoSqPrimeConstant (b : ℕ) : ℝ :=
  ∑' k : ℕ, (sumTwoSqPrimeDigit k : ℝ) / b ^ (k + 1)

/-- The square constant of the sums of two squares is irrational in every base `b ≥ 2`. -/
theorem irrational_sumTwoSqSquareConstant {b : ℕ} (hb : 2 ≤ b) :
    Irrational (sumTwoSqSquareConstant b) :=
  irrational_tsum_div_pow hb
    (fun k ↦ by unfold sumTwoSqSquareDigit; split_ifs <;> omega)
    fun _ hP ↦ not_eventuallyPeriodic_sumTwoSqSquareDigit hP

/-- The prime constant of the sums of two squares is irrational in every base `b ≥ 2`. -/
theorem irrational_sumTwoSqPrimeConstant {b : ℕ} (hb : 2 ≤ b) :
    Irrational (sumTwoSqPrimeConstant b) :=
  irrational_tsum_div_pow hb
    (fun k ↦ by unfold sumTwoSqPrimeDigit; split_ifs <;> omega)
    fun _ hP ↦ not_eventuallyPeriodic_sumTwoSqPrimeDigit hP

end Real

-- The parity digit of the sums of two squares, conditionally on Landau's theorem

namespace Nat

/-- If `2 n = a ^ 2 + b ^ 2` then `n` is a sum of two squares: `a ≡ b (mod 2)`, and with
`a = b + 2 e` one has `n = (b + e) ^ 2 + e ^ 2`. -/
theorem exists_sq_add_sq_of_two_mul_eq {n a b : ℕ} (h : 2 * n = a ^ 2 + b ^ 2) :
    ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  wlog hab : b ≤ a generalizing a b
  · exact this (a := b) (b := a) (by rw [h]; ring) (by omega)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨e, rfl | rfl⟩ := Nat.even_or_odd' d
  · refine ⟨b + e, e, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_⟩
    rw [h]
    ring
  · exfalso
    have : 2 * n = 2 * (b ^ 2 + 2 * b * e + b + 2 * e ^ 2 + 2 * e) + 1 := by rw [h]; ring
    generalize b ^ 2 + 2 * b * e + b + 2 * e ^ 2 + 2 * e = X at this
    omega

/-- **Self-similarity under doubling**: `2 n` is a sum of two squares iff `n` is. -/
theorem isSumTwoSq_two_mul_iff {n : ℕ} : IsSumTwoSq (2 * n) ↔ IsSumTwoSq n := by
  constructor
  · rintro ⟨hpos, a, b, h⟩
    exact ⟨by omega, exists_sq_add_sq_of_two_mul_eq h⟩
  · rintro ⟨hpos, x, y, h⟩
    obtain ⟨r, s, hrs⟩ := Nat.sq_add_sq_mul (x := 1) (y := 1) (by norm_num : 2 = 1 ^ 2 + 1 ^ 2) h
    exact ⟨by omega, r, s, hrs⟩

/-- The counting function `sumTwoSqCount n = #{m ≤ n : m is a positive sum of two squares}`
(Landau's `B(n)`). -/
noncomputable def sumTwoSqCount (n : ℕ) : ℕ := count IsSumTwoSq (n + 1)

/-- The counting function of the sums of two squares tends to infinity. -/
theorem tendsto_sumTwoSqCount_atTop : Tendsto sumTwoSqCount atTop atTop := by
  refine tendsto_atTop.2 fun k ↦ eventually_atTop.2 ⟨nth IsSumTwoSq k, fun n hn ↦ ?_⟩
  calc k = count IsSumTwoSq (nth IsSumTwoSq k) :=
        (count_nth_of_infinite infinite_setOf_isSumTwoSq k).symm
    _ ≤ sumTwoSqCount n := count_monotone _ (by omega)

/-- Summing a function along the enumeration `nth p` up to `count p n` is summing it over the
elements of `p` below `n`. -/
theorem sum_range_count_nth (p : ℕ → Prop) [DecidablePred p] (g : ℕ → ℕ) (n : ℕ) :
    ∑ k ∈ range (count p n), g (nth p k) = ∑ m ∈ range n, if p m then g m else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [count_succ, sum_range_succ, ← ih]
    split_ifs with h
    · rw [sum_range_succ, nth_count h]
    · simp

/-- The **doubling identity** `B(2 n) = #{odd s ≤ 2 n} + B(n)`: the even sums of two squares up
to `2 n` are the doubles of the sums of two squares up to `n`. -/
theorem sum_mod_two_add_count (n : ℕ) :
    (∑ m ∈ range (2 * n + 1), if IsSumTwoSq m then m % 2 else 0) + count IsSumTwoSq (n + 1) =
      count IsSumTwoSq (2 * n + 1) := by
  induction n with
  | zero => simp [count_succ, IsSumTwoSq]
  | succ n ih =>
    have h2 : IsSumTwoSq (2 * n + 1 + 1) ↔ IsSumTwoSq (n + 1) := by
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
      exact isSumTwoSq_two_mul_iff
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      count_succ _ (n + 1), count_succ _ (2 * n + 1 + 1), count_succ _ (2 * n + 1), ← ih]
    have m1 : (2 * n + 1) % 2 = 1 := by omega
    have m2 : (2 * n + 1 + 1) % 2 = 0 := by omega
    by_cases a : IsSumTwoSq (2 * n + 1) <;> by_cases b : IsSumTwoSq (n + 1) <;>
      simp [a, b, h2, m1, m2] <;> ring

/-- **The parity digit, conditionally.** Suppose that the counting function `B` of the sums of
two squares has density zero, `B(n) / n → 0`, and is regularly varying of index one along
doubling, `B(n) / B(2 n) → 1 / 2`; both follow from Landau's theorem. Then the parity sequence
`sₖ mod 2` of the sums of two squares is not eventually periodic.

If it were, the number of odd `sₖ` among the first `K` would be `c K + O(1)`, and the doubling
identity `B(2 n) = #{odd s ≤ 2 n} + B(n)` would give `B(n) = (1 - c) B(2 n) + O(1)`. The second
hypothesis forces `c = 1 / 2`, and then `B(2 n) - 2 C ≥ 2 (B(n) - 2 C)`, so `B(2 ^ j n₀) ≥ 2 ^ j`
for a suitable `n₀`, contradicting density zero. -/
theorem not_eventuallyPeriodic_sumTwoSq_mod_two_of_tendsto
    (h0 : Tendsto (fun n : ℕ ↦ (sumTwoSqCount n : ℝ) / n) atTop (𝓝 0))
    (h2 : Tendsto (fun n : ℕ ↦ (sumTwoSqCount n : ℝ) / sumTwoSqCount (2 * n)) atTop
      (𝓝 (1 / 2))) {P : ℕ} (hP : 0 < P) :
    ¬ EventuallyPeriodic (fun k ↦ sumTwoSq k % 2) P := by
  intro hper
  set T : ℕ → ℝ := fun n ↦ (sumTwoSqCount n : ℝ) with hT
  have hper' : EventuallyPeriodic (fun k ↦ ((sumTwoSq k % 2 : ℕ) : ℤ)) P :=
    hper.mono fun n hn ↦ by simp only [hn]
  obtain ⟨c, C, hC⟩ := hper'.exists_abs_sum_sub_mul_le hP
  have hC0 : 0 ≤ C := by simpa using hC 0
  -- `|B(n) - (1 - c) B(2 n)| ≤ C`.
  have key (n : ℕ) : |T n - (1 - c) * T (2 * n)| ≤ C := by
    have e := sum_mod_two_add_count n
    rw [← sum_range_count_nth IsSumTwoSq (· % 2) (2 * n + 1)] at e
    have e' : (count IsSumTwoSq (2 * n + 1) : ℝ) =
        (∑ k ∈ range (count IsSumTwoSq (2 * n + 1)), ((nth IsSumTwoSq k % 2 : ℕ) : ℝ)) +
          count IsSumTwoSq (n + 1) := by
      exact_mod_cast e.symm
    have hc := hC (count IsSumTwoSq (2 * n + 1))
    simp only [Int.cast_natCast, sumTwoSq] at hc
    simp only [hT, sumTwoSqCount]
    rw [abs_le] at hc ⊢
    constructor <;> linarith [hc.1, hc.2]
  have hTt : Tendsto T atTop atTop := tendsto_natCast_atTop_atTop.comp tendsto_sumTwoSqCount_atTop
  have hT2 : Tendsto (fun n ↦ T (2 * n)) atTop atTop :=
    hTt.comp (tendsto_atTop_mono (fun n ↦ by dsimp only [id]; omega) tendsto_id)
  -- The ratio `B(n) / B(2 n)` tends to `1 - c`, so `c = 1 / 2`.
  have hlim : Tendsto (fun n ↦ T n / T (2 * n)) atTop (𝓝 (1 - c)) := by
    have hE : Tendsto (fun n ↦ C / T (2 * n)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hT2
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hE
    filter_upwards [hT2.eventually_gt_atTop 0] with n hn
    have : T n / T (2 * n) - (1 - c) = (T n - (1 - c) * T (2 * n)) / T (2 * n) := by
      field_simp
    rw [this, Real.norm_eq_abs, abs_div, abs_of_pos hn]
    exact div_le_div_of_nonneg_right (key n) hn.le
  have hc : (1 : ℝ) - c = 1 / 2 := tendsto_nhds_unique hlim h2
  -- Doubling: `B(2 n) - 2 C ≥ 2 (B(n) - 2 C)`.
  have hdbl (n : ℕ) : 2 * (T n - 2 * C) ≤ T (2 * n) - 2 * C := by
    have := (abs_le.mp (key n)).2
    rw [hc] at this
    linarith
  obtain ⟨n₀, hn₀, hn₀1⟩ :=
    ((hTt.eventually_ge_atTop (2 * C + 1)).and (eventually_ge_atTop 1)).exists
  have hgrow (j : ℕ) : (2 : ℝ) ^ j ≤ T (2 ^ j * n₀) - 2 * C := by
    induction j with
    | zero => simp; linarith
    | succ j ih =>
      rw [show 2 ^ (j + 1) * n₀ = 2 * (2 ^ j * n₀) by ring, pow_succ]
      linarith [hdbl (2 ^ j * n₀)]
  have hn₀R : (0 : ℝ) < n₀ := by exact_mod_cast hn₀1
  have hj : Tendsto (fun j : ℕ ↦ 2 ^ j * n₀) atTop atTop :=
    tendsto_atTop_mono (fun j ↦
      (Nat.lt_two_pow_self).le.trans (Nat.le_mul_of_pos_right _ hn₀1)) tendsto_id
  obtain ⟨j, hj⟩ := ((h0.comp hj).eventually (gt_mem_nhds (one_div_pos.2 hn₀R))).exists
  have hpos : (0 : ℝ) < 2 ^ j * n₀ := by positivity
  have h1 : (1 : ℝ) / n₀ ≤ T (2 ^ j * n₀) / (2 ^ j * n₀) := by
    rw [div_le_div_iff₀ hn₀R hpos]
    nlinarith [hgrow j]
  simp only [Function.comp, hT] at hj h1
  push_cast at hj
  linarith

/-- **The parity digit under Landau's theorem.** If `B(n) √(log n) / n → K > 0` (Landau, 1908),
then the parity sequence `sₖ mod 2` of the sums of two squares is not eventually periodic. -/
theorem not_eventuallyPeriodic_sumTwoSq_mod_two_of_landau {K : ℝ} (hK : 0 < K)
    (hL : Tendsto (fun n : ℕ ↦ (sumTwoSqCount n : ℝ) * √(Real.log n) / n) atTop (𝓝 K))
    {P : ℕ} (hP : 0 < P) : ¬ EventuallyPeriodic (fun k ↦ sumTwoSq k % 2) P := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ ↦ √(Real.log n)) atTop atTop := Real.tendsto_sqrt_atTop.comp hlog
  have hev : ∀ᶠ n : ℕ in atTop, 0 < √(Real.log n) := hsq.eventually_gt_atTop 0
  have h2n : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by dsimp only [id]; omega) tendsto_id
  refine not_eventuallyPeriodic_sumTwoSq_mod_two_of_tendsto ?_ ?_ hP
  · have := hL.mul (tendsto_inv_atTop_zero.comp hsq)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp]
    field_simp
  · have hratio : Tendsto (fun n : ℕ ↦ Real.log ((2 * n : ℕ) : ℝ) / Real.log n) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log n + 1) atTop (𝓝 (0 + 1)) :=
        (tendsto_const_nhds.div_atTop hlog).add tendsto_const_nhds
      rw [zero_add] at this
      refine this.congr' ?_
      filter_upwards [hlog.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hn hn0
      push_cast
      rw [Real.log_mul two_ne_zero (by positivity)]
      field_simp
    have hsr : Tendsto (fun n : ℕ ↦ √(Real.log ((2 * n : ℕ) : ℝ)) / √(Real.log n)) atTop
        (𝓝 1) := by
      have := (Real.continuous_sqrt.tendsto 1).comp hratio
      rw [Real.sqrt_one] at this
      refine this.congr' ?_
      filter_upwards [hlog.eventually_gt_atTop 0] with n hn
      simp only [Function.comp]
      rw [Real.sqrt_div' _ hn.le]
    have := ((hL.div (hL.comp h2n) hK.ne').mul hsr).div_const 2
    rw [div_self hK.ne', one_mul] at this
    refine this.congr' ?_
    filter_upwards [hev, h2n.eventually hev, eventually_gt_atTop 0,
      h2n.eventually ((tendsto_natCast_atTop_atTop.comp tendsto_sumTwoSqCount_atTop
        ).eventually_gt_atTop 0)] with n h1 h2 h3 h4
    simp only [Function.comp, Pi.div_apply] at h2 h4 ⊢
    have h3' : (0 : ℝ) < n := by exact_mod_cast h3
    push_cast at h2 h4 ⊢
    have h2' : √(Real.log (↑n * 2)) ≠ 0 := by rw [mul_comm]; exact h2.ne'
    field_simp

end Nat

namespace Real

open Nat

/-- The **parity constant** `∑ₖ (sₖ mod 2) / b ^ (k + 1)` of the sums of two squares. -/
noncomputable def sumTwoSqParityConstant (b : ℕ) : ℝ :=
  ∑' k : ℕ, ((sumTwoSq k % 2 : ℕ) : ℝ) / b ^ (k + 1)

/-- **Under Landau's theorem the parity constant is irrational** in every base `b ≥ 2`. -/
theorem irrational_sumTwoSqParityConstant_of_landau {K : ℝ} (hK : 0 < K)
    (hL : Tendsto (fun n : ℕ ↦ (sumTwoSqCount n : ℝ) * √(Real.log n) / n) atTop (𝓝 K))
    {b : ℕ} (hb : 2 ≤ b) : Irrational (sumTwoSqParityConstant b) :=
  irrational_tsum_div_pow hb (fun _ ↦ (Nat.mod_lt _ two_pos).trans_le hb)
    fun _ hP ↦ not_eventuallyPeriodic_sumTwoSq_mod_two_of_landau hK hL hP

end Real

-- Squarefree numbers: every word of residues mod 4 occurs

namespace Nat

/-- There are infinitely many squarefree numbers (for instance, the primes). -/
theorem infinite_setOf_squarefree : (Set.ofPred (Squarefree : ℕ → Prop)).Infinite :=
  Set.infinite_of_forall_exists_gt fun n ↦ by
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp.prime.squarefree, by omega⟩

/-- The `k`-th squarefree number: `squarefreeNth 0 = 1`, `squarefreeNth 1 = 2`,
`squarefreeNth 2 = 3`, `squarefreeNth 3 = 5`, … -/
noncomputable def squarefreeNth (k : ℕ) : ℕ := nth (Squarefree : ℕ → Prop) k

/-- **Exact windows give consecutive elements.** If, in the window `[M, M + W)`, the elements of
`p` are exactly `M + f 0 < ⋯ < M + f (L - 1)`, then these are the elements of index
`count p M, …, count p M + L - 1` of the enumeration `nth p`. -/
theorem nth_count_add_eq_of_window {p : ℕ → Prop} [DecidablePred p] {M L W : ℕ} {f : ℕ → ℕ}
    (hf : StrictMono f) (hfW : ∀ t < L, f t < W) (hpos : ∀ t < L, p (M + f t))
    (honly : ∀ j < W, p (M + j) → ∃ s < L, f s = j) {t : ℕ} (ht : t < L) :
    nth p (count p M + t) = M + f t := by
  have hcount : count (fun j ↦ p (M + j)) (f t) = t := by
    rw [count_eq_card_filter_range]
    have : {j ∈ range (f t) | p (M + j)} = (range t).image f := by
      ext j
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hj, hpj⟩
        obtain ⟨s, -, rfl⟩ := honly j (hj.trans (hfW t ht)) hpj
        exact ⟨s, hf.lt_iff_lt.mp hj, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨hf hs, hpos s (hs.trans ht)⟩
    rw [this, Finset.card_image_of_injective _ hf.injective, card_range]
  rw [show count p M + t = count p (M + f t) by rw [count_add, hcount]]
  exact nth_count (hpos t ht)

/-- In the progression `a + Q m`, `m < Y`, at most `Y / d + 1` terms are divisible by a modulus
`d` coprime to `Q`: two such `m` are congruent modulo `d`. -/
theorem card_filter_dvd_add_mul_le {d Q : ℕ} (hQ : Coprime d Q) (a Y : ℕ) :
    #{m ∈ range Y | d ∣ a + Q * m} ≤ Y / d + 1 := by
  calc #{m ∈ range Y | d ∣ a + Q * m} ≤ #(range (Y / d + 1)) := by
        refine card_le_card_of_injOn (· / d) (fun m hm ↦ ?_) (fun m₁ h₁ m₂ h₂ he ↦ ?_)
        · simp only [coe_filter, mem_range, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hm ⊢
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hm.1.le)
        · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at h₁ h₂ he
          have h : a + Q * m₁ ≡ a + Q * m₂ [MOD d] :=
            (Nat.modEq_zero_iff_dvd.2 h₁.2).trans (Nat.modEq_zero_iff_dvd.2 h₂.2).symm
          have h' : m₁ ≡ m₂ [MOD d] :=
            Nat.ModEq.cancel_left_of_coprime hQ (Nat.ModEq.add_left_cancel' a h)
          rw [← Nat.div_add_mod m₁ d, ← Nat.div_add_mod m₂ d, he, h']
    _ = Y / d + 1 := card_range _

/-- **The sieve bound.** If every prime `p` with `p ^ 2 ∣ a + Q m`, `m < Y`, satisfies
`K < p < B` and is coprime to `Q`, then at most `2 Y / (K + 1) + B` of the terms `a + Q m`,
`m < Y`, are not squarefree. This uses only `∑_{p > K} 1 / p ^ 2 ≤ 2 / (K + 1)`. -/
theorem card_filter_not_squarefree_le {Q a K B Y : ℕ}
    (h : ∀ m < Y, ∀ p : ℕ, p.Prime → p ^ 2 ∣ a + Q * m → K < p ∧ p < B ∧ Coprime (p ^ 2) Q) :
    (#{m ∈ range Y | ¬ Squarefree (a + Q * m)} : ℝ) ≤ Y * (2 / (K + 1)) + B := by
  set S := {p ∈ Ioo K B | p.Prime}
  have hsub : {m ∈ range Y | ¬ Squarefree (a + Q * m)} ⊆
      S.biUnion fun p ↦ {m ∈ range Y | p ^ 2 ∣ a + Q * m} := by
    intro m hm
    simp only [mem_filter, mem_range] at hm
    obtain ⟨p, hp, hpd⟩ : ∃ p, p.Prime ∧ p * p ∣ a + Q * m := by
      have := hm.2
      rw [Nat.squarefree_iff_prime_squarefree] at this
      push Not at this
      exact this
    have hpd' : p ^ 2 ∣ a + Q * m := by rwa [sq]
    obtain ⟨h1, h2, -⟩ := h m hm.1 p hp hpd'
    simp only [mem_biUnion, mem_filter, mem_Ioo, mem_range, S]
    exact ⟨p, ⟨⟨h1, h2⟩, hp⟩, hm.1, hpd'⟩
  have hcard (p : ℕ) (hp : p ∈ S) :
      (#{m ∈ range Y | p ^ 2 ∣ a + Q * m} : ℝ) ≤ Y / (p : ℝ) ^ 2 + 1 := by
    rcases Finset.eq_empty_or_nonempty {m ∈ range Y | p ^ 2 ∣ a + Q * m} with he | ⟨m₀, hm₀⟩
    · rw [he, card_empty, Nat.cast_zero]
      positivity
    · simp only [S, mem_filter, mem_range] at hp hm₀
      obtain ⟨-, -, hcop⟩ := h m₀ hm₀.1 p hp.2 hm₀.2
      calc (#{m ∈ range Y | p ^ 2 ∣ a + Q * m} : ℝ) ≤ ((Y / p ^ 2 + 1 : ℕ) : ℝ) := by
            exact_mod_cast card_filter_dvd_add_mul_le hcop a Y
        _ ≤ Y / (p : ℝ) ^ 2 + 1 := by
            push_cast
            gcongr
            exact_mod_cast Nat.cast_div_le
  calc (#{m ∈ range Y | ¬ Squarefree (a + Q * m)} : ℝ)
      ≤ #(S.biUnion fun p ↦ {m ∈ range Y | p ^ 2 ∣ a + Q * m}) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ p ∈ S, (#{m ∈ range Y | p ^ 2 ∣ a + Q * m} : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ p ∈ S, ((Y : ℝ) / (p : ℝ) ^ 2 + 1) := sum_le_sum hcard
    _ ≤ ∑ p ∈ Ioo K B, ((Y : ℝ) / (p : ℝ) ^ 2 + 1) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ by positivity
    _ = Y * ∑ p ∈ Ioo K B, ((p : ℝ) ^ 2)⁻¹ + #(Ioo K B) := by
        rw [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul, mul_one]
        simp only [div_eq_mul_inv]
    _ ≤ Y * (2 / (K + 1)) + B := by
        gcongr
        · exact sum_Ioo_inv_sq_le K B
        · rw [Nat.card_Ioo]
          exact_mod_cast (by omega : B - K - 1 ≤ B)

/-- Two numbers `X + i`, `X + j` with `i, j < W` both divisible by `q ^ 2`, `q > W`, coincide. -/
theorem eq_of_sq_dvd_add_of_sq_dvd_add {q X i j W : ℕ} (hq : W < q) (hi : i < W) (hj : j < W)
    (h1 : q ^ 2 ∣ X + i) (h2 : q ^ 2 ∣ X + j) : i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi h2 h1 (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hd : q ^ 2 ∣ d := by
    have := Nat.dvd_sub h2 h1
    rwa [show X + (i + d) - (X + i) = d by omega] at this
  have : d < q ^ 2 := by nlinarith
  have := Nat.eq_zero_of_dvd_of_lt hd this
  omega

/-- **Every word of residues occurs among consecutive squarefree numbers.** For every word
`w 0, …, w (L - 1)` of residues mod `4` with `w t ≢ 0 (mod 4)` and every `N` there is `k ≥ N`
with `squarefreeNth (k + t) ≡ w t (mod 4)` for all `t < L`.

Proof: let `K = 4 L + 2` and `G = (K !) ^ 2`, and place the candidates at `M + f t`,
`f t = t G + (w t mod 4)`. By the Chinese remainder theorem choose `M ≡ 0 (mod G)` and, for every
other offset `j` of the window `[0, (L + 1) G)`, `M + j ≡ 0 (mod q_j ^ 2)` with distinct primes
`q_j` beyond the window. Then the only possible squarefree numbers in the window are the
candidates; a candidate is never divisible by `p ^ 2` for `p ≤ K` (it is `≡ w t (mod p ^ 2)`)
nor for `p = q_j`; and along the progression of admissible `M` the union bound over the primes
`p > K` (`card_filter_not_squarefree_le`) leaves at most half of the `M` with a non-squarefree
candidate. -/
theorem exists_squarefreeNth_mod_four_eq (L N : ℕ) (w : ℕ → ℕ) (hw : ∀ t < L, w t % 4 ≠ 0) :
    ∃ k, N ≤ k ∧ ∀ t < L, squarefreeNth (k + t) % 4 = w t % 4 := by
  -- The shape of the window.
  set K := 4 * L + 2 with hK
  set G := (K !) ^ 2 with hG
  have hGpos : 0 < G := by positivity
  have hG4 : 4 ∣ G := by
    rw [hG, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow_of_dvd (Nat.dvd_factorial two_pos (by omega)) 2
  have hG4' : 4 ≤ G := Nat.le_of_dvd hGpos hG4
  set f : ℕ → ℕ := fun t ↦ t * G + w t % 4 with hf
  set W := L * G + G with hW
  have hfmono : StrictMono f := by
    intro s t hst
    have h1 : w s % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h2 : s * G + G ≤ t * G := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hst
    simp only [hf]
    omega
  have hfW : ∀ t < L, f t < W := by
    intro t ht
    have h1 : w t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h2 : t * G + G ≤ L * G := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht
    simp only [hf, hW]
    omega
  -- The excluded offsets and their primes.
  set E := range W \ (range L).image f with hE
  set q : ℕ → ℕ := fun j ↦ nth Nat.Prime (W + K + 1 + j) with hq
  have hqprime (j : ℕ) : (q j).Prime := nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have hqbig (j : ℕ) : W + K < q j :=
    Nat.lt_of_lt_of_le (by omega) (nth_strictMono Nat.infinite_setOfPred_prime).le_apply
  have hqinj : Injective q := fun i j h ↦ by
    have := nth_injective Nat.infinite_setOfPred_prime h
    omega
  have hGq (j : ℕ) : Coprime G (q j) := by
    refine (Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd (hqprime j)).2
      fun h ↦ ?_)).symm
    have := (Nat.Prime.dvd_factorial (hqprime j)).1 h
    have := hqbig j
    omega
  -- The Chinese remainder theorem.
  set s : Option ℕ → ℕ := fun o ↦ o.elim G fun j ↦ q j ^ 2 with hs
  set a : Option ℕ → ℕ := fun o ↦ o.elim 0 fun j ↦ q j ^ 2 - j with ha
  have hs0 : ∀ o ∈ insertNone E, s o ≠ 0 := by
    rintro (_ | j) -
    · exact hGpos.ne'
    · exact pow_ne_zero 2 (hqprime j).ne_zero
  have hpp : Set.Pairwise (insertNone E : Set (Option ℕ)) (Coprime on s) := by
    rintro (_ | i) - (_ | j) - hij
    · exact absurd rfl hij
    · exact Nat.Coprime.pow_right 2 (hGq j)
    · exact (Nat.Coprime.pow_right 2 (hGq i)).symm
    · have hij' : i ≠ j := fun h ↦ hij (by rw [h])
      exact Nat.Coprime.pow 2 2 ((Nat.coprime_primes (hqprime i) (hqprime j)).2 (hqinj.ne hij'))
  obtain ⟨a₀, ha₀⟩ := chineseRemainderOfFinset a s (insertNone E) hs0 hpp
  set Q := ∏ o ∈ insertNone E, s o with hQdef
  have hQ : Q = G * ∏ j ∈ E, q j ^ 2 := prod_insertNone _ _
  have hQpos : 0 < Q := by
    rw [hQ]
    exact Nat.mul_pos hGpos (prod_pos fun j _ ↦ pow_pos (hqprime j).pos 2)
  have hGQ : G ∣ Q := hQ ▸ dvd_mul_right _ _
  have hqQ : ∀ j ∈ E, q j ^ 2 ∣ Q := fun j hj ↦ hQ ▸ dvd_mul_of_dvd_right (dvd_prod_of_mem _ hj) _
  have hGa : G ∣ a₀ := Nat.modEq_zero_iff_dvd.1 (ha₀ none (by simp))
  have hqa : ∀ j ∈ E, q j ^ 2 ∣ a₀ + j := by
    intro j hj
    have hjW : j < W := by simp only [hE, Finset.mem_sdiff, mem_range] at hj; exact hj.1
    have hj' : j < q j ^ 2 := by nlinarith [hqbig j]
    have h := Nat.ModEq.add_right j (ha₀ (some j) (by simpa using hj))
    simp only [ha, Option.elim, Nat.sub_add_cancel hj'.le] at h
    exact Nat.modEq_zero_iff_dvd.1 (h.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
  -- Excluded offsets are never squarefree.
  have hexcl (m : ℕ) (j : ℕ) (hj : j ∈ E) : q j ^ 2 ∣ a₀ + Q * m + j := by
    rw [show a₀ + Q * m + j = (a₀ + j) + Q * m by ring]
    exact dvd_add (hqa j hj) (dvd_mul_of_dvd_left (hqQ j hj) m)
  -- Sieve hypotheses for the candidates.
  have hsieve (t : ℕ) (ht : t < L) (m p : ℕ) (hp : p.Prime) (hpd : p ^ 2 ∣ a₀ + f t + Q * m) :
      K < p ∧ Coprime (p ^ 2) Q := by
    have hK' : K < p := by
      by_contra hle
      push Not at hle
      have hpG : p ^ 2 ∣ G := pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hle) 2
      have hbase : p ^ 2 ∣ a₀ + Q * m + t * G :=
        dvd_add (dvd_add (hpG.trans hGa) (dvd_mul_of_dvd_left (hpG.trans hGQ) m))
          (dvd_mul_of_dvd_right hpG t)
      have hd : p ^ 2 ∣ w t % 4 := by
        refine (Nat.dvd_add_right hbase).1 ?_
        rw [show a₀ + Q * m + t * G + w t % 4 = a₀ + f t + Q * m by simp only [hf]; ring]
        exact hpd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero (hw t ht)) hd
      have : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
      have : w t % 4 < 4 := Nat.mod_lt _ (by norm_num)
      omega
    refine ⟨hK', Nat.Coprime.pow_left 2 ?_⟩
    rw [hQ]
    refine Nat.Coprime.mul_right ?_ (Nat.Coprime.prod_right fun j hj ↦ ?_)
    · refine Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦ ?_)
      have := (Nat.Prime.dvd_factorial hp).1 h
      omega
    · refine Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp (hqprime j)).2 fun hpq ↦ ?_)
      have hjW : j < W ∧ j ∉ (range L).image f := by
        simpa only [hE, Finset.mem_sdiff, mem_range] using hj
      have h1 := hexcl m j hj
      have h2 : q j ^ 2 ∣ a₀ + Q * m + f t := by
        rw [← hpq, show a₀ + Q * m + f t = a₀ + f t + Q * m by ring]
        exact hpd
      have := eq_of_sq_dvd_add_of_sq_dvd_add (hqbig j |>.trans_le' (by omega)) hjW.1
        (hfW t ht) h1 h2
      exact hjW.2 (mem_image.2 ⟨t, mem_range.2 ht, this.symm⟩)
  -- Choose the length `Y` of the progression.
  set N' := nth (Squarefree : ℕ → Prop) N with hN'
  set D := a₀ + W with hD
  set c := 2 * N' + 2 * L * (D + 1) with hc
  set H := 2 * L * Q + c + 1 with hH
  set Y := Q * (H * H) with hY
  set B := Nat.sqrt (a₀ + Q * Y + W) + 1 with hB
  have hBle : B ≤ Q * H + D + 1 := by
    have : a₀ + Q * Y + W ≤ (Q * H + D) ^ 2 := by
      rw [hY, hD]
      nlinarith [Nat.zero_le (Q * H * (a₀ + W)), Nat.le_self_pow (n := 2) two_ne_zero (a₀ + W)]
    have := Nat.sqrt_le_sqrt this
    rw [Nat.sqrt_eq'] at this
    omega
  have hYbig : 2 * N' + 2 * L * B < Y := by
    have e1 : H * H = H * (2 * L * Q) + H * c + H := by rw [hH]; ring
    have e2 : c ≤ H * c := Nat.le_mul_of_pos_left c (by omega)
    have e3 : H * H ≤ Q * (H * H) := Nat.le_mul_of_pos_left _ hQpos
    have e4 : 2 * L * B ≤ 2 * L * (Q * H + D + 1) := Nat.mul_le_mul_left _ hBle
    have e5 : 2 * L * (Q * H + D + 1) = H * (2 * L * Q) + 2 * L * (D + 1) := by ring
    omega
  -- The sieve along the progression `a₀ + f t + Q m`, `m < Y`.
  have hbad (t : ℕ) (ht : t < L) :
      (#{m ∈ range Y | ¬ Squarefree (a₀ + f t + Q * m)} : ℝ) ≤ Y * (2 / (K + 1)) + B := by
    refine card_filter_not_squarefree_le fun m hm p hp hpd ↦ ?_
    obtain ⟨h1, h2⟩ := hsieve t ht m p hp hpd
    refine ⟨h1, ?_, h2⟩
    have hpos : 0 < a₀ + f t + Q * m := by
      have := hw t ht
      simp only [hf]
      omega
    have hle : p ^ 2 ≤ a₀ + Q * Y + W := by
      refine (Nat.le_of_dvd hpos hpd).trans ?_
      have := hfW t ht
      have : Q * m ≤ Q * Y := Nat.mul_le_mul_left _ hm.le
      omega
    have := Nat.le_sqrt'.2 hle
    omega
  obtain ⟨m, hmN, hmY, hgood⟩ :
      ∃ m, N' ≤ m ∧ m < Y ∧ ∀ t < L, Squarefree (a₀ + f t + Q * m) := by
    by_contra hcon
    push Not at hcon
    have hsub : Ico N' Y ⊆
        (range L).biUnion fun t ↦ {m ∈ range Y | ¬ Squarefree (a₀ + f t + Q * m)} := by
      intro m hm
      rw [mem_Ico] at hm
      obtain ⟨t, ht, hnt⟩ := hcon m hm.1 hm.2
      simp only [mem_biUnion, mem_range, mem_filter]
      exact ⟨t, ht, hm.2, hnt⟩
    have h1 : ((Y - N' : ℕ) : ℝ) ≤ ∑ t ∈ range L,
        (#{m ∈ range Y | ¬ Squarefree (a₀ + f t + Q * m)} : ℝ) := by
      rw [← Nat.card_Ico]
      exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    have h2 : ∑ t ∈ range L, (#{m ∈ range Y | ¬ Squarefree (a₀ + f t + Q * m)} : ℝ) ≤
        L * (Y * (2 / (K + 1)) + B) := by
      calc _ ≤ ∑ _t ∈ range L, (Y * (2 / (K + 1)) + B : ℝ) :=
            sum_le_sum fun t ht ↦ hbad t (mem_range.1 ht)
        _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
    have h3 : (L : ℝ) * (Y * (2 / (K + 1))) ≤ Y / 2 := by
      have hK1 : (K : ℝ) + 1 = 4 * L + 3 := by rw [hK]; push_cast; ring
      rw [hK1]
      have : (L : ℝ) * (2 / (4 * L + 3)) ≤ 1 / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      nlinarith [(Nat.cast_nonneg Y : (0 : ℝ) ≤ Y)]
    have h4 : ((2 * N' + 2 * L * B : ℕ) : ℝ) < Y := by exact_mod_cast hYbig
    have h5 : ((Y - N' : ℕ) : ℝ) = Y - N' := by
      rw [Nat.cast_sub (by omega)]
    push_cast at h4
    rw [h5] at h1
    nlinarith
  -- The window `[M, M + W)` with `M = a₀ + Q m`.
  set M := a₀ + Q * m with hM
  have hpos (t : ℕ) (ht : t < L) : Squarefree (M + f t) := by
    rw [show M + f t = a₀ + f t + Q * m by ring]
    exact hgood t ht
  have honly (j : ℕ) (hj : j < W) (hsq : Squarefree (M + j)) : ∃ s < L, f s = j := by
    by_contra hne
    push Not at hne
    have hjE : j ∈ E := by
      simp only [hE, Finset.mem_sdiff, mem_range, mem_image, not_exists, not_and]
      exact ⟨hj, fun s hs ↦ hne s hs⟩
    exact (Nat.squarefree_iff_prime_squarefree.1 hsq) (q j) (hqprime j)
      (by rw [← sq]; exact hexcl m j hjE)
  refine ⟨count (Squarefree : ℕ → Prop) M, ?_, fun t ht ↦ ?_⟩
  · calc N = count (Squarefree : ℕ → Prop) N' :=
          (count_nth_of_infinite infinite_setOf_squarefree N).symm
      _ ≤ count (Squarefree : ℕ → Prop) M := count_monotone _
          (hmN.trans ((Nat.le_mul_of_pos_left m hQpos).trans (Nat.le_add_left _ _)))
  · rw [squarefreeNth, nth_count_add_eq_of_window hfmono hfW hpos honly ht]
    obtain ⟨x, hx⟩ : 4 ∣ M + t * G :=
      dvd_add (dvd_add (hG4.trans hGa) (dvd_mul_of_dvd_left (hG4.trans hGQ) m))
        (dvd_mul_of_dvd_right hG4 t)
    have : M + f t = 4 * x + w t % 4 := by rw [← hx]; simp only [hf]; ring
    omega

end Nat

namespace Nat

/-- **Squarefree residue digits are not eventually periodic.** If a digit rule `g` takes
different values at two nonzero residues `r₁, r₂` mod `4`, then `k ↦ g (uₖ mod 4)` is not
eventually periodic: it has arbitrarily late runs of the value `g r₁` of every length
(`exists_squarefreeNth_mod_four_eq` with a constant word) and takes the value `g r₂` arbitrarily
late. -/
theorem not_eventuallyPeriodic_squarefreeNth_mod_four {α : Type*} (g : ℕ → α) {r₁ r₂ : ℕ}
    (h₁ : r₁ % 4 ≠ 0) (h₂ : r₂ % 4 ≠ 0) (hg : g (r₁ % 4) ≠ g (r₂ % 4)) {P : ℕ} (hP : 0 < P) :
    ¬ EventuallyPeriodic (fun k ↦ g (squarefreeNth k % 4)) P := by
  refine not_eventuallyPeriodic_of_runs (v := g (r₁ % 4)) (fun L N ↦ ?_) (fun N ↦ ?_) hP
  · obtain ⟨k, hk, hw⟩ := exists_squarefreeNth_mod_four_eq L N (fun _ ↦ r₁) fun _ _ ↦ h₁
    exact ⟨k, hk, fun i hi ↦ by simp only [hw i hi]⟩
  · obtain ⟨k, hk, hw⟩ := exists_squarefreeNth_mod_four_eq 1 N (fun _ ↦ r₂) fun _ _ ↦ h₂
    refine ⟨k, hk, ?_⟩
    have := hw 0 one_pos
    rw [add_zero] at this
    simp only [this]
    exact hg.symm

end Nat

namespace Real

open Nat

/-- **Squarefree residue constants are irrational.** For a base `b ≥ 2` and a digit rule `g`
with values `< b` that separates two nonzero residues mod `4`, the number
`∑ₖ g (uₖ mod 4) / b ^ (k + 1)` is irrational, where `uₖ` is the `k`-th squarefree number. -/
theorem irrational_tsum_squarefreeNth_mod_four {b : ℕ} (hb : 2 ≤ b) (g : ℕ → ℕ)
    (hgb : ∀ r < 4, g r < b) {r₁ r₂ : ℕ} (h₁ : r₁ % 4 ≠ 0) (h₂ : r₂ % 4 ≠ 0)
    (hg : g (r₁ % 4) ≠ g (r₂ % 4)) :
    Irrational (∑' k : ℕ, (g (squarefreeNth k % 4) : ℝ) / b ^ (k + 1)) :=
  irrational_tsum_div_pow hb (fun _ ↦ hgb _ (Nat.mod_lt _ (by norm_num)))
    fun _ hP ↦ not_eventuallyPeriodic_squarefreeNth_mod_four g h₁ h₂ hg hP

/-- The **squarefree constant** `∑ₖ [uₖ ≡ 3 (mod 4)] / b ^ (k + 1)` (row 9 of
`research/sequences.md` in base `2`). -/
noncomputable def squarefreeConstant (b : ℕ) : ℝ :=
  ∑' k : ℕ, ((if squarefreeNth k % 4 = 3 then 1 else 0 : ℕ) : ℝ) / b ^ (k + 1)

/-- The squarefree constant is irrational in every base `b ≥ 2`. -/
theorem irrational_squarefreeConstant {b : ℕ} (hb : 2 ≤ b) : Irrational (squarefreeConstant b) :=
  irrational_tsum_squarefreeNth_mod_four hb (fun r ↦ if r = 3 then 1 else 0)
    (fun r _ ↦ by split_ifs <;> omega) (r₁ := 3) (r₂ := 1) (by norm_num) (by norm_num)
    (by norm_num)

/-- The base-`4` number `0.r₀ r₁ r₂ …` whose digits are the residues `rₖ = uₖ mod 4` of the
squarefree numbers is irrational. -/
theorem irrational_tsum_squarefreeNth_mod_four_div_four_pow :
    Irrational (∑' k : ℕ, ((squarefreeNth k % 4 : ℕ) : ℝ) / 4 ^ (k + 1)) := by
  have := irrational_tsum_squarefreeNth_mod_four (b := 4) (by norm_num) id (fun r hr ↦ hr)
    (r₁ := 1) (r₂ := 2) (by norm_num) (by norm_num) (by norm_num)
  simpa using this

end Real
