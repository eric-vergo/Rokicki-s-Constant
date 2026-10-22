# The rate of equidistribution in one residue class (Direction 4, quantitative)

**Status.** Formalized, `sorry`-free, standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), in `RokickiConstant/General/SingleClassRate.lean` (about 720 lines). No prime number
theorem, and no information about zeros of `L`-functions, is used. Unions of an odd number of
classes are covered by the same theorems. The one-sided (sign) version is **not** formalized: it
is not a straightforward consequence of the method; see §4 for the precise (conditional) statement.

## 1. Statements

Notation: `q ≥ 3`, `a` coprime to `q`, `φ = φ(q)`, `p₀ = 2 < p₁ < …` the primes,

    π(x; q, a) = #{p < x : p ≡ a (mod q)},   π(x) = #{p < x}  (= Nat.primeCounting' x),
    E(n) = #{k < n : p_k ≡ a (mod q)} − n/φ.

**Theorem (single-class rate theorem).** For every class `a` coprime to `q ≥ 3`:

1. `E(n)` is not `O(n^θ)` for any `θ < 1/2`; equivalently no `C` has `|E(n)| ≤ C n^θ` for all `n`.
2. `π(x; q, a) − π(x)/φ` is not `O(x^θ)` for any `θ < 1/2`.
3. `π(x; q, a) − π(x)/φ` is not `O(√x / (log x)^β)` for any `β > 1`; equivalently, for every `C`,
   `|π(x; q, a) − π(x)/φ| > C √x/(log x)^β` for some `x ≥ 2` (in fact for arbitrarily large `x`).
4. `E(n)` is not `O(√n / (log n)^β)` for any `β > 1/2` (index scale, via Chebyshev).

In Landau's notation: `π(x; q, a) − π(x)/φ(q) = Ω(√x / (log x)^{1+ε})` for every `ε > 0`, and
`E(n) = Ω(√n/(log n)^{1/2+ε})`.

The same holds for a union `A` of unit classes with `|A|` odd, with `π(x)/φ` replaced by
`|A| π(x)/φ` and `n/φ` by `|A| n/φ`.

| Statement | Lean (root namespace unless marked; `DC` = `DirichletCharacter`) |
|---|---|
| 1, single class | `Nat.not_isBigO_card_nthPrime_modEq_sub_rpow`, `Nat.not_exists_abs_card_nthPrime_modEq_sub_le_rpow` |
| 2, single class | `Nat.not_isBigO_card_primesBelow_modEq_sub_rpow` |
| 3, single class | `Nat.not_isBigO_card_primesBelow_modEq_sub_rpow_div_log_rpow`, `Nat.not_exists_abs_card_primesBelow_modEq_sub_le_rpow_div_log_rpow` (`∀ x ≥ 2`) |
| 4, single class | `Nat.not_isBigO_card_nthPrime_modEq_sub_rpow_div_log_rpow`, `Nat.not_exists_abs_card_nthPrime_modEq_sub_le_rpow_div_log_rpow` (`∀ n ≥ 2`) |
| 1–4, odd unions | the same names with `mem` for `modEq`: `Nat.not_isBigO_card_nthPrime_mem_sub_rpow`, `Nat.not_exists_abs_card_nthPrime_mem_sub_le_rpow`, `Nat.not_isBigO_card_primesBelow_mem_sub_rpow`, `Nat.not_isBigO_card_primesBelow_mem_sub_rpow_div_log_rpow`, `Nat.not_exists_abs_card_primesBelow_mem_sub_le_rpow_div_log_rpow`, `Nat.not_isBigO_card_nthPrime_mem_sub_rpow_div_log_rpow`, `Nat.not_exists_abs_card_nthPrime_mem_sub_le_rpow_div_log_rpow` |
| the engine: multiplicity relation for any continuation `B` | `DC.sum_unionCoeff_mul_analyticOrderNatAt_eq_of_differentiableOn` |
| no continuation for odd `\|A\|` | `DC.not_exists_differentiableOn_of_odd` |
| prime scale, weight sums | `DC.not_exists_norm_sum_succ_unionWeight_le_nthPrime_rpow` (`θ < 1/2`), `DC.not_exists_norm_sum_succ_unionWeight_le_nthPrime_rpow_div_log_rpow` (`β > 1`) |
| prime scale, discrepancy | `DC.not_isBigO_unionDiscrepancy_succ_nthPrime_rpow`, `DC.not_isBigO_unionDiscrepancy_succ_nthPrime_rpow_div_log_rpow` |
| bookkeeping | `DC.unionDiscrepancy` (`E_A(n)`), `DC.norm_sum_unionWeight_le` (`‖Σ_{k<n} e(p_k)‖ ≤ \|E_A(n)\| + \|A\| q/φ`), `DC.card_primesBelow_mem_sub_eq` (`π_A(x) − \|A\|π(x)/φ = E_A(π(x))`), `DC.one_le_mul_rpow_div_log_rpow` |

Example of the main statement as formalized:

```lean
theorem Nat.not_isBigO_card_primesBelow_modEq_sub_rpow_div_log_rpow (hq : 3 ≤ q)
    (ha : a.Coprime q) {β : ℝ} (hβ : 1 < β) :
    ¬ (fun x : ℕ ↦ (#{p ∈ Nat.primesBelow x | p % q = a % q} : ℝ) -
      Nat.primeCounting' x / q.totient) =O[atTop]
        fun x : ℕ ↦ (x : ℝ) ^ (1 / 2 : ℝ) / Real.log x ^ β
```

**Classical context.** Classically, oscillation of `π(x; q, a) − π(x)/φ(q)` of size `√x/log x`
(and more, with `Ω±` and iterated logarithms) comes from the explicit formula together with the
existence of zeros of the `L(s, χ)` (off the line, giving larger oscillations, or on the line
`re s = 1/2`); Littlewood's theorem for `q = 4` is the prototype. The present result is weaker by a
factor `(log x)^ε` in the `x` scale but uses no zeros at all: zeros of the `L(s, χ)` enter only
through their orders at `s = 1/2`, and integrality shows they cannot cancel the prime-square
singularity. In the index scale (`n ≍ x/log x`) the statement `Ω(√n/(log n)^{1/2+ε})` is within
`(log n)^ε` of the conjectured true size `√n/√(log n)`.

## 2. The proof

It is exactly the single-class proof (`research/single-class.md`) with the bounded Abel series
replaced by a quantitative one. `SingleClass.lean` and `Unions.lean` state their pipeline for the
Abel series under *bounded* partial sums, so the core was re-stated, for unions, with an arbitrary
function `B` in place of the Abel series:

    Φ_B(s) = φ B(s) + Σ_{χ≠1} c_χ(A) primePowerPart χ s          (unionLogOf A B)

with three hypotheses on `B`: holomorphic on `re s > 1/2`; `φ B = Σ_{χ≠1} c_χ primePart χ` on
`re s > 1`; and `‖B(σ)‖` bounded as `σ → 1/2⁺`. These are all the single-class argument uses:

* `(Π L) Φ_B' = Σ c_χ L'_χ Π_{ψ≠χ} L_ψ` on `re s > 1/2` (identity theorem; `prod_mul_deriv_unionLogOf`);
* the `L` side: `Φ_B(σ) = (Σ c_χ m_χ) log(σ − 1/2) + O(1)` (Unions.lean's
  `Complex.exists_norm_sub_mul_analyticOrderNatAt_log_le`, reused as is);
* the prime-square side: `Φ_B(σ) = −((ν(A) − |A|)/2) log(σ − 1/2) + O(1)`
  (`exists_norm_unionLogOf_add_mul_log_le`), from Unions.lean's per-unit
  `exists_norm_sum_primePowerPart_add_mul_log_le` (no Abel series involved there) plus the
  boundedness of `B`;
* hence `Σ_{χ≠1} c_χ m_χ = (|A| − ν(A))/2`, impossible for `|A|` odd by integrality
  (`not_exists_differentiableOn_of_odd`).

**Producing `B`.** With `B` the Abel series of `e(p_k) = [p_k ∈ A] − |A|[p_k ∤ q]/φ`:

* if `‖Σ_{j≤k} e(p_j)‖ ≤ C p_k^θ`, `θ < 1/2`: `B` is holomorphic on `re s > max θ 0`
  (`differentiableOn_abelSeries_of_le_rpow`), so continuous, hence bounded, at `1/2`;
* if `‖Σ_{j≤k} e(p_j)‖ ≤ C p_k^{1/2}/(log p_k)^β`, `β > 1`: `B` is holomorphic on `re s > 1/2`
  (the `θ = 1/2` bound) and `σ ↦ B(σ)` is continuous on `[1/2, 2]`
  (`continuousOn_abelSeries_of_le_rpow_div_log_rpow`, Bertrand), so bounded as `σ → 1/2⁺`;
* in both cases `B = Σ_k e(p_k) p_k^{-s}` on `re s > 1` (`abelSeries_eq_tsum_of_le_rpow`), and
  `φ Σ_k e(p_k)p_k^{-s} = Σ c_χ primePart χ s` (`totient_mul_tsum_unionWeight`).

**Bookkeeping.** `Σ_{k<n} e(p_k)` differs from `E_A(n)` by at most `|A| q/φ` (only `p_k | q` are
non-units, all with `k < q`). The bounded error is absorbed: for `θ` because `p_k^θ ≥ 1`; for the
log power because `(log x)^β ≤ (2β)^β √x` (from `log x ≤ x^ε/ε`). The `x` scale is reduced to the
index scale at the points `x = p_k + 1`, where `π_A(x) = #{j ≤ k : p_j ∈ A}` and `π(x) = k + 1`;
the index-scale log-power form loses `(log)^{1/2}` through Chebyshev's `k log p_k ≤ 5 p_k`,
`log p_k ≤ 2 log k` (Landau.lean's `rpow_div_log_rpow_le_nthPrime`), whence `β > 1/2`. Single
classes are the unions `A = {a}` (`|A| = 1` odd).

## 3. Unions

Done in the same file: every statement holds for `A` a set of units with `|A|` odd (the
refactoring was clean because Unions.lean already isolates the per-unit prime-square asymptotics).
For `|A|` even the method is conditional exactly as in `research/unions.md` §T2: the analogue of
`not_exists_differentiableOn_of_odd` holds under `L(1/2, χ) ≠ 0` for the `χ` with `c_χ ≠ 0`, when
`ν(A) ≠ |A|` (not formalized here; it would combine
`sum_unionCoeff_mul_analyticOrderNatAt_eq_of_differentiableOn` with the argument of
`DirichletCharacter.not_eventuallyPeriodic_of_re_unionCoeff`).

## 4. Why no sign, and the precise one-sided statement (next task)

The proof shows `|E|` is large, not in which direction. The obvious route to a sign is Landau's
theorem as in `General/Landau.lean`: assume `E ≤ C g` (or `≥ −C g`), `g(x) = √x/(log x)^β`,
apply Landau to the Mellin transform of the nonnegative function `h = C g − E` (or `E + C g`).
On the real axis `σ F_h(σ) = Γ(σ) ∓ φ^{-2}(Φ(σ) − Σ c_χ H_χ(σ)) + O(1)` with
`Φ = Σ_{χ≠1} χ(a⁻¹) log L(σ, χ)` (real for real `σ`) and `Γ` continuous on `[1/2, 2]`.

The prime-square coefficient has a fixed sign, as expected: `Σ c_χ H_χ(σ) = ((1 − ν)/2) log(σ −
1/2) + O(1)` with `1 − ν = 1` for non-squares and `≤ −1` for squares. **But the zeros do not.**
At a real point `σ₀ ∈ [1/2, 1)`, `Φ(σ) = x(σ₀) log(σ − σ₀) + O(1)` with

    x(σ₀) = Σ_{χ≠1} re χ(a⁻¹) · ord_{σ₀} L(s, χ),

and `re χ(a⁻¹)` takes both signs. (For `q = 7`, `a = 3`: `re χ(5) = 1/2, −1/2, −1, −1/2, 1/2` over
the five nonprincipal `χ`.) In the quadratic case of Landau.lean the weight is a single real
character with a fixed sign, so a real zero always pushes `log ‖L‖ → −∞`, in the helpful
direction; here a real zero of the "wrong" characters pushes `F_h → +∞`, which is consistent with a
positive measure, and the argument stops. At `σ₀ = 1/2` integrality excludes only the exact value
`x(1/2) = (1 − ν)/2`, not the wrong side of it (e.g. `L(1/2, χ) = L(1/2, χ̄) = 0` for the two
characters of order 6 mod 7 would give `x(1/2) = 1 > 1/2` for `a = 3`).

**Next task (precise statement, conditional).** Let `q ≥ 3`, `a` a unit, `ν = #{r : r² = a}`,
`β > 1`, `x(σ)` as above.

* *(non-squares, `ν = 0`)* If `x(σ₀) ≤ 0` for every real `σ₀ ∈ (1/2, 1)` and `x(1/2) < 1/2`, then
  for every `C`, `π(x; q, a) − π(x)/φ > C √x/(log x)^β` for arbitrarily large `x`.
* *(squares, `ν ≥ 2`)* If `x(σ₀) ≥ 0` for every real `σ₀ ∈ (1/2, 1)` and `x(1/2) > (1 − ν)/2`,
  then for every `C`, `π(x; q, a) − π(x)/φ < −C √x/(log x)^β` for arbitrarily large `x`.
* In particular both hold under the hypothesis `L(σ, χ) ≠ 0` for all nonprincipal `χ` mod `q` and
  all real `σ ∈ [1/2, 1)` (a finite check for each `q`, believed true, not available in Mathlib).
  That is the "Chebyshev bias towards non-residues" with no zeros off the real axis used.

Proof plan: copy `DirichletCharacter.IsQuadratic.not_exists_le_re_sum_succ_nthPrime_rpow_div_log_rpow`
with `primePart χ` replaced by `φ⁻¹ Σ_χ χ(a⁻¹) primePart χ` and the logarithm `E` of `L` replaced by
`Φ`; under the hypothesis, near every real `σ₀ ∈ (1/2, 1]` each `L(·, χ)` has a local logarithm
(the `ℓ` construction of Landau.lean, one per `χ`), so `F_h` continues across `σ₀` and Landau's
theorem forces the abscissa to be `1/2`, where the signed logarithm
`∓φ^{-2}(x(1/2) + (ν − 1)/2) log(σ − 1/2)` drives `σ F_h(σ) → −∞`. Unconditionally the same proof
gives a disjunction: either the one-sided bound fails, or some real `σ₀ ∈ [1/2, 1)` has `x(σ₀)` of
the wrong sign. Estimated 300–400 lines; not attempted, since the result is conditional.

## 5. Numerics

`sympy`, the first `N = 10^5` primes (`p_N = 1 299 709`), `q = 7`, `E(n)` as above.

```python
import sympy, math
N = 10**5
ps = list(sympy.primerange(2, sympy.prime(N) + 1))
q, phi = 7, 6
for a in (1, 3):
    c, best, bestx = 0, [0.0] * 5, [0.0] * 5
    for n, p in enumerate(ps, 1):
        c += p % q == a
        E = c - n / phi
        j = min(int(math.log10(n)), 4)
        best[j] = max(best[j], abs(E) / math.sqrt(n))
        if p > 2:
            bestx[j] = max(bestx[j], abs(E) / (math.sqrt(p) / math.log(p)))
    print(a, [round(b, 3) for b in best], [round(b, 3) for b in bestx])
```

`max |E(n)|/√n` over each decade `n ∈ [10^j, 10^{j+1})`, and `max |E(n)|/(√p_n/log p_n)`:

| decade of `n` | `a = 1` (`ν = 2`): `max \|E\|/√n` | `a = 3` (`ν = 0`): `max \|E\|/√n` | `a = 1`: `max \|E\|/(√p/log p)` | `a = 3`: `max \|E\|/(√p/log p)` |
|---|---|---|---|---|
| `[1, 10)` | 0.500 | 0.471 | 0.98 | 0.57 |
| `[10, 10²)` | 0.352 | 0.352 | 0.88 | 0.87 |
| `[10², 10³)` | 0.316 | 0.288 | 0.94 | 0.91 |
| `[10³, 10⁴)` | 0.273 | 0.205 | 0.93 | 0.70 |
| `[10⁴, 10⁵)` | 0.196 | 0.227 | 0.75 | 0.86 |

Signed extremes of `E(n)/(√p_n/log p_n)` and the proportion of `n` with `E(n) > 0`, per decade:

| decade | `a = 1`: min, max, `E > 0` | `a = 3`: min, max, `E > 0` |
|---|---|---|
| `[1, 10)` | −0.98, −0.08, 0% | −0.08, 0.57, 78% |
| `[10, 10²)` | −0.88, −0.07, 0% | −0.19, 0.87, 93% |
| `[10², 10³)` | −0.93, 0.18, 2% | −0.34, 0.91, 92% |
| `[10³, 10⁴)` | −0.93, 0.32, 2% | −0.21, 0.70, 88% |
| `[10⁴, 10⁵)` | −0.75, 0.40, 19% | −0.26, 0.86, 92% |

* `max |E(n)|/√n` decreases slowly across decades, as it should if `|E(n)| ≍ √n/√(log n)`
  (`1/√(log n)` drops from about `0.37` to `0.30` between `n = 10³` and `10⁵`), while
  `max |E|/(√p/log p)` stays of order `1`: the scale `√x/log x` of the explicit formula. The
  theorem's `√x/(log x)^{1+ε}` is just below that; `n^θ`, `θ < 1/2`, is far below.
* The sign bias is visible (the residue `1` stays below its share, the non-residue `3` above it),
  but, as §4 explains, the formalized theorem does not see it.

## 6. What is not done

* The one-sided version (§4), conditional on real zeros; not formalized.
* Even unions under `L(1/2, χ) ≠ 0` (§3), quantitative form; not formalized (routine from the
  engine).
* `Ω(√x/log x)` itself (the borderline `β = 1`): the method stops there, as in
  `research/oscillation.md` (the dominating series `Σ (p_{k+1} − p_k)/(p_k log p_k)` diverges).
