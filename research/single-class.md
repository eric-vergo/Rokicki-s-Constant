# A single residue class of primes (Direction 4)

**Status.** Formalized, `sorry`-free, standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), in `RokickiConstant/General/SingleClass.lean` (about 900 lines). No prime number
theorem, and no information about zeros of `L`-functions, is used.

**Theorem (single-class theorem).** Let `q ≥ 3`, let `a` be coprime to `q`, and let
`p_0 = 2 < p_1 = 3 < …` be the primes. Then the digit sequence `d_k = [p_k ≡ a (mod q)]` is not
eventually periodic, for any period `P > 0`. Consequently, for every base `b ≥ 2`,

    classConstant q a b = Σ_k [p_k ≡ a (mod q)] / b^(k+1)

is irrational.

```lean
theorem Nat.not_eventuallyPeriodic_nthPrime_modEq {q a : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q)
    {P : ℕ} (hP : 0 < P) :
    ¬ Function.EventuallyPeriodic (fun k ↦ if Nat.nth Nat.Prime k % q = a % q then 1 else 0) P

noncomputable def Real.classConstant (q a b : ℕ) : ℝ :=
  ∑' k : ℕ, (if Nat.nth Nat.Prime k % q = a % q then (1 : ℝ) else 0) / b ^ (k + 1)

theorem Real.irrational_classConstant {q a b : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hb : 2 ≤ b) :
    Irrational (Real.classConstant q a b)
```

**Rokicki's constant.** For `q = 4`, `a = 3`, `b = 2` the digit of `p_0 = 2` is `0`, and the
remaining digits are Rokicki's digits `[p_{k+1} ≡ 3 (mod 4)]` shifted by one place, so
`classConstant 4 3 2 = ρ / 2` (`Real.classConstant_four_three_two`). This gives a third proof
that `ρ` is irrational (`Real.irrational_rokickiConstant''`).

## 1. What is proved (Lean names)

Notation: `φ = φ(q)`, `u` is the unit `a mod q`, `1` is the principal character mod `q`, `χ`
runs over the nonprincipal characters (`nonprincipal q`), `G_χ(s) = Σ_k χ(p_k) p_k^{-s}`
(`primePart`), `H_χ` the prime-power part of `log L(s, χ)` (`primePowerPart`).

| Statement | Lean (namespace `DirichletCharacter` unless marked) |
|---|---|
| Orthogonality `Σ_χ χ(u⁻¹)χ(n) = φ[n = u]`, and its nonprincipal form | `sum_apply_inv_mul_apply`, `sum_nonprincipal_apply_inv_mul_apply` |
| Class series `Σ_k [p_k ≡ r] p_k^{-σ}`; every series with coefficients depending on `p_k mod q` is a finite combination of them | `classSeries`, `tsum_apply_mul_cpow_eq_sum` |
| **Dirichlet density** (PNT-free): `φ Σ_{p ≡ r} p^{-σ} − Σ_{p∤q} p^{-σ} = O(1)` on `1 < σ ≤ 2`, for every unit `r` | `exists_norm_classSeries_sub_primePart_one_le` |
| `Σ_{p∤q} p^{-σ} = log(1/(σ−1)) + O(1)` as `σ → 1⁺` | `exists_norm_primePart_one_add_log_le` |
| `H_χ(s) = G_{χ²}(2s)/2 + tailPart χ 3 s` on `re s > 1/2` | `primePowerPart_eq_primePart_sq_add_tailPart` |
| `#{r mod q : r² = u}` is even for `q ≥ 3` | `even_card_sq_eq` |
| `χ(v)` is an algebraic integer for a unit `v` | `isIntegral_apply_unit` |
| `n/2` is not an algebraic integer for odd `n` | `Complex.not_isIntegral_intCast_div_two` |
| bounded `a_k` with `Σ a_k p_k^{-σ}` bounded on `(1,2]` cannot have partial sums `c n + O(1)`, `c ≠ 0` | `not_exists_abs_sum_sub_mul_le_of_abs_tsum_le` (root) |
| `‖y log(σ − s₀)‖ = O(1)` as `σ → s₀⁺` forces `y = 0` | `Complex.eq_zero_of_eventually_norm_mul_log_le` |
| **Orders of vanishing**: if `(Π f_i) Φ' = Σ c_i f_i' Π_{j≠i} f_j` right of a real `s₀`, with `f_i` analytic and not locally zero at `s₀`, then `Φ(σ) = (Σ c_i m_i) log(σ − s₀) + O(1)`, `m_i = ord_{s₀} f_i` | `Complex.exists_norm_sub_mul_log_le_of_prod_mul_deriv_eq` |
| weight `e(n) = [n = u] − 1(n)/φ`; `φ e(n) = Σ_{χ≠1} χ(u⁻¹)χ(n)` | `classWeight`, `totient_mul_classWeight` |
| `Φ = φ·(Abel series of e(p_k)) + Σ_{χ≠1} χ(u⁻¹) H_χ`; holomorphic on `re s > 1/2` under bounded partial sums; `= Σ χ(u⁻¹) log L(s,χ)` on `re s > 1` | `classLog`, `differentiableOn_classLog`, `classLog_eq` |
| `(Π L(s,χ)) Φ'(s) = Σ_χ χ(u⁻¹) L'(s,χ) Π_{ψ≠χ} L(s,ψ)` on `re s > 1/2` | `prod_mul_deriv_classLog` |
| `Φ(σ) + ((ν−1)/2) log(σ − 1/2) = O(1)` as `σ → 1/2⁺` | `exists_norm_classLog_add_mul_log_le` |
| **Analytic form**: `Σ_{k<n} ([p_k ≡ u] − [p_k ∤ q]/φ)` is unbounded | `not_exists_norm_sum_classWeight_le` |
| **Single-class theorem** | `Nat.not_eventuallyPeriodic_nthPrime_modEq` |
| irrationality in every base; `ρ = 2·classConstant 4 3 2` | `Real.irrational_classConstant`, `Real.classConstant_four_three_two`, `Real.irrational_rokickiConstant''` |

## 2. The proof

Suppose `d` is eventually periodic. Put `e_k = d_k − [p_k ∤ q]/φ`. By orthogonality,

    φ e_k = Σ_{χ ≠ 1} χ(u⁻¹) χ(p_k).                                              (1)

**Step 1: the partial sums of `e` are bounded.** Periodicity gives `Σ_{k<n} d_k = c n + O(1)`,
and `[p_k ∤ q] = 1` for `k ≥ q`, so `Σ_{k<n} e_k = (c − 1/φ) n + O(1)`. By (1),
`Σ_k e_k p_k^{-σ} = φ⁻¹ Σ_{χ≠1} χ(u⁻¹) G_χ(σ)`, which is bounded on `1 < σ ≤ 2`
(`exists_norm_primePart_le` for each of the finitely many `χ`). Summation by parts against
`Σ_k p_k^{-σ} → ∞` forces `c = 1/φ`. This is the "Dirichlet density" input; it uses only
`L(1, χ) ≠ 0`.

**Step 2: continuation.** With bounded partial sums, the Abel series `A(s)` of `e_k` is
holomorphic on `re s > 0` and equals `Σ_k e_k p_k^{-s}` on `re s > 1`. Then

    Φ(s) = φ A(s) + Σ_{χ≠1} χ(u⁻¹) H_χ(s)

is holomorphic on `re s > 1/2` and equals `Σ_{χ≠1} χ(u⁻¹) ℓ_χ(s)` on `re s > 1`, where
`exp ℓ_χ = L(·, χ)`. The weights `χ(u⁻¹)` are complex, so `exp Φ` is not a product of
`L`-functions; instead differentiate: `ℓ_χ' = L_χ'/L_χ` on `re s > 1`, so

    (Π_χ L_χ) Φ' = Σ_χ χ(u⁻¹) L_χ' Π_{ψ≠χ} L_ψ                                  (2)

on `re s > 1`, and both sides are holomorphic on `re s > 1/2`: by the identity theorem (2)
holds on `re s > 1/2`. No information about zeros in the strip is needed.

**Step 3: the `L` side at `1/2`.** Each `L_χ` is entire and not identically zero
(`L(2, χ) ≠ 0`), so near `1/2`, `L_χ(s) = (s − 1/2)^{m_χ} g_χ(s)` with `g_χ(1/2) ≠ 0`. On a
punctured right neighbourhood of `1/2` all `L_χ(σ) ≠ 0`, and (2) gives
`Φ'(σ) = x/(σ − 1/2) + B(σ)` with `B` bounded and

    x = Σ_{χ≠1} χ(u⁻¹) m_χ.

The mean value inequality gives `Φ(σ) = x log(σ − 1/2) + O(1)` as `σ → 1/2⁺` (complex `O(1)`).

**Step 4: the prime-square side at `1/2`.** Split `H_χ(σ) = ½ G_{χ²}(2σ) + (terms p^m, m ≥ 3)`;
the latter, and `A`, are continuous at `1/2`. By (1) applied to `p²`,

    Σ_{χ≠1} χ(u⁻¹) G_{χ²}(t) = φ Σ_{p² ≡ u} p^{-t} − Σ_{p∤q} p^{-t}.

Let `ν = #{r mod q : r² = u}`. For `p ∤ q`, `p² ≡ u` iff `p` lies in one of the `ν` classes
`r`, so by Dirichlet density (Step 1 for each class `r`) the right side is
`(ν − 1) Σ_{p∤q} p^{-t} + O(1)` for `t ∈ (1, 2]`. Finally `Σ_{p∤q} p^{-t} = log(1/(t−1)) + O(1)`:
`exp(G_1 + H_1) = L(·, 1)`, `H_1` is bounded, and `(t − 1) L(t, 1) → Π_{p|q}(1 − 1/p) ≠ 0`
(Mathlib's `LFunctionTrivChar_residue_one`). With `t = 2σ`:

    Φ(σ) = −((ν − 1)/2) log(σ − 1/2) + O(1)        (σ → 1/2⁺),

again with a complex `O(1)`: the singular term is real.

**Step 5: integrality.** Comparing Steps 3 and 4, `(x + (ν−1)/2) log(σ − 1/2) = O(1)`, so

    x = Σ_{χ≠1} χ(u⁻¹) m_χ = (1 − ν)/2.

The left side is an algebraic integer: each `χ(u⁻¹)` is a root of unity and each `m_χ ∈ ℕ`.
The right side is rational, hence would be an integer. But `ν` is even for `q ≥ 3` (the
involution `r ↦ −r` on the square roots of `u` has no fixed point, since `2r ≠ 0` for a unit
`r`), so `(1 − ν)/2 ∈ ½ + ℤ`. Contradiction. ∎

**The integrality twist: why zeros at `1/2` cannot save periodicity.** In the quadratic case
(`ρ`) the weight is `±χ/2` for one real `χ`, `exp Φ` is a power of `L(s, χ)`, and the
contradiction is a sign: the prime squares push `|L(σ, χ)|` to `+∞` while `L` is entire. With a
single class, the weights `χ(u⁻¹)` are complex and the sign argument is gone: a priori, zeros of
the `L(s, χ)` at `s = 1/2` could produce exactly the logarithmic singularity that the prime
squares demand. The proof shows they cannot, for arithmetic reasons: a zero of order `m_χ`
contributes `χ(u⁻¹) m_χ` to the coefficient of `log(σ − 1/2)`, an algebraic integer, whereas the
prime squares contribute `(1 − ν)/2`, a half odd integer. No configuration of zeros at `1/2`,
with any multiplicities, can match it. Zeros elsewhere never enter: (2) is used only near `1/2`.

**Deviations from the original plan.** (a) The conjugation symmetry `m_{χ̄} = m_χ`, planned to
show that `x` is real, is not needed: Step 4 holds with a complex `O(1)`, since the only
divergent term `(ν − 1) Σ_{p∤q} p^{-2σ}` is real, so the comparison gives `x = (1 − ν)/2`
directly, imaginary part included. (b) `log(1/(t − 1))` for `Σ_{p∤q} p^{-t}` comes from the pole
of `L(s, 1)` (whose Euler product is already in `primePart 1`), not from `ζ`. (c) The
orders-of-vanishing step is a general lemma about finite families of analytic functions
(`Complex.exists_norm_sub_mul_log_le_of_prod_mul_deriv_eq`).

## 3. Why this is new relative to the quadratic and cubic results

The earlier irrationality theorems (`irrational_tsum`, `irrational_tsum_of_pow_three`,
`irrational_residueConstant`) all need digits that *determine* the value `χ(p_k)` of one
character `χ` (quadratic or cubic), or the full residue `p_k mod q`. Periodic digits then give
periodic `χ(p_k)`, and the argument runs for that single `χ`. A single-class indicator determines
no character value: for `q = 7`, `a = 3`, knowing whether `p ≡ 3 (mod 7)` says nothing about
`χ(p)` for any `χ ≠ 1` mod `7` when `p ≢ 3`. The indicator is the combination (1) of all `φ − 1`
nonprincipal characters with complex weights, and the single-character arguments do not apply.
The new ingredients are the derivative identity (2) (so that complex weights are harmless), the
local orders of vanishing at `1/2`, and the integrality comparison.

It also contrasts with `research/sequences.md` §3.2. There, for `χ`-digits along a progression
of non-squares, the prime-square coefficient vanishes. Here it never does: the centring term
`−[p ∤ q]/φ` contributes `−½ Σ p^{-2σ}` for every class, and the coefficient `(ν − 1)/2` is a
half odd integer whether or not `a` is a square (`ν = 0` for non-squares, `x = 1/2`). The
complex-weight problem raised at the end of `sequences.md` §3.1 ("complex powers
`Π L(s, χψ)^{ψ̄(a)/φ(q)}` … needs `L(σ, χψ) ≠ 0` on `(1/2, 1)`") is solved by the same device:
work with `Φ'` and orders of vanishing at `1/2` only. (Whether this settles the twisted digits of
§3.1 for, e.g., `p ≡ 1 mod 5` has not been checked; the arithmetic of the coefficient is
different there.)

## 4. Corollaries

* **Every single-class constant** `Σ_k [p_k ≡ a (mod q)] b^{-(k+1)}`, `q ≥ 3`, `gcd(a, q) = 1`,
  `b ≥ 2`, is irrational (`Real.irrational_classConstant`).
* **Rokicki's constant** is the case `q = 4`, `a = 3`, `b = 2`, up to the factor `2`
  (`Real.classConstant_four_three_two`). Here `ν(3 mod 4) = 0` and the identity of Step 5 would
  read `−m_{χ₄} = 1/2`.
* **Residue constants** `Σ_k (p_k mod q) b^{-(k+1)}` (`Real.irrational_residueConstant`) also
  follow, since periodic residues give a periodic indicator of any class; that result was
  already proved through quadratic characters.
* For `q ≤ 2` the statement is false: `[p_k ≡ 1 (mod 2)]` is `0, 1, 1, 1, …`.

## 5. Unions of classes: the generalization and where it fails

Let `A` be a set of units mod `q` and `d_k = [p_k mod q ∈ A]`. The proof goes through verbatim
with the weight `e = [p ∈ A] − |A| [p ∤ q]/φ`, with `φ e(p) = Σ_{χ≠1} c_χ χ(p)`,
`c_χ = Σ_{a∈A} χ(a⁻¹)` (algebraic integers), and

    ν(A) = #{r mod q : r² ∈ A} = Σ_{a∈A} ν(a).

Steps 1–4 give, under eventual periodicity,

    Σ_{χ≠1} c_χ m_χ = (|A| − ν(A))/2.                                              (3)

Every `ν(a)` is even for `q ≥ 3`, so `ν(A)` is even, and:

* **`|A` odd: unconditional.** The right side of (3) is a half odd integer, the left an
  algebraic integer. So the indicator of any union of an *odd* number of unit classes is not
  eventually periodic, and the corresponding constants are irrational. (Not formalized; the Lean
  proof would replace `classWeight` by a sum over `A`. Note that `A` and its complement in the
  units have the same parity of size, since `φ` is even.)
* **`|A|` even, `ν(A) ≠ |A|`: conditional.** Then the right side of (3) is a nonzero integer,
  and zeros at `1/2` could, as far as the method sees, produce exactly that coefficient. The
  method proves: *if `L(1/2, χ) ≠ 0` for every nonprincipal `χ` mod `q` with `c_χ ≠ 0` (a case of
  Chowla's conjecture), then the indicator of `A` is not eventually periodic.* Some of these
  cases are settled unconditionally by other arguments. Example: `A` the quadratic non-residues
  mod an odd prime `ℓ` (`|A| = (ℓ−1)/2`, `ν(A) = 0`). For `ℓ ≡ 3 (mod 4)`, `|A|` is odd and the
  single-class method applies; for `ℓ ≡ 1 (mod 4)` it is only conditional, but `d_k` determines
  the Legendre symbol of `p_k`, and `Real.irrational_legendreConstant` settles it through one
  quadratic character, where the weights are real and the sign argument works.
* **`ν(A) = |A|`: no information.** Then (3) is consistent with no zeros at all, and the
  method gives nothing even conditionally. Example: `A = {1, 3}` mod `7` (`ν(1) = 2`, `ν(3) = 0`).
  Here the prime-square term cancels exactly, as for the non-square progressions of
  `sequences.md` §3.2, and Chebyshev's bias between the classes of `A` and the rest vanishes.

## 6. Numerical checks

`sympy`, the first `N = 10^5` primes (`p_N = 1 299 709`), `S(n) = #{k < n : p_k ≡ a (mod q)} − n/φ`.
The script runs in a few seconds:

```python
import sympy, math
N = 10**5
ps = list(sympy.primerange(2, sympy.prime(N) + 1))
for q, a in [(7, 3), (7, 2), (7, 1), (5, 2), (4, 3), (4, 1)]:
    phi = int(sympy.totient(q))
    nu = sum(1 for r in range(q) if math.gcd(r, q) == 1 and (r * r - a) % q == 0)
    c, S = 0, []
    for n, p in enumerate(ps, 1):
        c += p % q == a
        S.append(c - n / phi)
    print(q, a, nu, [S[10**j - 1] for j in (3, 4, 5)], max(S), min(S),
          sum(s > 0 for s in S) / N, sum(S) / N)
```

| `q` | `a` | `ν` | `x = (1−ν)/2` | `S(10³)` | `S(10⁴)` | `S(10⁵)` | `max S` | `min S` | `S > 0` | mean `S` |
|---|---|---|---|---|---|---|---|---|---|---|
| 7 | 3 | 0 | `1/2` | 1.33 | 11.33 | 18.33 | 46.8 | −11.2 | 91.2% | 12.9 |
| 7 | 2 | 2 | `−1/2` | −0.67 | −9.67 | −17.67 | 28.7 | −42.3 | 29.1% | −6.1 |
| 7 | 1 | 2 | `−1/2` | −1.67 | −5.67 | 10.33 | 31.5 | −49.8 | 17.3% | −11.6 |
| 5 | 2 | 0 | `1/2` | 5 | 9 | 16 | 40 | −14.8 | 90.4% | 13.0 |
| 4 | 3 | 0 | `1/2` | 4 | 15 | 50 | 78 | −4.5 | 99.5% | 33.6 |
| 4 | 1 | 2 | `−1/2` | −5 | −16 | −51 | 3.5 | −79 | 0.15% | −34.6 |

* **Sign bias.** For `q = 7`, `a = 3` (a non-residue, `ν = 0`), `S(n) > 0` for `91%` of
  `n ≤ 10^5`: the class `3 mod 7` is ahead of its share `1/6`. For the residues `1, 2 mod 7`
  (`ν = 2`) the bias is reversed. This is Chebyshev's bias, and its sign is the sign of `1 − ν`:
  the explicit formula gives `φ π(x; q, a) − π(x) ≈ (1 − ν(a)) √x / log x + (zeros)`. The same
  coefficient `(1 − ν)/2` drives Steps 4–5: the proof turns the term that causes Chebyshev's bias
  into the contradiction.
* **Size.** The heuristic `S(n) ≈ (1 − ν)/φ · √p_n / log p_n` gives `≈ 13.5` for `q = 7` at
  `n = 10^5` (`√p_n / log p_n ≈ 81`); the observed mean over `n ≤ 10^5` is `12.9`. For `q = 4`
  the heuristic gives `≈ 40`, observed mean `34`.
* **No periodicity, consistent with Step 1.** `S(n)` stays `O(√p_n)` in all cases, so the slope
  `c` of Step 1 is `1/φ` numerically, as Dirichlet density forces, and the theorem is genuinely
  about the `O(1)` level: bounded `S` is what Steps 2–5 exclude.
