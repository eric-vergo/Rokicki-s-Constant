# Unions of residue classes of primes (Round 4, item 2: parity)

**Status.** Formalized, `sorry`-free, standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), in `RokickiConstant/General/Unions.lean` (about 1000 lines, built on
`General/SingleClass.lean`, which is not modified). No prime number theorem; no information on
zeros of `L`-functions except where a hypothesis says so explicitly.

Setting: `q ≥ 3`, `A` a set of units modulo `q` (a `Finset (ZMod q)` with `∀ a ∈ A, IsUnit a`),
`p_0 = 2 < p_1 < …` the primes, and the digit

    d_k = [p_k mod q ∈ A].

Notation: `φ = φ(q)`; `χ` runs over the nonprincipal characters mod `q`;
`c_χ(A) = Σ_{a∈A} χ(a⁻¹)` (`unionCoeff`); `m_χ = ord_{s=1/2} L(s, χ)`;
`ν(a) = #{r mod q : r² = a}` and `ν(A) = #{r mod q : r² ∈ A} = Σ_{a∈A} ν(a)`.

## 1. Results

**The multiplicity relation** (the engine; unconditional). If `d` is eventually periodic, then

    Σ_{χ≠1} c_χ(A) · m_χ = (|A| − ν(A)) / 2.                                        (R)

The left side is an algebraic integer, `ν(A)` is even, and the `m_χ` are nonnegative integers.
Everything below is read off from (R).

| | Statement | Lean |
|---|---|---|
| (R) | periodic `d` ⇒ `Σ_{χ≠1} c_χ m_χ = (|A| − ν(A))/2` | `DirichletCharacter.sum_unionCoeff_mul_analyticOrderNatAt_eq_of_eventuallyPeriodic` |
| **T1** | `|A|` odd ⇒ `d` not eventually periodic; `Σ_k d_k b^{-(k+1)}` irrational, every `b ≥ 2` | `Nat.not_eventuallyPeriodic_nthPrime_mem_of_odd`, `Real.irrational_unionConstant_of_odd` |
| **T2** | `ν(A) ≠ |A|` and `ChowlaHypothesis q` ⇒ same conclusion | `Nat.not_eventuallyPeriodic_nthPrime_mem_of_chowla`, `Real.irrational_unionConstant_of_chowla` |
| T2, sharp form | `ν(A) ≠ |A|` and `L(1/2, χ) ≠ 0` only for the `χ` with `re c_χ · (|A| − ν(A)) > 0` | `DirichletCharacter.not_eventuallyPeriodic_of_re_unionCoeff` |
| T2, `c_χ ≠ 0` form | `L(1/2, χ) ≠ 0` for the `χ` with `c_χ ≠ 0` | `DirichletCharacter.not_eventuallyPeriodic_of_LFunction_ne_zero` |
| **Positivity** (unconditional) | `ν(A) ≠ |A|` and `re c_χ · (ν(A) − |A|) ≥ 0` for all `χ ≠ 1` | `DirichletCharacter.not_eventuallyPeriodic_of_re_unionCoeff_mul_nonneg` |
| Pairs (unconditional) | `A = {1, a}`, `a ≠ 1` a unit with `ν(A) > 2` (e.g. `a` a square, or `ν(1) > 2` as mod 8) ⇒ not eventually periodic | `Nat.not_eventuallyPeriodic_nthPrime_mem_one_pair`, `…_one_pair_of_isSquare` |
| **T3** complement | `Aᶜ` = units not in `A` (`unitsCompl`); digit of `Aᶜ` is `1 − d_k` for `k ≥ q`, same periods; `|Aᶜ| + |A| = φ`; `ν(Aᶜ) + ν(A) = φ`; `|Aᶜ| ≡ |A| (mod 2)`; `|Aᶜ| − ν(Aᶜ) = −(|A| − ν(A))` | `eventuallyPeriodic_nthPrime_mem_unitsCompl_iff`, `card_unitsCompl_add_card`, `card_sq_mem_unitsCompl_add_card_sq_mem`, `even_card_unitsCompl_iff`, `card_unitsCompl_sub_card_sq_mem_unitsCompl` |
| `ν(A)` even | `q ≥ 3` | `even_card_sq_mem` (via `card_sq_mem_eq_sum` and `even_card_sq_eq`) |
| Hypothesis | `ChowlaHypothesis q : ∀ χ ≠ 1, LFunction χ (1/2) ≠ 0` | `DirichletCharacter.ChowlaHypothesis` |
| Examples mod 7 | `{1,2,4}`, `{1,2,3}` (T1); `{1,2}` (pairs); `{3,6}` (T2); `{1,3}`: `ν = |A|` | `Nat.not_eventuallyPeriodic_nthPrime_mod_seven_mem_squares`, `…_mem_one_two_three`, `…_mem_one_two`, `…_mem_three_six_of_chowla`, `card_sq_mem_one_three_mod_seven` |

`ChowlaHypothesis` is Chowla's conjecture (S. Chowla, *The Riemann hypothesis and Hilbert's tenth
problem*, 1965) at level `q`: `L(1/2, χ) ≠ 0` for every Dirichlet character. It is expected for all
`q`; it is open in general, verified numerically for small moduli, and known for a positive
proportion of characters (Iwaniec–Sarnak, Soundararajan for quadratic characters, and others).
Numerically, for `q = 5, 7, 8, 9, 12` all `L(1/2, χ)` are nonzero (§6), so every case of the
tables below is settled *numerically*; the point is what is settled *formally*.

T3 makes the classification complement-invariant: `A` and `Aᶜ` have the same digit up to
`d ↦ 1 − d` (from `k = q` on), the same parity of size (since `φ(q)` is even, `Nat.totient_even`),
and opposite defects `|A| − ν(A)`. So T1 covers exactly the classes `{A, Aᶜ}` with `|A|` odd, and
the rest of the method concerns `|A|` even.

## 2. The proof (what changes from the single class)

The single-class proof (`single-class.md` §2) goes through with `[n = u]` replaced by `[n ∈ A]`
and `1` by `|A|`:

* weight `e(n) = [n ∈ A] − |A| 1(n)/φ` (`unionWeight`), with `φ e(n) = Σ_{χ≠1} c_χ χ(n)`
  (`totient_mul_unionWeight`; orthogonality summed over `a ∈ A`, `sum_nonprincipal_unionCoeff_mul_apply`);
* Step 1 (Dirichlet density, slope `c = |A|/φ`): `exists_norm_sum_unionWeight_le`;
* Step 2: `Φ_A = φ·(Abel series of e(p_k)) + Σ_{χ≠1} c_χ H_χ` (`unionLog`), holomorphic on
  `re s > 1/2`, and `(Π L_χ) Φ_A' = Σ_χ c_χ L_χ' Π_{ψ≠χ} L_ψ` (`prod_mul_deriv_unionLog`);
* Step 3: `Φ_A(σ) = (Σ c_χ m_χ) log(σ − 1/2) + O(1)`. Here the orders `m_χ` must be identified
  (for T2), so `SingleClass`'s existential lemma is restated with `analyticOrderNatAt`
  (`Complex.exists_norm_sub_mul_analyticOrderNatAt_log_le`);
* Step 4: `Φ_A(σ) = −((ν(A) − |A|)/2) log(σ − 1/2) + O(1)`: the per-unit prime-square estimate
  (`exists_norm_sum_primePowerPart_add_mul_log_le`, the Abel-free half of
  `exists_norm_classLog_add_mul_log_le`) summed over `a ∈ A`
  (`exists_norm_unionLog_add_mul_log_le`);
* Step 5: compare (`sum_unionCoeff_mul_analyticOrderNatAt_eq`), giving (R).

Then: **T1** — `c_χ` is a sum of roots of unity (`isIntegral_unionCoeff`), so the left side of (R)
is an algebraic integer; the right side is `(odd)/2` (`Complex.not_isIntegral_intCast_div_two`).
**T2** — `L(1/2, χ) ≠ 0` gives `m_χ = 0` (`analyticOrderAt_eq_zero`), so (R) reads
`0 = (|A| − ν(A))/2`. **Positivity** — take real parts of (R):

    Σ_{χ≠1} re c_χ · m_χ = (|A| − ν(A))/2,     m_χ ≥ 0.                               (R_re)

If every `re c_χ` has the sign opposite to `|A| − ν(A)` (or is `0`), the left side cannot reach
the right side. More precisely only the characters with `re c_χ (|A| − ν(A)) > 0` can help, so
only their central values need to be nonzero (sharp T2). For `A = {1, a}`:
`re c_χ = 1 + re χ(a⁻¹) ≥ 0` for every `χ`, so positivity applies as soon as `ν(A) > 2 = |A|`
(`Nat.not_eventuallyPeriodic_nthPrime_mem_one_pair`); this holds when `a ≠ 1` is a square, since
`ν(A) = ν(1) + ν(a)` and each nonzero `ν` is even (`…_one_pair_of_isSquare`), and also whenever
`1` has more than two square roots (`q = 8, 12, 15, …`).

## 3. What is proved about central zeros, both directions

* **Odd `|A|`**: no configuration of zeros at `1/2` matters (integrality).
* **Even `|A|`, `ν(A) ≠ |A|`**, the converse direction, formalized as (R): *if* the digit of some
  such union were eventually periodic, then

      Σ_{χ≠1} (Σ_{a∈A} χ(a⁻¹)) · ord_{s=1/2} L(s, χ) = (|A| − ν(A))/2 ≠ 0,

  so some `L(1/2, χ)` vanishes, and the orders satisfy this exact linear relation (and its real
  part (R_re), so some `χ` with `re c_χ · (|A| − ν(A)) > 0` has `L(1/2, χ) = 0`). This is a
  curious link: a statement about a 0/1 digit expansion would produce a central zero of a
  Dirichlet `L`-function, with prescribed multiplicities.
* **`ν(A) = |A|`**: (R) reads `Σ c_χ m_χ = 0`, satisfied by `m ≡ 0`. The method is silent even
  under Chowla. This is exactly the case where Chebyshev's bias of `A` against its share
  vanishes (§6): the prime-square term cancels.

**Further reduction with conjugation symmetry (not formalized).** `L(s̄, χ̄) = conj L(s, χ)`, so
`m_χ̄ = m_χ`. Since `c_χ̄ = conj c_χ`, (R) becomes a relation between *real* algebraic integers
indexed by the classes `{χ, χ̄}`: `Σ_{χ real} c_χ m_χ + Σ_{pairs} 2 re c_χ · m_χ = (|A| − ν(A))/2`.
For `q = 5, 7, 8, 9, 12` all character values lie in `ℚ(i)` or `ℚ(√−3)`, so the weights are
integers, and the relation is a single linear Diophantine equation in nonnegative integers. For
real `χ` and even `|A|`, `c_χ = Σ_{a∈A} χ(a)` is even. This yields further parity obstructions
(below). Formalizing it needs `LFunction χ̄ (conj s) = conj (LFunction χ s)`, which is not in
Mathlib.

## 4. Tables: all proper unions up to complement

Status codes: **T1** (unconditional, `|A|` odd); **Pos** (unconditional, positivity,
formalized criterion); **Par** (unconditional *given* `m_χ̄ = m_χ`, by a parity obstruction; not
formalized); **Cond(χ)** (needs `L(1/2, χ) ≠ 0` for the listed characters); **silent**
(`ν(A) = |A|`). "Other route": single class (`|A| = 1` or `|Aᶜ| = 1`), quadratic
(`A` or `Aᶜ` the kernel of a real character, `IsQuadratic.irrational_tsum` with `f = [z = 1]`),
cubic (kernel of a cubic character, `irrational_tsum_of_pow_three`).
In the equations, `m₂, m₃, m₄, m₆` are the common orders of the characters of that order
(conjugates have equal order of vanishing).

**`q = 5`** (`φ = 4`, squares `{1, 4}`, `ν(a) = 2` on squares, `0` otherwise).

| `A` | `Aᶜ` | `|A|` | `ν(A)` | status | other route |
|---|---|---|---|---|---|
| `{a}` (4 sets) | 3 elements | 1 | 2 or 0 | T1 | single class |
| `{1, 4}` | `{2, 3}` | 2 | 4 | Pos: `2m₂ = −1` | quadratic |
| `{1, 2}` | `{3, 4}` | 2 | 2 | silent | – |
| `{1, 3}` | `{2, 4}` | 2 | 2 | silent | – |

**`q = 7`** (`φ = 6`, squares `{1, 2, 4}`; characters of orders 2, 3, 3, 6, 6). All 10 classes
with `|A| = 3` and the 6 single classes are T1. Note: `{1, 2, 4}` is the set of *quadratic*
residues; the *cubic* residues mod 7 are `{1, 6}`.

| `A` (`|A| = 2`) | `ν(A)` | (R) after `m_χ̄ = m_χ` | status | other route |
|---|---|---|---|---|
| `{1, 2}`, `{1, 4}` | 4 | `2m₂ + m₆ + m₃ = −1` | **Pos** (pairs theorem; `{1, 2}` stated as an example) | – |
| `{2, 4}` | 4 | `2m₂ − 2m₆ − 2m₃ = −1` | Par | – |
| `{3, 5}` | 0 | `−2m₂ + 2m₆ − 2m₃ = 1` | Par | – |
| `{3, 6}`, `{5, 6}` | 0 | `−2m₂ − m₆ + m₃ = 1` | Cond(cubic χ mod 7) | – |
| `{1, 6}` | 2 | – | silent | cubic |
| `{1, 3}`, `{1, 5}`, `{2, 3}`, `{2, 5}`, `{2, 6}`, `{3, 4}`, `{4, 5}`, `{4, 6}` | 2 | – | silent | – |

For `{3, 6}` the relation has the solution `m₃ = 1`, `m₂ = m₆ = 0`: periodicity of
`[p_k mod 7 ∈ {3, 6}]` would follow from nothing worse than simple zeros of the two cubic
`L(s, χ)` mod 7 at `1/2`, and conversely the sharp T2 needs only `L(1/2, χ) ≠ 0` for those two
characters (they are the `χ` with `re c_χ > 0`: `re c_χ = 1/2` for the cubic ones, `−1/2` for
the sextic ones, `−2` for the quadratic one). Numerically `L(1/2, χ_3) ≈ 0.310 ± 0.073 i ≠ 0`.

**`q = 8`** (`φ = 4`, all units square to `1`, `ν(1) = 4`) and **`q = 12`** (same structure).

| `A` | `|A|` | `ν(A)` | status | other route |
|---|---|---|---|---|
| `{a}` (4 sets) | 1 | 4 or 0 | T1 | single class |
| `{1, a}`, `a ≠ 1` (3 sets) | 2 | 4 | Pos: `2m_χ = −1` (pairs theorem, `ν(1) = 4`) | quadratic |

Here every even union is a quadratic kernel, and the pairs theorem reproves it.

(`q = 9`, for comparison: `{1, 4}`, `{1, 7}` Pos; `{2, 5}`, `{4, 7}` Par; `{2, 8}`, `{5, 8}`
Cond(cubic χ mod 9); the rest of the pairs silent; `|A|` odd T1.)

## 5. Specializations and comparison with the character routes

* **`A = {a}`**: `Nat.not_eventuallyPeriodic_nthPrime_modEq` (`SingleClass.lean`) is the case
  `|A| = 1` of T1; not re-proved.
* **Quadratic non-residues mod an odd prime `ℓ`**: `|A| = (ℓ−1)/2`, `ν(A) = 0`. For
  `ℓ ≡ 3 (mod 4)`, `|A|` is odd and T1 applies (`{3, 5, 6}` mod 7, `{2, 6, 7, 8, 10}` mod 11). For
  `ℓ ≡ 1 (mod 4)`, T1 does not apply, but positivity does: `c_χ = 0` unless `χ` is the Legendre
  character `λ`, where `c_λ = −(ℓ−1)/2`, so (R) reads `−((ℓ−1)/2) m_λ = (ℓ−1)/4`, impossible for
  `m_λ ≥ 0`. This agrees with `Real.irrational_legendreConstant` (all odd `ℓ`), whose proof is the
  same sign argument for the single real character `λ` (the digit there *is* a character digit).
  Not formalized via `Unions.lean` (needs the character sums over the non-residues).
* **Cubic residues mod `ℓ ≡ 1 (mod 3)`**: `|A| = (ℓ−1)/3` is always *even* (`ℓ ≡ 1 (mod 6)`), and
  `ν(A) = |A|` (if `r²` is a cube then `r = r³ · (r²)⁻¹` is a cube). Same for every coset of the
  cubes. So the union method is **silent** on all cubic-residue digits; these are covered instead
  by `irrational_tsum_of_pow_three` (digit `[χ(p) = 1]` for a cubic `χ`), since there the
  prime-cube term, not the prime-square term, carries the singularity. (The task statement's
  "`{1, 2, 4}` = cubic residues mod 7" is the quadratic residues; the cubic residues mod 7 are
  `{1, 6}`, `ν = |A| = 2`.)
* **Genuinely new cases**: unions that are not unions of fibres of one character, such as
  `{1, 2, 3}` mod 7 (T1, formalized) and `{1, 2}` mod 7 (Pos, formalized). No single character
  value is determined by these digits.

## 6. Numerics

`sympy`, first `N = 10^5` primes, `S(n) = Σ_{k<n} ([p_k ∈ A] − |A| [p_k ∤ q]/φ)`; prediction
from the explicit formula with the prime-square term, `S(n) ≈ ((|A| − ν(A))/φ) √p_n / log p_n`
(mean of `√p_n/log p_n` over `n ≤ N` is `55.4`). The script runs in about a second:

```python
import sympy, math
N = 10**5
ps = list(sympy.primerange(2, sympy.prime(N) + 1))
for q, A in [(7, {1, 2, 4}), (7, {1, 2, 3}), (7, {1, 2}), (7, {3, 6}), (7, {1, 3}), (5, {1, 2})]:
    phi = int(sympy.totient(q))
    nu = sum(1 for r in range(q) if (r * r) % q in A)
    c, S = 0.0, []
    for p in ps:
        c += (p % q in A) - (len(A) / phi if p % q else 0)
        S.append(c)
    print(q, sorted(A), len(A), nu, [S[10**j - 1] for j in (3, 4, 5)], max(S), min(S),
          sum(s > 0 for s in S) / N, sum(S) / N)
```

| `q` | `A` | `|A|` | `ν(A)` | status | `S(10³)` | `S(10⁴)` | `S(10⁵)` | `max S` | `min S` | `S > 0` | mean `S` | predicted mean |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 7 | `{1,2,4}` | 3 | 6 | T1 | −4.5 | −15.5 | −43.5 | 1.0 | −73.5 | ≈ 0% | −29.8 | −27.7 |
| 7 | `{1,2,3}` | 3 | 4 | T1 | −0.5 | −3.5 | 11.5 | 34.0 | −48.0 | 35.5% | −4.2 | −9.2 |
| 7 | `{1,2}` | 2 | 4 | Pos | −2.0 | −15.0 | −7.0 | 12.7 | −59.7 | 5.3% | −17.3 | −18.5 |
| 7 | `{3,6}` | 2 | 0 | Cond | 1.0 | 8.0 | 37.0 | 59.3 | −14.0 | 97.3% | 21.7 | 18.5 |
| 7 | `{1,3}` | 2 | 2 | silent | 0.0 | 6.0 | 29.0 | 58.0 | −36.0 | 45.7% | 1.7 | 0 |
| 5 | `{1,2}` | 2 | 2 | silent | 0.5 | −6.5 | −16.5 | 36.5 | −31.0 | 38.7% | −2.3 | 0 |

* The sign of the bias is the sign of `|A| − ν(A)`, the right side of (R), in every case; for the
  silent cases (`ν(A) = |A|`) there is no bias (mean near `0`, `S > 0` about half the time).
  The proof converts exactly this bias term into the contradiction, which is why it says nothing
  when the bias vanishes.
* Central values (`mpmath`, Hurwitz zeta): every `L(1/2, χ)`, `χ ≠ 1`, for `q = 5, 7, 8, 9, 12` is
  nonzero, e.g. mod 7: `1.147` (quadratic), `0.310 ± 0.073 i` (cubic), `0.714 ± 0.475 i`
  (sextic). So `ChowlaHypothesis q` holds numerically for these `q`, and all the
  Cond/Par entries above are settled numerically (not formally: the Lean statements keep the
  hypothesis).

## 7. Left open

* Formal conjugation symmetry `m_χ̄ = m_χ` (needs `LFunction χ̄ (conj s) = conj (LFunction χ s)`),
  which would upgrade the Par entries (e.g. `{2, 4}`, `{3, 5}` mod 7) to unconditional theorems.
* A formal criterion for which unions are settled unconditionally: (R) with `m_χ̄ = m_χ`, the
  Galois conjugates of (R) (the right side is rational, so `Σ_χ c_{χ^t} m_χ = (|A| − ν(A))/2` for
  every `t` prime to the exponent), and nonnegativity. This is an integer feasibility problem;
  where it is infeasible the union is settled unconditionally, where it is feasible (as for
  `{3, 6}` mod 7) the method needs central nonvanishing for specific characters.
* The silent unions (`ν(A) = |A|`, e.g. `{1, 3}` mod 7, `{1, 2}` mod 5, the cubic residues):
  no approach known here. The prime-square singularity is absent; a different singular term (as
  the prime cubes for cubic kernels) would be needed.
* Certified numerics for `L(1/2, χ) ≠ 0`, `q ≤ 12`, would make the conditional cases in the
  tables unconditional, but turning interval arithmetic for `L(1/2, χ)` into a Lean proof is
  a separate project.
