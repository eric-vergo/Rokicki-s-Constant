# Characters of higher order (Direction 1)

**Status.** Formalized, `sorry`-free, in `RokickiConstant/General/HigherOrder.lean`:

1. the linear case `S(n) = c·n + O(1)`, `c ≠ 0` complex, is impossible for **every** nonprincipal
   Dirichlet character;
2. for a character of **order 3**, the partial sums are unbounded, and even their real parts are;
3. for every order `m`, a *simultaneous* statement: the sums `S_{χ^j}` for `1 ≤ j ≤ m/2` are not
   all bounded;
4. the **cubic residue constants** (digit `k` records whether `p_k` is a cube modulo a prime
   `ℓ ≡ 1 (mod 3)`) are irrational, in every base.

For a single character of order `m ≥ 4` the method stops; section 4 says exactly where, what a
conditional version needs, and why non-squarefree orders such as `m = 4` are out of reach of the
method even conditionally.

Notation: `p_0 = 2 < p_1 < …` are the primes (`Nat.nth Nat.Prime`), `χ` is a Dirichlet character
modulo `q`, `S_χ(n) = Σ_{k<n} χ(p_k)`, `G_ψ(s) = Σ_k ψ(p_k) p_k^{-s}` (`primePart ψ s`), and for
`re s > 1`

    log L(s, χ) = Σ_{j≥1} G_{χ^j}(j s) / j.                                         (1)

## 1. What is proved (Lean names)

All in namespace `DirichletCharacter` unless marked; `[NeZero q]` throughout.

| Statement | Lean |
|---|---|
| `‖G_χ(σ)‖` bounded on `1 < σ ≤ 2` for `χ ≠ 1` | `exists_norm_primePart_le` |
| `re(u·S_χ(n)) ≠ c·n + O(1)` for `u ∈ ℂ`, real `c ≠ 0` | `not_exists_abs_re_mul_sum_sub_mul_le` |
| `S_χ(n) ≠ c·n + O(1)`, complex `c ≠ 0` | `not_exists_norm_sum_sub_mul_le` |
| `Σ_{k<n} re χ(p_k) ≠ c·n + O(1)`, real `c ≠ 0` | `not_exists_abs_sum_re_sub_mul_le` |
| Split of (1) at `j = m`: `G_χ + (prime powers) = Σ_{j<m} G_{χ^j}(j s)/j + tailPart χ m s` | `primePart_add_primePowerPart_eq` |
| `tailPart χ m` holomorphic on `re s > 1/m`; `re → +∞` at `1/m⁺` if `χ^m = 1` | `differentiableOn_tailPart`, `tendsto_re_tailPart` |
| Engine: for a nonempty set `X` of nonprincipal `ψ` with `ψ^m = 1`, the sums `Σ_{ψ∈X} G_{ψ^j}`, `0 < j < m`, cannot all continue holomorphically to `re s > 0` | `not_forall_exists_differentiableOn_primePart` |
| `χ^m = 1`, `χ ≠ 1`: the `S_{χ^j}`, `0 < j < m`, are not all bounded | `not_forall_exists_norm_sum_pow_le` |
| same with `0 < j ≤ m/2` only (`S_{χ^{m-j}} = conj S_{χ^j}`) | `not_forall_exists_norm_sum_pow_le_of_two_mul_le` |
| `χ^3 = 1`, `χ ≠ 1`: `Σ_{k<n} re χ(p_k)` unbounded | `not_exists_abs_sum_re_le_of_pow_three` |
| `χ^3 = 1`, `χ ≠ 1`: `S_χ(n)` unbounded | `not_exists_norm_sum_le_of_pow_three` |
| `χ^3 = 1`, `χ ≠ 1`: `k ↦ re χ(p_k)` not eventually periodic | `not_eventuallyPeriodic_re_apply_nthPrime` |
| digits `f(χ(p_k)) < b` with `f z ≠ f 1` for cube roots `z ≠ 1` give an irrational number | `irrational_tsum_of_pow_three` (and `'` for `f` injective on cube roots) |
| a cubic character exists modulo every prime `ℓ ≡ 1 (mod 3)` | `exists_ne_one_pow_three_eq_one` |
| for such `χ` and `a ≠ 0`: `χ(a) = 1 ↔ a` is a cube mod `ℓ` | `apply_eq_one_iff_exists_pow_three` |
| `Real.cubicResidueConstant ℓ b = Σ_k [p_k is a nonzero cube mod ℓ] b^{-(k+1)}` is irrational | `Real.irrational_cubicResidueConstant` |

Helpers: `Complex.logTail m z = -log(1-z) - Σ_{j<m} z^j/j` with `norm_logTail_le`
(`‖logTail m z‖ ≤ ‖z‖^m (1-‖z‖)^{-1}/m`), `Function.EventuallyPeriodic.exists_abs_sum_real_sub_mul_le`
(real-valued periodic sums are `c·n + O(1)`), `Filter.Tendsto.finsetSum_atTop`.

## 2. Proof ideas

**Linear case (every order).** The program planned a case split: `re c ≠ 0` through `|L|`, and
`re c = 0` through `arg L` with a lifting argument for `exp`. The formal proof avoids both. Let
`F(s) = G_χ(s) + (prime-power part)` on `re s > 1`, so `exp F = L(·, χ)`. Then `F' = L'/L`, and
`L'/L` is continuous on the compact segment `[1, 2]` because `L(·, χ)` is entire and has no zero
on `re s ≥ 1` (Mathlib's `LFunction_ne_zero_of_one_le_re`). The mean value inequality gives
`‖F(σ) - F(2)‖ ≤ max_{[1,2]} |L'/L|`, so `G_χ(σ)` stays bounded as `σ → 1⁺`
(`exists_norm_primePart_le`). This is the whole analytic input. If `‖S_χ(n) - c n‖ ≤ C`, take
`u = c̄`: then `re(c̄ S_χ(n)) = |c|² n + O(1)`, summation by parts gives
`re(c̄ G_χ(σ)) = |c|² Σ_k p_k^{-σ} + O(1)`, and the right side tends to `+∞` while the left is
bounded. One theorem with a twist `u` gives the complex case (`u = c̄`), the real-part case
(`u = 1`) and the imaginary-part case (`u = -i`).

**The order-`m` engine.** Cut (1) at `j = m`:
`log L(s, χ) = Σ_{j<m} G_{χ^j}(j s)/j + T_m(s)` with `T_m(s) = Σ_k logTail m (χ(p_k) p_k^{-s})`.
The tail converges absolutely for `re s > 1/m` (`‖logTail m z‖ ≤ ‖z‖^m/(1-‖z‖)` and
`‖z‖ ≤ p^{-re s} ≤ 2^{-re s} < 1`). If `χ^m = 1`, then `χ(p)^m = 1` for `p ∤ q`, and
`T_m(σ) = Σ_{p∤q} p^{-mσ}/m + O(Σ_p p^{-(m+1)/m})`, whose real part tends to `+∞` as `σ → 1/m⁺`
(`le_re_tailPart`). Now assume holomorphic `B_j` on `re s > 0` with `B_j = G_{χ^j}` on `re s > 1`,
`0 < j < m`. Then `Φ(s) = Σ_{j<m} B_j(js)/j + T_m(s)` is holomorphic on `re s > 1/m`, `exp Φ = L`
on `re s > 1`, hence on `re s > 1/m` (identity theorem), and `|L(σ, χ)| = exp(re Φ(σ)) → ∞` as
`σ → 1/m⁺`, contradicting continuity of `L` at `1/m`. The formal statement allows a finite set
`X` of characters and the product `Π_{ψ∈X} L(s, ψ)`; then only the *sums* `Σ_{ψ∈X} G_{ψ^j}` need
to continue.

**Order 3.** Take `X = {χ, χ²}`. Since `χ(p)³ = 1` for `p ∤ q`, `χ(p)² = χ̄(p)`, so `χ² = χ̄` on
the primes and `(χ²)² = χ`. Both `j = 1` and `j = 2` require the continuation of
`G_χ + G_χ̄ = 2 Σ_k re χ(p_k) p_k^{-s}`, which the Abel series provides as soon as
`Σ_{k<n} re χ(p_k)` is bounded. This is stronger than bounded `S_χ`, and it is exactly what the
cubic-residue digits need: the digit `[χ(p) = 1]` determines `re χ(p) ∈ {1, -1/2}`. The single
character version (`X = {χ}`) needs `S_χ` and `S_{χ²} = conj S_χ` bounded, i.e. only `S_χ`.

**Digits.** If the digit sequence `f(χ(p_k))` is eventually periodic and `f` separates `1` from
`ω, ω²`, then `re χ(p_k)` is eventually periodic (eventually `χ(p_k)` is a cube root of unity and
`re χ(p_k) = 1` or `-1/2` according to `f(χ(p_k)) = f(1)`), so `Σ_{k<n} re χ(p_k) = c n + O(1)`
with real `c`: `c = 0` contradicts the order-3 theorem, `c ≠ 0` the linear case. For the cubic
residue constant, `χ(a) = 1` iff `a` is a nonzero cube mod `ℓ` (proved through a generator of the
cyclic group `(ZMod ℓ)ˣ`: `χ(g)` is a primitive cube root of unity, so `χ(g^n) = 1` iff `3 ∣ n`).

## 3. Context: what is new here

As mathematics, unboundedness of `S_χ` for every nonprincipal `χ` is classical, by zeros:
bounded `S_χ` continues `G_χ` and `G_χ̄` to `re s > 0`, so (1) and its analogue for `χ̄` make
`L(·, χ)` and `L(·, χ̄)` zero-free on `re s > 1/2`; the functional equation then puts all
nontrivial zeros on `re s = 1/2`, where the `j ≥ 2` terms of (1) are still holomorphic (away
from `s = 1/2`), so there would be no nontrivial zeros except possibly `s = 1/2`, which the
Hadamard theory of the completed `L`-function forbids (Landau-type oscillation theorem; it even gives `S_χ = Ω(n^{1/2-ε})`). The linear case
follows from the prime number theorem in progressions. The point of the formal development is a
proof that uses neither zeros nor the prime number theorem, only that `L(·, χ)` is entire and
`L(1, χ) ≠ 0`, both in Mathlib. That proof covers orders 2 and 3, the linear case in all orders,
and the simultaneous statements; it does not cover a single character of order `≥ 4`.

## 4. Why order `m ≥ 4` fails with bounded `S_χ` alone

The engine needs every term `G_{χ^j}(j s)/j`, `0 < j < m`, of (1) holomorphic on (a neighbourhood
of the real segment in) `re s > 1/m`, i.e. `G_{χ^j}(w)` on `re w > j/m`. Bounded `S_χ` gives
`G_χ` and, since `S_χ̄ = conj S_χ`, `G_χ̄ = G_{χ^{m-1}}` on `re w > 0`. For `2 ≤ j ≤ m-2` (empty
exactly when `m ≤ 3`) nothing is known about `χ^j` beyond the Euler product: `G_{χ^j}(w)` is
`log L(w, χ^j)` minus terms holomorphic on `re w > 1/2`, so it continues to `re w > j/m` (with
`j/m < 1`) only through a holomorphic logarithm of `L(·, χ^j)` there, i.e. only if
`L(·, χ^j)` has no zeros on the relevant region. That is information about zeros, which the
method was designed to avoid. Note that `j` need not be coprime to `m`: for `m = 4` the obstacle
is `j = 2` (`χ²` quadratic), for `m = 5` it is `j = 2, 3` (`χ³ = conj χ²`).

**What the method gives for `m ≥ 4` (formalized).** Bounded `S_{χ^j}` for all `1 ≤ j ≤ m/2`
supplies all the needed continuations (`S_{χ^{m-j}} = conj S_{χ^j}`):
`not_forall_exists_norm_sum_pow_le_of_two_mul_le`. Example: for `χ` of order 5, `S_χ` and
`S_{χ²}` are not both bounded. If `2 ∣ m` or `3 ∣ m`, some `χ^j` with `j ≤ m/2` has order 2 or 3
and its sums are already known to be unbounded, so the simultaneous statement carries new
information only when `gcd(m, 6) = 1` (`m = 5, 7, 11, 13, 25, …`).

**A conditional version (not formalized; proof sketch).** Let `χ` have exact order `m ≥ 4`, and
assume `L(σ, χ^k) ≠ 0` for real `σ ∈ [k/m, 1]`, `2 ≤ k ≤ m-2`. Under bounded `S_χ`, continue each
`G_{χ^k}` along a thin simply connected neighbourhood of the real segment by
`G_ψ(w) = log L(w, ψ) - Σ_{i≥2} G_{ψ^i}(i w)/i`, recursively (stopping at `ψ ∈ {χ, χ̄}`, which are
given; the segments that occur for `ψ = χ^{ij}` are `(ij/m, 1]` with `ij < m`, covered by the
hypothesis). The principal character enters only through `G_{χ_0}(m s)`, and collecting its
coefficient over the recursion with Möbius inversion
`G_χ(s) = Σ_{i≥1} μ(i)/i · log L(i s, χ^i)` gives, as `σ → 1/m⁺`,

    log L(σ, χ) = (μ(m)/m) · log(mσ - 1) + C + o(1).                              (2)

If `μ(m) = -1` then `|L(σ, χ)| → ∞`; if `μ(m) = +1` then `L` would vanish at `1/m` to the
non-integral order `1/m`. Either way `L(·, χ)` is not analytic at `1/m`: contradiction. So
**for squarefree `m`, `S_χ` is unbounded provided `L(σ, χ^k) ≠ 0` on `[k/m, 1]` for
`2 ≤ k ≤ m-2`** (since `L(σ, χ̄^k) = conj L(σ, χ^k)` for real `σ`, half of these suffice). For
`m = 2, 3` the condition is empty and (2) is the formalized blow-up (`μ(2) = μ(3) = -1`). A
non-vanishing condition of this kind, at finitely many real points of finitely many
`L`-functions, is checkable numerically (and rigorously with interval arithmetic) for a given
character; see section 5.

**Non-squarefree `m`: the leading singularity cancels.** For `μ(m) = 0` the coefficient in (2)
vanishes, even under the zero-free hypothesis. For `m = 4` explicitly:
`G_{χ²}(2s)/2 = ½ log L(2s, χ²) - ¼ G_{χ_0}(4s) + …`, and the `-¼ G_{χ_0}(4s)` cancels the
divergent `+¼ G_{χ_0}(4s)` of the tail. In multiplicative form, bounded `S_χ` gives
`L(s, χ)² / L(2s, χ²) = exp(H(s))` with `H` holomorphic on `re s > 1/5`, and nothing blows up at
`s = 1/4`. So the method gives nothing for `m = 4, 8, 9, 12, …`, conditionally or not. (The
identity does force every zero `ρ` of `L(w, χ²)` with `re ρ > 2/5` to be a zero of `L(·, χ)` at
`ρ/2`; since about half of the zeros of `L(w, χ²)` have `2/5 < re ρ ≤ 1/2`, this would produce
`≫ T log T` zeros of `L(·, χ̄)` with real part `≥ 3/4` up to height `T`, contradicting classical
zero-density estimates. That route uses zeros and density theorems, neither of which is in Mathlib.)

## 5. Numerical sanity checks

Computed with `sympy` (primes) and `mpmath` (Hurwitz zeta); scripts in the session scratchpad,
not committed.

**Cubic character modulo 7** (`χ(3) = ω = e^{2πi/3}`, so `χ = 1` on `{1, 6}`, the cubes mod 7,
`χ = ω` on `{3, 4}`, `χ = ω²` on `{2, 5}`), first `10^5` primes:

| `n` | `p_n` | `re S` | `im S` | `\|S\|` | `\|S\|/√n` | `\|S\|/(√p_n / log p_n)` |
|---|---|---|---|---|---|---|
| 10 | 29 | -1.50 | -0.87 | 1.73 | 0.548 | 1.08 |
| 100 | 541 | -3.00 | -3.46 | 4.58 | 0.458 | 1.24 |
| 1000 | 7919 | -3.00 | -3.46 | 4.58 | 0.145 | 0.46 |
| 10^4 | 104729 | -13.50 | 11.26 | 17.58 | 0.176 | 0.63 |
| 5·10^4 | 611953 | -30.50 | -16.45 | 34.66 | 0.155 | 0.59 |
| 10^5 | 1299709 | 43.50 | -6.06 | 43.92 | 0.139 | 0.54 |

`max_{n≤10^5} |S(n)| = 81.96` (at `n = 96898`); `re S` ranges over `[-61.5, 80.0]` and changes
sign 1819 times; residue classes mod 7 are hit `16677, 16649, 16685, 16630, 16673, 16685` times
(classes `1, …, 6`). The growth is consistent with the expected `√p_n / log p_n` scale, and there
is no visible bias: `re S < 0` for 63.7% and `im S < 0` for 53.6% of `n ≤ 10^5`, compared with
100% for the Legendre symbol mod 7 (`S(10^5) = -87`), which has the Chebyshev bias. This matches
the theory: the bias of a character sum comes from the `j = 2` term `G_{χ²}(2s)/2` of (1), which
for a quadratic `χ` is `G_{χ_0}(2s)/2` (a constant-sign term) and for a cubic `χ` is
`G_χ̄(2s)/2`, oscillating with mean zero. First 40 digits of the base-2 cubic residue constant of
`ℓ = 7`: `0000010001001100000100101000011001000010`.

**Real-zero condition of section 4** (non-rigorous scan, 200 points per segment):

| character | needs | `min \|L(σ, ψ)\|` on the segment |
|---|---|---|
| order 5 mod 11, `ψ = χ²` | `σ ∈ [2/5, 1]` | 0.333 (at `σ = 0.4`) |
| order 5 mod 11, `ψ = χ³` | `σ ∈ [3/5, 1]` | 0.451 (at `σ = 0.6`) |
| order 6 mod 7, `ψ = χ²` | `σ ∈ [1/3, 1]` | 0.222 (at `σ = 1/3`) |
| order 6 mod 7, `ψ = χ³` (quadratic) | `σ ∈ [1/2, 1]` | 1.147 (at `σ = 1/2`) |
| order 6 mod 7, `ψ = χ⁴` | `σ ∈ [2/3, 1]` | 0.404 (at `σ = 2/3`) |

So, granting a rigorous version of this scan, the partial sums of the order-5 character mod 11 and
of the order-6 character mod 7 are unbounded by the conditional argument (`μ(5) = -1`,
`μ(6) = +1`).

## 6. Open questions

1. **Formalize order `m ≥ 4`.** Two routes: (a) the conditional theorem of section 4, which needs
   holomorphic logarithms along real segments (`log L(w, ψ)` on a simply connected zero-free
   neighbourhood) plus a certified real-zero check for a specific character; it covers squarefree
   `m` only. (b) The classical zero argument of section 3, which covers every `m` but needs the
   functional equation (in Mathlib for primitive characters) and the existence of nontrivial zeros
   (Hadamard factorization of an entire function of order 1, not in Mathlib).
2. **Imaginary parts for order 3.** `im S_χ = c n + O(1)` with `c ≠ 0` is excluded (twist
   `u = -i`), but *bounded* `im S_χ` is not: the relevant product is `L(s, χ)/L(s, χ̄)`, and its
   `j = 3` terms cancel (`χ³ - χ̄³ = 0` on the primes), so there is no blow-up at `1/3`. Bounded
   `im S_χ` forces only `L(·, χ)/L(·, χ̄)` to be zero-free on `re s > 1/2`, i.e. the zeros of
   `L(·, χ)` there to be symmetric under conjugation. Consequently the irrationality of digit
   sequences that distinguish `ω` from `ω²` but not `1` from `ω` is open by this method.
3. **Rates.** Combining with Direction 2: if `|S_χ(n)| ≤ C n^θ` with `θ < 1/3` (cubic `χ`), the
   Abel series continue `G_χ` to `re s > θ` and `G_χ̄(2s)` to `re s > θ/2`, and the blow-up at `1/3`
   still applies; so `S_χ ≠ O(n^{1/3-ε})` for cubic `χ` without zeros. (Classically
   `Ω(n^{1/2-ε})` holds through zeros.) The formal version needs the polynomially bounded Abel
   series of Direction 2.
4. **Prime-power moduli and non-squarefree orders.** Is there any zero-free argument for a single
   character of order 4? Section 4 shows the blow-up method cannot work; the multiplicative
   identity `L(s, χ)² / L(2s, χ²) = exp(H(s))` on `re s > 1/5` is the precise residual
   information.
5. **Other cubic constants.** Mathlib's `MulChar.exists_mulChar_orderOf` gives characters of every
   order `n ∣ ℓ - 1` modulo a prime `ℓ`; the cubic residue constant is the first instance beyond the
   quadratic one. For order 5 or 7 residue symbols, irrationality would follow from the
   conditional theorem of section 4 (squarefree orders) but not from what is formalized.
