# What replaces the primes: other sequences, other placements (Direction 4)

> **Corrections (second round).** Two statements below have been superseded. (1) The positive
> bias of the sector digit `[a ≡ 3 (mod 4)]` for `p = a² + b²` is *not* a small-`a` lattice
> effect: it is an L-function effect of order `√x/(2π)` spread over all lines, with two independent
> derivations of the constant; see `research/gaussian-primes.md`. (2) The single-class indicator
> `[p_k ≡ a (mod q)]` is now proved non-periodic for every `q ≥ 3` and every unit `a`, including the
> classes where the prime-square coefficient was thought to vanish; see `research/single-class.md`.

**Status.**

* **Formalized** (`RokickiConstant/General/Lacunary.lean`, no `sorry`, standard axioms only):
  Rokicki's digits placed at the factorial positions give a Liouville number, hence a
  transcendental one: `Real.rokickiLacunary = Σ_k b_k 2^{-(k+1)!}` with
  `Real.liouville_rokickiLacunary` and `Real.transcendental_rokickiLacunary`. The general lemma
  is `liouville_tsum_div_pow_factorial`: for every base `m ≥ 2` and all `0/1` digits with
  infinitely many ones, `Σ_k d_k m^{-k!}` is a Liouville number.
* **Classification** of fifteen variants (§1), each checked numerically by
  `scripts/sequences.py`, which runs in about 15 seconds.
* **Two observations that seem to be new** (sketches; not formalized, not checked against the
  literature):
  1. The method of this project transfers verbatim to primes in a progression cut out by
     quadratic characters (for example `p ≡ 1 mod 3`), but **not** to a progression of
     non-squares (for example `p ≡ 2 mod 3`). There the `m = 2` prime-square term, which the
     method relies on, vanishes identically (§3.2).
  2. That same term is the source of the Chebyshev bias. The numerics show the bias exactly
     where the method works and its absence where it fails: `S(n) < 0` for `100%` of `n`
     along `p ≡ 1 mod 3`, but only for `58%` (with `1253` sign changes) along `p ≡ 2 mod 3`
     (§3.3).
* **The placement hierarchy** (§2.8). With Rokicki's digits at positions `e_k`:
  * `e_k = k+1` is `ρ`; its transcendence is open;
  * `e_k = (k+1)²`: no known criterion applies;
  * `e_k = 2^k`: transcendental by Roth's theorem, and a Liouville number by Shiu's theorem;
  * `e_k = (k+1)!`: a Liouville number by an elementary argument (formalized).

Notation. `b_k = [p_{k+2} ≡ 3 (mod 4)]` are Rokicki's digits (`Real.rokickiDigit k`). For a
sequence `a_0 < a_1 < …` and a digit rule `d_k ∈ {0, 1}`, the *dense* constant is
`x = Σ_k d_k 2^{-(k+1)}`. "Irrational" for a dense constant means exactly that `(d_k)` is not
eventually periodic (`irrational_tsum_div_two_pow`). `p(L)` is the subword complexity, the
number of distinct length-`L` blocks of digits.

## 1. The table

The values are those printed by `scripts/sequences.py`, certified by an exact enclosure from
`3400` binary digits; it prints `60` decimals, and `1000` with `--full`. "Checked" means checked
numerically here. "Lit." means the claim is taken from the literature. "Sketch" means the claim
is argued in this note and is neither formalized nor taken from the literature.

| # | Sequence `a_k` / digit `d_k` | `x ≈` | Status | Method | Formalized? |
|---|---|---|---|---|---|
| 1 | odd primes, `[p ≡ 3 mod 4]` (`ρ`) | `0.7004001379` | irrational; transc. open | `L(s,χ₄)`, `m = 2` blow-up | yes (main) |
| 2 | primes `≡ 1 mod 3`, `[p ≡ 7 mod 12]` | `0.7083634348` | irrational (sketch) | `L(s,χ₄)L(s,χ₁₂)`, `m = 2` blow-up | no |
| 3 | primes `≡ 2 mod 3`, `[p ≡ 11 mod 12]` | `0.3238094692` | irrational (sketch) | `L(s,χ₄)/L(s,χ₁₂)` + Hadamard; **no** `m = 2` term | no |
| 4 | primes `≡ 1 mod 8`, `[2 not a 4th power mod p]` | `0.7940976767` | irrational (sketch) | quadratic Hecke `L` over `ℚ(ζ₈)`, coefficient `1` | no |
| 5 | `p ≡ 1 mod 4`, `p = a²+b²`, `a` odd `> 0`: `[a ≡ 3 mod 4]` | `0.2600033884` | **not settled here** | infinitely many Grössencharacters; method fails | no |
| 6 | `p = a²+b²`: `[b ≡ 2 mod 4]` | — | = `[p ≡ 5 mod 8]` (checked) | `χ₈` in disguise; along `p ≡ 1 mod 4` a case of §3.1 | along all primes: `irrational_tsum` |
| 7 | sums of two squares, `[n ≡ 3 mod 4]` | `0` | rational (never `3`) | — | — |
| 8 | sums of two squares, `[n odd]` | `0.5831631619` | irrational (sketch, elementary) | self-similarity `n ∈ S ⇔ 2n ∈ S` + density 0 | no |
| 9 | squarefree, `[s ≡ 3 mod 4]` | `0.1451579508` | irrational; every word occurs (sketch, elementary); transc. open | CRT + Mirsky's pattern count | no |
| 10 | Beatty `⌊k√2⌋`, `[⌊k√2⌋ ≡ 3 mod 4]` | `0.0357058388` | **transcendental** (lit.) | rotation coding, `p(L) = 2L`; Adamczewski–Bugeaud 2007 | no |
| 11 | Sturmian `[⌊(k+1)√2⌋ − ⌊k√2⌋ = 2]` | `0.1612942612` | **transcendental** (lit.) | `p(L) = L+1`; Ferenczi–Mauduit 1997 | no |
| 12 | Thue–Morse `[t_k = 1]` (control) | `0.4124540336` | **transcendental** (lit.) | Mahler 1929 | no |
| 13 | Fibonacci `[F_k ≡ 3 mod 4]` | `2/63` | rational | Pisano period `6` | — |
| 14 | `[k² ≡ 1 mod 4]`, `[3^k ≡ 3 mod 4]` | `1/3`, `1/3` | rational | period `2`; `[k² ≡ 3] = 0` | — |
| 15 | `b_k` at positions `(k+1)!` | `0.5156250596` | **Liouville, transcendental** | Liouville 1844 | **yes** |
| 16 | `b_k` at positions `2^k` | `0.5664062500` | **transcendental**; Liouville | Roth (needs `∞` many 0s and 1s); Shiu (runs) | no |
| 17 | `b_k` at positions `(k+1)²` | `0.5019683838` | irrational (trivial); transc. open | — | no |

Numerics, for every row:

* **Periodicity.** The script finds the period `6`, `2`, `2` for rows 13–14 and recovers `2/63`
  and `1/3` exactly, matching the enclosure. No period `≤ 1000` appears in `2·10^5` digits for
  any other row.
* **PSLQ** on `[1, x, …, x^d]`, `d ≤ 6`, at `300` digits with `maxcoeff = 10^25`. It finds
  `2 − 63x` and `1 − 3x` for rows 13–14, and nothing for rows 1–5 and 8–12.
* **Rows 15–17** are dyadic rationals of height `> 10^150` to `300` digits, so PSLQ is
  meaningless for them.

## 2. Row by row

### 2.1 Primes in an arithmetic progression (rows 2, 3)

There are two routes to these constants: a combinatorial reduction, which fails, and the
character-sum method, which works with an `L`-function product (§3.1).

The reduction fails. The digits of row 2 are `χ₄(q_k)` along `q_0 = 7 < q_1 = 13 < …`, the
primes `≡ 1 mod 3`. This sequence is **not** a function of the full sequence `χ₄(p_k)`, or of
the residue sequence `p_k mod 12` read at the same positions. The positions of the subsequence
inside the primes are themselves irregular. So neither `Real.irrational_residueConstant` nor
`irrational_tsum` applies.

The method works. Bounded or linear partial sums of `χ₄` along `p ≡ 1 mod 3` make the product
`L(s,χ₄)L(s,χ₁₂)` blow up at `s = 1/2`, a contradiction (§3.1). Row 3 is different: the analogous
quotient `L(s,χ₄)/L(s,χ₁₂)` has **no** blow-up, and an extra argument is needed (§3.2).

Numerics, consistent with the theory (§3.3): row 2 has a total bias, row 3 none.

### 2.2 Gaussian primes and Hecke characters (rows 4, 5, 6)

Every `p ≡ 1 mod 4` is `a² + b²` with `a` odd, `b` even, uniquely up to signs. Natural digits,
sorted by what they really are:

* **`b mod 4` (row 6).** For `p ≡ 1 mod 4`, `[b ≡ 2 mod 4] = [p ≡ 5 mod 8]`: from `a² ≡ 1 mod 8`
  and `b² ≡ 0` or `4 mod 16`; checked for all `332180` such `p < 10^7`. So this digit is the
  Dirichlet character `χ₈` restricted to `p ≡ 1 mod 4`. Taken along *all* primes it is a Legendre
  constant, already covered; along the subsequence `p ≡ 1 mod 4` it is a case of §2.1 (the class
  `1 mod 4` is a square class, so the method transfers).
* **"Parity of `a`".** This is not a digit, because one normalizes `a` odd. With the other
  normalization, "the smaller of `a, b` is even", the digit is a sector condition like the next
  one.
* **`a mod 4` with `a > 0` (row 5).** This digit is not a function of `p mod 8`: both residues
  occur in both classes (checked). It equals `(1 − ε(p)χ₈(p))/2`, where `ε(p)` is the sign of
  `Re π` for the *primary* Gaussian prime `π ≡ 1 mod (2+2i)` above `p`. The sign of `Re π` is a
  half-plane condition on the angle of `π`. Its Fourier expansion runs over **all** odd powers
  `λ^j`, `λ(π) = π/|π|`, of the basic Grössencharacter. So the digit is not one character but an
  infinite combination (Hecke's equidistribution of angles gives density `1/2`). The method
  controls each mode `λ^j χ₈` separately (§3.4), but not the infinite sum. We know no proof that
  this digit sequence is not eventually periodic.

  The numerics show a strong bias: `Σ_{p<10^7} χ₄(a_p) = +704`, positive for every prefix. The
  bias sits at the edge of the sector: the primes `p = 1 + b²` (`a = 1`) alone contribute `+315`,
  and `a ≤ 9` contributes `+443`. It looks like a lattice-point effect from small `a`, not an
  `L`-function effect.
* **A genuine finite-order Hecke character (row 4).** For `p ≡ 1 mod 8`, the number `2` is a
  quadratic residue, and the question "is `2` a 4th power mod `p`" is a quadratic Hecke
  character `ψ` of `K = ℚ(ζ₈)`. It is attached to the quadratic extension `K(2^{1/4}) = K(√√2)`,
  whose Galois closure over `ℚ` has group `D₄`, so `ψ` is not a Dirichlet character. By Gauss,
  `2` is a 4th power mod `p` exactly when `p = x² + 64y²`, that is, when `8 ∣ b`. This is
  checked for the first `20000` primes `p ≡ 1 mod 8`, with no exceptions. The method transfers,
  with blow-up coefficient `1` (§3.4).

### 2.3 Sums of two squares (rows 7, 8)

Let `S = {n ≥ 1 : n = a² + b²}`, enumerated `n_0 = 1 < n_1 = 2 < 4 < 5 < 8 < …`, and
`B(x) = #S ∩ [1, x]`.

The digit `[n ≡ 3 mod 4]` is identically `0`, because `a² + b² ≢ 3 (mod 4)`: row 7 is the
rational `0`. The residues of elements of `S` take only the values `0, 1, 2`, with densities
`1/4, 1/2, 1/4` inside `S`. A nontrivial binary encoding is `d_k = [n_k odd]` (equivalently
`[n_k ≡ 1 mod 4]`), or the full residue in base `3`.

**Claim (sketch; elementary).** `(d_k)` is not eventually periodic, so row 8 is irrational.

*Proof.* Two facts are used:

* **Scaling.** `n ∈ S ⇔ 2n ∈ S`, using `2(a²+b²) = (a+b)² + (a−b)²` and its converse. So the
  even elements of `S` up to `x` are exactly `2·(S ∩ [1, x/2])`, and
  `#{odd n ∈ S, n ≤ x} = B(x) − B(x/2)`.
* **Density zero.** `B(x) = o(x)`. This follows from `Σ_{p ≡ 3 (4)} 1/p = ∞`, which in turn
  follows from `L(1,χ₄) = π/4 ≠ 0`.

If `(d_k)` were eventually periodic with frequency `α`, then counting odd elements among the
first `N` elements of `S` would give `B(x) − B(x/2) = α B(x) + O(1)` for all `x`. So
`B(x/2) = β B(x) + O(1)` with `β = 1 − α`. Iterating:

* `β < 1/2` forces `B(x) ≫ x^{θ}` with `θ > 1`, which is absurd because `B(x) ≤ x`.
* `β > 1/2` forces `B(x) ≪ x^{θ}` with `θ < 1`. This contradicts the elementary lower bound
  `B(x) ≫ x/log³x`, which follows from Cauchy–Schwarz with `Σ_{n≤x} r₂(n) ~ πx` and
  `r₂(n) ≤ 4d(n)`.
* `β = 1/2` gives `B(x) = 2B(x/2) + O(1)`, hence `|B(x)/x − B(y)/y| ≤ 2C/y` whenever
  `x = 2^j y`. Since `B(y) ≥ √y` (the squares), this keeps `B(x)/x` bounded below along
  `x = 2^j y`, contradicting density zero. ∎

Numerics: `B(x) − 2B(x/2)` is `−24, −137, −892, −6417, −48852` at `x = 10^3, …, 10^7`, so it is
not `O(1)`; it matches Landau's `B(x) ~ K x/√log x`, which gives
`B(x) − 2B(x/2) ≈ −K x log 2 /(2 (log x)^{3/2})`.

`χ₄` sits behind the scenes in two places:

* Landau's theorem comes from `Σ_{n∈S} n^{-s} = (ζ(s)L(s,χ₄))^{1/2} · H(s)`, with `H`
  holomorphic and nonzero on `re s > 1/2`.
* Density zero uses `L(1,χ₄) = π/4`.

The character-sum method itself does not transfer. There is no Euler product of the indexed kind
(`Σ_k χ(n_k) n_k^{-s}` with `χ` a character), and the elementary proof above is better.

### 2.4 Squarefree numbers (row 9)

Write `s_0 = 1 < s_1 = 2 < 3 < 5 < 6 < …` for the squarefree numbers. Their residues mod `4` lie
in `{1, 2, 3}`, each with density `1/3` inside the squarefree numbers; the local factor at `2` is
the same for all three classes. The digit is `d_k = [s_k ≡ 3 mod 4]`.

**Claim (sketch; elementary).** Every finite word over `{1,2,3}` occurs infinitely often in
`(s_k mod 4)`. So the residue sequence has complexity `p(L) = 3^L`, the digit sequence has
`p(L) = 2^L`, and row 9 is irrational.

*Proof.* Fix a word `r_1 … r_L`.

1. **Gaps.** Choose gaps `g_i ≡ r_{i+1} − r_i (mod 4)`, `g_i ≥ 1`, and also `g_i ≡ 0 mod ℓ²`
   for every odd prime `ℓ` with `ℓ² ≤ L`; this is possible by CRT. Let `h_i` be the partial sums.
2. **Forced non-squarefree numbers.** For each intermediate offset `h` not divisible by `4`
   (offsets `≡ 0 mod 4` are automatically non-squarefree), pick a fresh large prime `q_h` and
   require `q_h² ∣ n + h`.
3. **The progression.** Require also `n + h_1 ≡ r_1 (mod 4)` and `n + h_1 ≢ 0 (mod ℓ²)` for the
   small `ℓ`. This defines an arithmetic progression of `n`.
4. **Squarefree positions.** In this progression, the `L` numbers `n + h_i` are simultaneously
   squarefree for a positive proportion of `n`: the local densities are positive at every prime.
   This is the elementary pattern count of Mirsky (1947/1949) for `r`-free numbers, restricted
   to an arithmetic progression. ∎

This makes row 9 an instructive cousin of `ρ`. Its digit sequence provably has *maximal*
complexity, which is still conjectural for the primes. It is provably **not** normal in base `2`:
the digit `1` has density `1/3`. Its transcendence is open, for the same reasons as for `ρ`
(`research/transcendence.md` §2): every criterion that needs low complexity is excluded, and the
Bailey–Borwein–Crandall–Pomerance digit-count bound says nothing.

Numerics:

* All `3^L` words occur for `L ≤ 4` among the first `6·10^6` squarefree numbers. For `L = 5`,
  `225` of the `243` words occur.
* The `18` missing words each force at least `6` (out of at most `8`) specific numbers not
  divisible by `4` to be non-squarefree. Each forced number is non-squarefree with probability
  about `0.19`, so these words are rare, not impossible.

The analytic route (the method of this project) also transfers, but needs *more* input than
CRT:

1. A periodic residue sequence forces `Σ_{n≤x} μ²(n)χ₄(n) = O(1)`, since the frequencies of the
   residues `1` and `3` are equal.
2. Then `Σ μ²(n)χ₄(n)n^{-s} = L(s,χ₄)/((1 − 4^{-s})ζ(2s))` is holomorphic on `re s > 0`.
3. That forces `L(ρ/2, χ₄) = 0`, with multiplicity, at every nontrivial zero `ρ` of `ζ`. This
   is false: by Riemann–von Mangoldt, `ζ` has about `(T/π) log T` zeros up to height `2T`, more
   than the `(T/2π) log T` zeros that `L(·,χ₄)` has up to height `T`.

So the analytic route needs the zeros of `ζ`; the elementary route needs nothing.

### 2.5 Beatty sequences (rows 10, 11)

For irrational `α > 0`, the residue is `⌊kα⌋ ≡ r (mod 4)` exactly when `{kα/4} ∈ [r/4, (r+1)/4)`.
So the digit `[⌊kα⌋ ≡ 3 mod 4]` codes the rotation by `β = α/4` with the interval
`I = [3/4, 1)`.

**Which encodings are Sturmian.** A coding of a rotation by `β` with one interval is Sturmian
(complexity `p(L) = L + 1`) exactly when the interval length is `β` or `1 − β` modulo `1`. The
basic example is the difference sequence `⌊(k+1)α⌋ − ⌊kα⌋` (row 11). For `[⌊kα⌋ ≡ 3 mod 4]` the
interval length `1/4` is not in `ℤ + ℤβ`, because `α` is irrational, and such codings have
complexity `p(L) = 2L` for large `L` (Rote 1994; Alessandri–Berthé 1998). The full residue
`⌊kα⌋ mod 4` codes four intervals and has `p(L) = 4L`. Checked for `α = √2`, `L ≤ 30`:

* row 10 has `p(L) = 2L` for `L ≥ 7`;
* row 11 has `p(L) = L + 1`;
* the residue sequence has `p(L) = 4L`.

**Transcendence.** Every irrational number whose `b`-ary digits have
`liminf p(L)/L < ∞` is transcendental (Adamczewski–Bugeaud, Annals 2007; Schmidt's Subspace
theorem). This covers rows 10, 11 and every rotation coding by finitely many intervals.
Irrationality is free: the complexity is unbounded (Morse–Hedlund). For the Sturmian case
(row 11) the older proof of Ferenczi–Mauduit (1997) needs only Ridout's `p`-adic Roth theorem.
None of this is formalizable now: Mathlib has neither Roth's theorem nor the Subspace theorem.

### 2.6 Periodic sequences (rows 13, 14)

The reduction of any linear recurrence over `ℤ` mod `4`, or any polynomial in `k` mod `4`, is
eventually periodic, so the constant is rational. Examples:

* `F_k mod 4` has Pisano period `6` (`0,1,1,2,3,1`), so the digit `[F_k ≡ 3]` gives
  `Σ_j 2^{-(6j+5)} = 2/63`.
* `k² mod 4 ∈ {0, 1}`, so `[k² ≡ 3] = 0` and `[k² ≡ 1] = [k odd]` gives `1/3`. Likewise
  `[3^k ≡ 3 mod 4]` gives `1/3`.
* `2^k mod 4` is eventually `0`.

The script detects the periods and recovers the fractions exactly; PSLQ finds `2 − 63x` and
`1 − 3x`.

### 2.7 Thue–Morse (row 12, control)

The sequence is automatic, with `p(L) = O(L)` (checked: `p(30) = 90`). The constant is
transcendental by Mahler (1929). It is the standard positive control for "transcendental by
structure".

### 2.8 Placements: the same digits, placed sparsely (rows 15–17)

Place Rokicki's digits at positions `e_0 < e_1 < …`: `x = Σ_k b_k 2^{-e_k}`. Truncating after
digit `n` gives `p/q` with `q = 2^{e_n}`. The error is `≈ 2^{-e_{n'}}`, where `n'` is the next
index with `b_{n'} = 1`, so the approximation exponent is `μ_n ≈ e_{n'}/e_n`. The exponents
`μ_0, …, μ_8` printed by the script are, for positions:

* `(k+1)!`: `6, 3, 4, 210, 42, 7, 8, 90, 10`;
* `2^k`: `4, 2, 2, 8, 4, 2, 2, 4, 2`;
* `(k+1)²`: `9, 2.25, 1.78, 3.06, …, 1.23`.

* **`e_k = (k+1)!` (formalized).** Here `μ_n ≥ (n+2)!/(n+1)! = n + 2 → ∞` regardless of the
  digits. The only input needed is that the tail is nonzero, that is, infinitely many digits are
  `1`; that is infinitely many primes `≡ 3 mod 4`. The Lean proof takes this from Mathlib's
  Dirichlet theorem; it would also follow from the project's non-periodicity of `(b_k)`.
  Liouville's theorem gives transcendence.
* **`e_k = 2^k`.** A digit `0` right after position `n` gives `μ_n ≥ 4 > 2`. There are
  infinitely many such `n` (infinitely many primes `≡ 1 mod 4`), and the tails are nonzero, so
  **Roth's theorem** gives transcendence. A run of `L` zeros gives `μ_n ≥ 2^{L+1}`, and Shiu's
  theorem (arbitrarily long runs of consecutive primes `≡ 1 mod 4`) makes `x` a **Liouville**
  number. Runs found below `10^7` (index of the first run of length `L`):

  | `L` | `5` | `6` | `10` | `12` |
  |---|---|---|---|---|
  | index | `376` | `1393` | `31796` | `240746` |

  The same holds for `e_k = ⌊c^k⌋` with any `c > 1`: by Shiu, every such placement is Liouville.
* **`e_k = (k+1)²`.** Here `μ_n → 1`. A useful run would need length `L ≫ n`, but runs at
  index `n` have length `≤ n^{7/12+ε}` (`research/transcendence.md` §4). The binary expansion
  has complexity `≍ L²`, beyond Adamczewski–Bugeaud. Algebraicity of degree `2` is not even
  excluded by the Bailey–Borwein–Crandall–Pomerance digit count. With all digits `1` the number
  is `(θ₃(1/2) − 1)/2`, transcendental by Nesterenko's theorem (1996). That proof uses the
  modular structure of the all-ones sequence and says nothing for Rokicki's digits. Open as far
  as we know.

**The reading.** The digits are the same in all four rows; only the placement changes, and the
arithmetic nature changes with it. The density of the placement, not the arithmetic of the
primes, is what blocks a transcendence proof for `ρ`. Liouville needs gap ratio `→ ∞`; Roth needs
gap ratio `> 2` infinitely often, together with one zero; the dense placement `e_k = k + 1` has
gap ratio `→ 1`.

## 3. Where the method transfers

The project's argument has three ingredients. Bounded (or linear) partial sums of the digit
signs `ε_k = ±1` along `a_k` make `F(s) = Σ_k ε_k a_k^{-s}` holomorphic and bounded near `s = 1/2`
(resp. `s = 1`) by Abel summation. What is needed:

1. **An Euler product.** The `a_k` are the norms of the degree-1 primes of some number field
   `K` (possibly restricted by congruence conditions). The sign `ε_k` is the value of a Hecke
   character `ψ` of finite order whose `L`-function is entire, with `L(1,ψ) ≠ 0` for the linear
   case.
2. **The value set of the character.** `ψ` must take the values `±1` on the `a_k`. The
   prime-power part of `log L(s,ψ)` must then have a **nonzero positive coefficient** `c` in
   front of `log(1/(2s−1))` as `s → 1/2⁺`. A non-integer coefficient also suffices, with an
   identity-theorem argument.

   This coefficient collects:
   * the `m = 2` terms `Σ ψ(𝔭)²/(2N𝔭^{2s})` of the degree-1 primes;
   * the `m = 1` terms of the primes of norm `p²`;
   * nothing else, since all other terms are holomorphic on `re s > 1/3`.

   With `c > 0`, `|L(σ,ψ)| ≍ (2σ − 1)^{-c} → ∞`, which contradicts entireness.
3. **Analytic input of Dirichlet type.** One needs `L(1,χ) ≠ 0` for the characters cutting out
   the progressions, to evaluate densities in `c`. Mathlib has this
   (`DirichletCharacter.LFunction_apply_one_ne_zero`).

### 3.1 Progressions cut out by quadratic characters (row 2): transfers

Let `T = {p : ψ_1(p) = ⋯ = ψ_r(p) = 1}` for quadratic Dirichlet characters `ψ_i`, and let `χ` be
quadratic with every `χψ_S` nonprincipal, where `ψ_S = Π_{i∈S}ψ_i`. Then
`[p ∈ T] = 2^{-r} Σ_S ψ_S(p)` for `p ∤ q`, and

    2^{-r} Σ_S log L(s, χψ_S) = F(s) + ½ Σ_{p ∤ q} p^{-2s} + (holomorphic on re s > 1/3),

with `F(s) = Σ_{p∈T} χ(p)p^{-s}`. The coefficient is `c = 1/2` for each of the `2^r` factors: the
product `Π_S L(s, χψ_S)` of entire functions behaves like `(2s−1)^{-2^{r-1}}`. So `F` cannot be
bounded near `1/2`, and the partial sums of `χ` along `T` are unbounded. The linear case is
excluded at `s = 1` by `L(1, χψ_S) ≠ 0`.

For row 2, take `r = 1`, `ψ_1 = χ₃`, `χ = χ₄`: the product is `L(s,χ₄)L(s,χ₁₂)`. This is the
"verbatim" transfer. A Lean proof would apply the machinery of `General/EulerProduct.lean`
(`primePart`, `primePowerPart`, the Abel series) to each factor and add the results; only the
bookkeeping of the subsequence is new.

Progressions not cut out by quadratic characters (for example `p ≡ 1 mod 5`) lead to complex
powers `Π_ψ L(s, χψ)^{ψ̄(a)/φ(q)}`. The blow-up survives when `a` is a square class. Making it
rigorous needs `L(σ, χψ) ≠ 0` on `(1/2, 1)` for complex `ψ`, or a version of the simultaneous
argument of `research/higher-order.md`. We have not checked this.

### 3.2 Progressions of non-squares (row 3): the `m = 2` term vanishes

For `T = {p ≡ a mod q}` the prime-square coefficient counts the primes `p` whose **square**
`p²` lies in `T`:

    (1/φ(q)) Σ_ψ ψ̄(a) Σ_p χ(p)²ψ(p)²/(2p^{2s}) = ½ Σ_{p : p² ≡ a (q)} p^{-2s}.

If `a` is not a square mod `q`, the sum is empty and `c = 0`. For `p ≡ 2 mod 3`:

    ½(log L(s,χ₄) − log L(s,χ₁₂)) = Σ_{m odd} F(ms)/m,

so bounded partial sums make `L(s,χ₄)/L(s,χ₁₂)` zero-free and pole-free on `re s > 0`. That is no
contradiction on the real axis. It is a contradiction globally: the two functions would have the
same nontrivial zeros with multiplicity. The completed functions `Λ` would then satisfy
`Λ(s,χ₄)/Λ(s,χ₁₂) = e^{A+Bs}` (Hadamard, order `1`). This is impossible, because `χ₄` is odd and
`χ₁₂` even, and the Gamma factors `Γ((s+1)/2)/Γ(s/2) ~ (s/2)^{1/2}` cannot be absorbed by
`e^{Bs}` as `s → +∞`. So row 3 is irrational too (sketch). The proof needs the functional
equation, which Mathlib has (`DirichletCharacter.completedLFunction`), and **Hadamard
factorization**, which Mathlib does not have. This is no longer the project's method: it uses
the zeros.

### 3.3 The same term is the Chebyshev bias (numerics)

In the explicit formula, the prime-square term is what produces the Chebyshev bias
(Rubinstein–Sarnak 1994). The method works exactly when that term is present, so bias and method
should go together. With `S(n) = Σ_{k<n} (1 − 2d_k)` over all terms below `10^7`:

| Sequence | Terms | `S(n) < 0` | Sign changes | `c` |
|---|---|---|---|---|
| `ρ`: `χ₄` over odd primes | `664578` | `99.9%` | `48` | `1/2` |
| row 2: `1` vs `7 mod 12` | `332194` | `100.0%` | `0` | `1/2` (per factor) |
| row 4: Hecke `ψ`, `p ≡ 1 mod 8` | `165976` | `93.5%` | `204` | `1` |
| row 3: `5` vs `11 mod 12` | `332383` | `57.9%` | `1253` | `0` |

Rubinstein–Sarnak predict exactly this: a race between two non-residue classes (`5`, `11` mod
`12`) is unbiased, and a race between a residue class and a non-residue class (`1`, `7`) is
biased. Row 5 (the sector digit) is biased the other way (`S > 0` throughout), but by the
small-`a` lattice effect of §2.2, not by a prime-square term. The sign of `Re π` alone has Fourier
modes with the same `c` (next section), and it is unbiased: its sum below `10^7` is `−72`.

### 3.4 Hecke characters (rows 4, 5)

**Row 4.** Take `K = ℚ(ζ₈)` and `ψ` the quadratic character of `K(2^{1/4})/K`.

* The degree-1 primes lie over `p ≡ 1 mod 8`, four for each such `p`, with
  `ψ = [2 is a 4th power mod p]·2 − 1`.
* The primes of degree `2` lie over `p ≡ 3, 5, 7 mod 8`, two for each `p`, with residue field
  `F_{p²}`. Write `x = √2 ∈ F_{p²}`; `x` is a square iff its norm `N(x)` is a square in `F_p`.
  * For `p ≡ 7`: `x ∈ F_p`, so `ψ = +1`.
  * For `p ≡ 3, 5`: `N(x) = −2`, so `ψ = (−2/p)`, which is `+1` for `p ≡ 3` and `−1` for
    `p ≡ 5`.

So `log L(s,ψ) = 4F(s) + c·log(1/(2s−1)) + hol` near `1/2`, with

* `½` from the `m = 2` terms of the degree-1 primes: `4 · ½ · ¼`, and
* `½` from the degree-2 primes: `2 · ¼ · (1 − 1 + 1)`,

so `c = 1`. Here `L(s,ψ) = ζ_{K(2^{1/4})}(s)/ζ_K(s)` is entire, and the contradiction is as for
`ρ` (sketch). The bias column above agrees: `93.5%` negative.

**Row 5's modes.** For the Grössencharacters `λ^jχ₈` (`j` odd):

* the split primes give no `m = 2` term, since `λ^{2j}` is nontrivial;
* the inert primes `p ≡ 3 mod 4` have primary generator `−p`, so the value is `−1`.

Hence `c = −1/2` for every mode. Each mode is therefore not bounded: the half-integer order would
mean a branch point of the entire `L(s, λ^jχ₈)` at `1/2`. But the sector digit is
`Σ_j (4/πj)(−1)^{(j−1)/2} λ^j χ₈`, an infinite combination, and the method says nothing about
infinite combinations: the values `log L(σ, λ^jχ₈)` are not uniformly controlled in `j`.

**What Mathlib would need** for rows 4–5:

* Hecke characters of number fields (ray class characters and Grössencharacters);
* their `L`-functions, with Euler products over prime ideals, analytic continuation to an
  entire function, and `L(1,ψ) ≠ 0`;
* prime ideals sorted by norm and their decomposition in `ℚ(ζ₈)`.

Mathlib currently has `NumberField.dedekindZeta` as a Dirichlet series with its residue at
`s = 1`, but no continuation and no Hecke characters. The cheapest route for row 4 avoids Hecke
theory altogether: use `L(s,ψ) = ζ_{K(2^{1/4})}(s)/ζ_K(s)`. Even that needs the continuation of
Dedekind zeta functions, which is not in Mathlib.

### 3.5 Summary: the next sequence for verbatim transfer

**Primes in a quadratic progression** (row 2) is the next target: same `L`-functions (Dirichlet),
same blow-up (`c = 1/2` per factor), only a product of `L`-functions instead of one. It is
formalizable with the existing `General/EulerProduct.lean` and Mathlib's Dirichlet `L`-functions.

Gaussian or `ℚ(ζ₈)` primes (row 4) need Hecke `L`-functions, which are missing. Non-square
progressions (row 3) need Hadamard factorization and are outside the method.

## 4. Where transcendence is provable

| Mechanism | Needs from the digits | Examples here | Formal status |
|---|---|---|---|
| Liouville (1844) | sparse placement, gap ratio `→ ∞`, infinitely many ones | row 15 | **formalized** (`Lacunary.lean`) |
| Roth (1955) | gap ratio `> 2` infinitely often, nonzero tail | row 16 | Roth not in Mathlib |
| Liouville via Shiu (2000) | geometric placement + arbitrarily long runs | row 16 | Shiu not in Mathlib |
| Ridout / Ferenczi–Mauduit (1997) | Sturmian, `p(L) = L+1` | row 11 | no |
| Subspace / Adamczewski–Bugeaud (2007) | `liminf p(L)/L < ∞` | rows 10, 11, 12 | no |
| Mahler's method (1929) | functional equation `F(z^k) = R(z, F(z))` | row 12 | no |

**Why the primes sit outside all of them.**

* Liouville and Roth need a sparse placement, whereas `ρ` is dense.
* The complexity criteria need `p(L) = O(L)`. The prime residues are expected to have
  `p(L) = 2^L`, and are proved to have unbounded complexity.
* Mahler's method needs a functional equation, and none exists (`research/transcendence.md` §2).

Rows 8–9 are in the same position: squarefree residues provably have *maximal* complexity, so
they are farther from every criterion than the primes are known to be.

Of the three structures, "sparse", "low complexity" and "functional equation", the digit sequences
of number theory (primes, squarefree numbers, sums of two squares) have none. Only re-placing the
digits (row 15) brings them in reach. Row 15 is the one case inside Mathlib's current
transcendence theory, which is exactly Liouville's theorem.

## 5. What is checked here, what is from the literature

**Formalized (Lean, this branch).**

* `liouville_tsum_div_pow_factorial`, `liouville_tsum_div_two_pow_factorial`,
  `liouville_tsum_div_pow_succ_factorial`, `transcendental_tsum_div_two_pow_factorial`;
* `Real.frequently_rokickiDigit_eq_one`;
* `Real.rokickiLacunary`, `Real.liouville_rokickiLacunary`,
  `Real.transcendental_rokickiLacunary`, `Real.irrational_rokickiLacunary`.

**Checked numerically (`scripts/sequences.py`).**

* every value in §1 (exact enclosures), the periods, and the PSLQ results;
* Gauss's `x² + 64y²` criterion (`20000` primes) and `[b ≡ 2 mod 4] = [p ≡ 5 mod 8]` (all
  `p < 10^7`);
* the biases of §3.3;
* the failure of `B(x) = 2B(x/2) + O(1)`;
* squarefree complexity (all words for `L ≤ 4`; the missing words at `L = 5` are the rare ones);
* rotation-coding complexities `2L`, `L + 1`, `4L`;
* the Liouville exponents and the zero runs of Rokicki's digits.

**Sketches in this note** (not formalized, not checked against the literature):

* row 2 via the product `Π_S L(s, χψ_S)`;
* row 3 via Hadamard and the parity mismatch;
* row 4's coefficient `c = 1`;
* rows 8–9 (elementary irrationality and full complexity);
* the transcendence of row 16 via Roth (a direct application) and the Liouville property via
  Shiu;
* the explanation of the bias of row 5.

**From the literature.**

* Landau (sums of two squares);
* Mirsky (patterns of `r`-free numbers);
* Rote and Alessandri–Berthé (rotation complexity);
* Ferenczi–Mauduit and Adamczewski–Bugeaud (transcendence for low complexity);
* Mahler (Thue–Morse);
* Nesterenko (`Σ 2^{-k²}`);
* Shiu (runs of congruent primes);
* Roth;
* Gauss (quartic residuacity of `2`);
* Hecke (equidistribution of Gaussian prime angles; entire `L`-functions);
* Rubinstein–Sarnak (races);
* Bailey–Borwein–Crandall–Pomerance.

## References

* B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
  bases*, Ann. of Math. 165 (2007), 547–565.
* P. Alessandri, V. Berthé, *Three distance theorems and combinatorics on words*, Enseign. Math.
  44 (1998), 103–132.
* D. H. Bailey, J. M. Borwein, R. E. Crandall, C. Pomerance, *On the binary expansions of
  algebraic numbers*, J. Théor. Nombres Bordeaux 16 (2004), 487–518.
* S. Ferenczi, C. Mauduit, *Transcendence of numbers with a low complexity expansion*, J. Number
  Theory 67 (1997), 146–161.
* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen*,
  Math. Z. 1 (1918), 357–376; 6 (1920), 11–51.
* E. Landau, *Über die Einteilung der positiven ganzen Zahlen in vier Klassen nach der Mindestzahl
  der zu ihrer additiven Zusammensetzung erforderlichen Quadrate*, Arch. Math. Phys. 13 (1908).
* J. Liouville, *Sur des classes très étendues de quantités dont la valeur n'est ni algébrique,
  ni même réductible à des irrationnelles algébriques*, C. R. Acad. Sci. Paris 18 (1844).
* K. Mahler, *Arithmetische Eigenschaften der Lösungen einer Klasse von Funktionalgleichungen*,
  Math. Ann. 101 (1929), 342–366.
* L. Mirsky, *Note on an asymptotic formula connected with r-free integers*, Quart. J. Math. 18
  (1947), 178–182; *Arithmetical pattern problems relating to divisibility by rth powers*, Proc.
  London Math. Soc. (2) 50 (1949), 497–508.
* Yu. V. Nesterenko, *Modular functions and transcendence questions*, Sb. Math. 187 (1996),
  1319–1348.
* G. Rote, *Sequences with subword complexity 2n*, J. Number Theory 46 (1994), 196–213.
* K. F. Roth, *Rational approximations to algebraic numbers*, Mathematika 2 (1955), 1–20.
* M. Rubinstein, P. Sarnak, *Chebyshev's bias*, Experiment. Math. 3 (1994), 173–197.
* D. K. L. Shiu, *Strings of congruent primes*, J. London Math. Soc. 61 (2000), 359–373.
