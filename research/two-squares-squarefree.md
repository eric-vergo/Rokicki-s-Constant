# Sums of two squares and squarefree numbers in place of the primes

**Status.** Part of Direction 4 (`PROGRAM.md`; rows 7–9 of `sequences.md`). Formalized in
`RokickiConstant/General/TwoSquares.lean`, with no `sorry` and only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`):

* **Squarefree numbers, unconditional.** Every finite word over the residues `{1, 2, 3}` occurs,
  arbitrarily late, as the residues mod `4` of consecutive squarefree numbers. So every digit
  `g(u_k mod 4)` that is not constant on `{1, 2, 3}` is not eventually periodic, and its constant
  is irrational in every base. This covers row 9 of `sequences.md`, `[u_k ≡ 3 mod 4]`. The proof
  is a CRT construction plus a union bound over primes (§4); it replaces Mirsky's pattern count.
* **Sums of two squares, unconditional.** The digits `[s_k is a square]` and `[s_k is prime]`
  are not eventually periodic, so their constants are irrational (§3.2, §3.3).
* **Sums of two squares, conditional.** The parity digit `[s_k odd]` (row 8) is not eventually
  periodic if `B(n)/n → 0` and `B(n)/B(2n) → 1/2`; in particular if Landau's asymptotic
  `B(n) ~ K n/√(log n)` holds (§3.4). Landau is not in Mathlib. An elementary unconditional proof
  exists on paper (§3.5) but is not formalized.
* **Open here.** Finer residue digits of the sums of two squares, such as `[s_k ≡ 1 mod 8]`
  (§3.6), and the transcendence of all of these constants.

The numbers in §5 come from `python3 scripts/two_squares.py` (about 15 seconds).

Notation. `S = {n ≥ 1 : n = x² + y²}`, enumerated `s_0 = 1 < s_1 = 2 < 4 < 5 < 8 < …`, with
counting function `B(x) = #(S ∩ [1, x])`. The squarefree numbers are `u_0 = 1 < u_1 = 2 < 3 < 5 < …`.
For a digit rule `d_k ∈ {0, …, b-1}` the constant is `x = Σ_k d_k b^{-(k+1)}`. It is irrational
exactly when `(d_k)` is not eventually periodic (`irrational_tsum_div_pow`).

## 1. Theorems

| Lean name | Statement |
|---|---|
| `Function.not_eventuallyPeriodic_of_runs` | arbitrarily late runs of `v` of every length, and values `≠ v` arbitrarily late ⇒ not eventually periodic |
| `Nat.exists_run_nth_of_window` | windows `[M, M+W)` with `≥ L` elements of `p`, all in `B`, arbitrarily far out ⇒ runs of length `L` in `B` along `nth p` |
| `Nat.exists_nth_of_frequently` | `A` holds at arbitrarily large elements of `p` ⇒ `A (nth p k)` for arbitrarily large `k` |
| `Nat.IsSumTwoSq`, `Nat.sumTwoSq`, `Nat.sumTwoSqCount` | `S`, its enumeration `s_k`, its counting function `B(n) = #(S ∩ [1, n])` |
| `Nat.Prime.isSumTwoSq` | Fermat: `p` prime, `p % 4 ≠ 3` ⇒ `p ∈ S` |
| `Nat.exists_window_isSumTwoSq_not_isSquare` | windows of `S` without squares |
| `Nat.not_eventuallyPeriodic_sumTwoSqSquareDigit` | `[s_k is a square]` is not eventually periodic |
| `Nat.exists_window_isSumTwoSq_not_prime` | windows of `S` without primes |
| `Nat.not_eventuallyPeriodic_sumTwoSqPrimeDigit` | `[s_k is prime]` is not eventually periodic |
| `Real.irrational_sumTwoSqSquareConstant`, `Real.irrational_sumTwoSqPrimeConstant` | the two constants are irrational in every base `b ≥ 2` |
| `Nat.isSumTwoSq_two_mul_iff` | `2n ∈ S ↔ n ∈ S` |
| `Nat.sum_mod_two_add_count` | `B(2n) = #{odd s ∈ S, s ≤ 2n} + B(n)` |
| `Nat.not_eventuallyPeriodic_sumTwoSq_mod_two_of_tendsto` | `B(n)/n → 0` and `B(n)/B(2n) → 1/2` ⇒ `s_k mod 2` is not eventually periodic |
| `Nat.not_eventuallyPeriodic_sumTwoSq_mod_two_of_landau` | `B(n)√(log n)/n → K > 0` ⇒ the same |
| `Real.irrational_sumTwoSqParityConstant_of_landau` | under Landau, `Σ (s_k mod 2)/b^{k+1}` is irrational |
| `Nat.squarefreeNth` | `u_k` |
| `Nat.card_filter_not_squarefree_le` | the sieve bound (§4.2) |
| `Nat.nth_count_add_eq_of_window` | an exact window gives consecutive elements of `nth p` |
| `Nat.exists_squarefreeNth_mod_four_eq` | every word `w` with `w_t ≢ 0 (mod 4)` occurs: `∃ k ≥ N, ∀ t < L, u_{k+t} ≡ w_t (mod 4)` |
| `Nat.not_eventuallyPeriodic_squarefreeNth_mod_four` | `g(r₁) ≠ g(r₂)` for nonzero residues `r₁, r₂` ⇒ `g(u_k mod 4)` is not eventually periodic |
| `Real.irrational_tsum_squarefreeNth_mod_four` | the same digits, with values `< b`, give irrational constants |
| `Real.irrational_squarefreeConstant` | `Σ [u_k ≡ 3 mod 4]/b^{k+1}` is irrational (row 9) |
| `Real.irrational_tsum_squarefreeNth_mod_four_div_four_pow` | `Σ (u_k mod 4)/4^{k+1}` is irrational |

## 2. The run principle

**Lemma.** Let `d` be eventually periodic with period `P`, so that `d(n + P) = d(n)` for
`n ≥ N`. If `d(k) = d(k+1) = ⋯ = d(k+P-1) = v` for some `k ≥ N`, then `d(n) = v` for all `n ≥ k`.

So a sequence that has arbitrarily late runs of `v` of every length, and that takes a value
`≠ v` arbitrarily late, is not eventually periodic. This is how every unconditional result below
is proved. Runs along the enumeration `nth p` come from *windows*: an interval `[M, M + W)` of
integers that contains at least `L` elements of `p`, all with the property `B`. The elements of
`p` in the window are consecutive in the enumeration, starting at index `count p M`.

The point of runs is that they need control of *every* element of the sequence in a window. So
each proof below has two parts: inclusion (enough elements in the window) and exclusion (every
element in the window has the property).

## 3. Sums of two squares

### 3.1 The candidate digits

| Digit `d_k` | `x` (base 2) | Status | Input |
|---|---|---|---|
| `[s_k ≡ 3 mod 4]` | `0` | rational | `x² + y² ≢ 3 (mod 4)` |
| `[s_k odd] = [s_k ≡ 1 mod 4]` | `0.5831631619` | irrational if `B(n)/n → 0`, `B(n)/B(2n) → 1/2` (**Lean**); unconditional on paper (§3.5) | doubling `2S = S ∩ 2ℕ` |
| `[s_k ≡ 0 mod 4]` | `0.1584673252` | same as parity (paper) | `4S = S ∩ 4ℕ` |
| `[s_k ≡ 2 mod 4]` | `0.2583695129` | same as parity (paper) | `2·(S ∩ odd) = S ∩ (2 mod 4)` |
| `[p ∣ s_k]`, `p = 2` or `p ≡ 1 mod 4`; `[q ∣ s_k]`, `q ≡ 3 mod 4` | — | same as parity (paper) | `pS = S ∩ pℕ`, `q²S = S ∩ qℕ` |
| `[s_k ≡ 1 mod 8]` | `0.5167242299` | **open here** | no self-similarity (§3.6) |
| `[s_k is a square]` | `0.6427041311` | **irrational (Lean)** | windows `(t², (t+1)²)` |
| `[s_k is prime]` | `0.3174157330` | **irrational (Lean)** | windows `t² + [2, R]`, `R! ∣ t` |

### 3.2 The square digit

Between `t²` and `(t+1)²` there is no square. The numbers `t² + b²`, `1 ≤ b ≤ L`, lie in `S` and
inside this interval once `L² < 2t`. With `t = L² + N + 1` this gives windows arbitrarily far out
with at least `L` elements of `S` and no square, hence runs of `0`s. The value `1` recurs at every
square. ∎

### 3.3 The prime digit

Let `R = (L + 2)²` and `t = R!·(N + 1)`. For `2 ≤ j ≤ R` we have `j ∣ t`, so `j ∣ t² + j`, and
`t² + j` is composite. The window `[t² + 2, t² + R]` contains the `L` elements `t² + b²`,
`2 ≤ b ≤ L + 1`, of `S`, and no prime at all. The value `1` recurs at the infinitely many primes
`p ≡ 1 (mod 4)` (Mathlib's `Nat.exists_prime_gt_modEq_one`), which lie in `S` by Fermat. ∎

The prime digit picks out the norms of the degree-one Gaussian primes among all norms. It is
`0.3174157330…` in base 2.

### 3.4 The parity digit (formalized, conditionally)

**Exact identity.** `n ∈ S ⇔ 2n ∈ S`. The forward direction is `2(x² + y²) = (x+y)² + (x-y)²`.
For the converse, `2n = a² + b²` forces `a ≡ b (mod 2)`; writing `a = b + 2e` gives
`n = (b + e)² + e²`. So the even elements of `S` up to `2n` are the doubles of the elements up
to `n`:

    B(2n) = O(2n) + B(n),        O(x) = #{s ∈ S odd, s ≤ x}.        (D)

**Argument.** Suppose `d_k = s_k mod 2` is eventually periodic with period `P`. Then its partial
sums are `Σ_{k<K} d_k = cK + O(1)`, with `c` the mean over a period
(`Function.EventuallyPeriodic.exists_abs_sum_sub_mul_le`). Also `O(x) = Σ_{k < B(x)} d_k`. So by
(D):

    |B(n) − (1 − c)·B(2n)| ≤ C        for all n.        (*)

1. Divide (*) by `B(2n) → ∞`: `B(n)/B(2n) → 1 − c`. The hypothesis `B(n)/B(2n) → 1/2` forces
   `c = 1/2`.
2. Then `B(2n) − 2C ≥ 2(B(n) − 2C)`. Take `n₀` with `B(n₀) ≥ 2C + 1`. Then
   `B(2^j n₀) ≥ 2^j`, so `B(x)/x ≥ 1/n₀` along `x = 2^j n₀`. This contradicts `B(x)/x → 0`. ∎

Both hypotheses follow from Landau's theorem `B(x) ~ K x/√(log x)`, with
`K = 0.7642236535…` the Landau–Ramanujan constant. The Lean corollary
`not_eventuallyPeriodic_sumTwoSq_mod_two_of_landau` takes `B(n)√(log n)/n → K > 0` as its only
hypothesis.

The same argument works for the other self-similar digits in the table:

* **`[s_k ≡ 0 mod 4]`.** Here `#{s ≤ x : 4 ∣ s} = B(x/4)`, so `B(x/4) = cB(x) + O(1)`. Landau
  gives `c = 1/4`, and then `B(4^j y) ≥ 4^j(B(y) − C')`, contradicting density zero.
* **`[s_k ≡ 2 mod 4]`.** Here `#{s ≤ x : s ≡ 2 (4)} = O(x/2) = B(x/2) − B(x/4)`. Periodicity
  and Landau give `B(x) = 4B(x/2) − 4B(x/4) + O(1)`. The characteristic root `2` is double, so
  `B(2^j y) = (a + bj)·2^j + O(1)`, because the second differences of `B(2^j y)/2^j` are
  `O(2^{-j})`. Density zero forces `a = b = 0`, and then `B(2^j y) = O(1)`, which is absurd.
* **`[m ∣ s_k]`.** For `m = p` (with `p = 2` or `p ≡ 1 mod 4`) or `m = q²` (with `q ≡ 3 mod 4`),
  we have `#{s ≤ x : m ∣ s} = B(x/m)`, and the argument is the same with `m` in place of `4`.

### 3.5 An elementary unconditional proof of the parity case (sketch, not formalized)

Landau can be avoided. Run the argument with a free `c`, writing `β = 1 − c`. By (*):

* **`β < 1/2`.** `B(2n) ≥ (B(n) − C)/β` makes `B` grow faster than `x^{1+δ}`, which is absurd
  since `B(x) ≤ x`.
* **`β = 1/2`.** This is step 2 of §3.4. It needs only **density zero**, `B(x) = o(x)`.
* **`β > 1/2`.** `B(2n) + C' ≤ (B(n) + C')/β` gives `B(x) ≪ x^θ` with `θ = log₂(1/β) < 1`. This
  is contradicted by `B(x) ≥ x^{1−o(1)}`.

Both inputs are elementary:

* **Density zero.** Let `A_F` be the set of `n` with `¬(q ∥ n)` for every `q` in a finite set `F`
  of primes `≡ 3 (mod 4)`. Then `S ⊆ A_F`. Counting `A_F` needs no CRT, only the exact recursion
  `A_{F∪{q}}(x) = A_F(x) − A_F(x/q) + A_F(x/q²)`. This gives
  `A_F(x) = x ∏_{q∈F}(1 − 1/q + 1/q²) + O(3^{|F|})`, and the product tends to `0` because
  `Σ_{q ≡ 3 (4)} 1/q = ∞`. Mathlib has `not_summable_residueClass_prime_div`, which is
  `Σ_{p ≡ a} log p/p = ∞`. That is weaker than what we need; the divergence of `Σ 1/p` would
  come from Mertens' theorem in progressions, which Mathlib lacks.
* **`B(x) ≥ x^{1−o(1)}`.** About `πx/4` lattice points have `x² + y² ≤ x`. Each `n` has
  `r₂(n) ≤ 4d(n) = n^{o(1)}` representations (Jacobi's `r₂ = 4Σ_{d∣n} χ₄(d)` and the divisor
  bound). A cheaper bound is not enough. For example, the values `A² + b²` with `A ≍ √x` and
  `b < x^{1/4}` are pairwise distinct, but they give only `B(x) ≫ x^{3/4}`. That rules out only
  `β ≥ 2^{-3/4}`.

So the parity, `0 mod 4` and `[m ∣ s_k]` constants are unconditionally irrational: the same case
analysis applies with `m` in place of `2`. For `2 mod 4` the analysis runs over the roots of
`cλ² = λ − 1`, using `u_j = B(2^j y)`:

* complex roots (`c > 1/4`) have `|λ| < 2`;
* a double root (`c = 1/4`) gives `λ = 2`;
* for real roots (`c < 1/4`), `λ₊ > 2 > λ₋`.

The bound `B(x) ≤ x` kills the `λ₊` component. The lower bound kills `|λ| < 2`, and density zero
kills `λ = 2`. The obstruction to formalizing any of this is the two pieces of analytic number
theory that Mathlib lacks.
The numerics (§5) show `B(x) − 2B(x/2)` growing like Landau's prediction
`−K x log 2/(2(log x)^{3/2})`, so the `O(1)` that periodicity would demand fails visibly.

**Why counting is the only handle for residue digits.** For `n ↦ 2n`, the frequencies `1/2, 1/4,
1/4` of the residues `1, 0, 2` inside `S` are forced by self-similarity together with Landau's
regular variation. So a residue digit can never be refuted at the level of main terms. The
contradiction comes from the *error term*: periodicity demands `O(1)`, and self-similarity
amplifies the error along `x, 2x, 4x, …` until it collides with density zero. Runs (§2) do not
work here, because forcing many consecutive elements of `S` into one residue class requires
excluding the elements of `S` in the other classes. Exclusion by CRT works one integer at a
time, but inclusion in `S` is not a sieve-positive property: `S` has density `0`, so no union
bound can certify membership. Only explicit families such as `t² + b²` can, and their residues
alternate.

### 3.6 Open: digits without self-similarity

`[s_k ≡ 1 mod 8]` splits the odd elements of `S` into `1 mod 8` (`b ≡ 0 mod 4`) and `5 mod 8`
(`b ≡ 2 mod 4`). Neither class is a dilate of `S`. Periodicity would give
`B(x; 8, 1) = cB(x) + O(1)`, and the Landau-type asymptotics in progressions force `c = 1/4`
(numerically the frequency is `0.2427`). A contradiction
needs `B(x; 8, 1) − B(x)/4` to be unbounded, that is, a two-term expansion of `B(x; 8, a)` with
*different* secondary constants for `a = 1` and `a = 5`. The numerics show a growing bias
`B(x;8,1) − B(x;8,5) = 3, 4, 12, 42, 128` at `x = 10^3, …, 10^7`. We know no elementary route.
The same applies to every residue digit modulo `2^e` with `e ≥ 3`, and to residues modulo primes
`p ≡ 1 (mod 4)` that are not divisibility conditions.

## 4. Squarefree numbers

### 4.1 Theorem (formalized)

**Theorem.** Let `w_0, …, w_{L−1}` be residues with `w_t ≢ 0 (mod 4)`, and let `N ≥ 0`. Then
there is `k ≥ N` with `u_{k+t} ≡ w_t (mod 4)` for all `t < L`.

So the residue sequence `u_k mod 4` has subword complexity `3^L`, and the digit `[u_k ≡ 3 mod 4]`
has complexity `2^L`. Every rule `g(u_k mod 4)` that separates two of the residues `1, 2, 3` has
arbitrarily long runs of each value, and so it is not eventually periodic (§2). Its constant is
irrational in every base.

### 4.2 Proof

Fix the word and `N`. Put

    K = 4L + 2,    G = (K!)²,    f(t) = tG + w_t  (w_t ∈ {1, 2, 3}),    W = (L + 1)G.

The candidates are `M + f(t)`, `t < L`. The window is `[M, M + W)`.

1. **Small primes cannot divide a candidate twice.** Suppose `G ∣ M`. Every prime `p ≤ K` has
   `p² ∣ G`, so `M + f(t) ≡ w_t (mod p²)`, and `p² ∤ w_t` because `1 ≤ w_t ≤ 3 < 4 ≤ p²`.
   Moreover `4 ∣ G`, so `M + f(t) ≡ w_t (mod 4)`.
2. **Every other integer in the window is killed.** For each offset `j < W` that is not a
   candidate position, take its own prime `q_j > W + K`. The `q_j` are distinct, for instance
   `q_j = nth Prime (W + K + 1 + j)`. Impose `M + j ≡ 0 (mod q_j²)`. Together with `M ≡ 0 (mod G)`
   these congruences have pairwise coprime moduli, so by CRT
   (`Nat.chineseRemainderOfFinset`) they define a progression `M = a₀ + Qm`, `m ≥ 0`, with
   `Q = G·∏ q_j²`.
3. **The `q_j` cannot divide a candidate twice.** If `q_j² ∣ M + f(t)`, then also
   `q_j² ∣ M + j`, so `q_j² ∣ |f(t) − j|`. But `0 < |f(t) − j| < W < q_j`, a contradiction.
4. **Sieve over the remaining primes.** Steps 1 and 3 show that any prime `p` with
   `p² ∣ a₀ + f(t) + Qm` satisfies `p > K` and `gcd(p, Q) = 1`. For such `p` the bad `m < Y`
   form a single class mod `p²`, so there are at most `Y/p² + 1` of them. Bounding the primes by
   all integers in `(K, B)`, with `B = ⌊√(a₀ + QY + W)⌋ + 1`, gives

       #{m < Y : a₀ + f(t) + Qm not squarefree} ≤ Y·Σ_{n>K} 1/n² + B ≤ 2Y/(K + 1) + B.

   This uses only `Σ_{n=K+1}^∞ 1/n² ≤ 2/(K+1)` (Mathlib's `sum_Ioo_inv_sq_le`). Summing over the
   `L` candidates gives at most `2LY/(4L + 3) + LB < Y/2 + LB` bad `m`.
5. **Choice of `Y`.** Take `Y = QH²` with `H = 2LQ + 2N' + 2L(a₀ + W + 1) + 1`, where
   `N' = u_N`. Then `B ≤ QH + a₀ + W + 1` and `2N' + 2LB < Y`, so `Y − N' > Y/2 + LB`, and
   some `m ∈ [N', Y)` is good.
6. **Reading off the word.** For such an `m`, put `M = a₀ + Qm`. The squarefree numbers in
   `[M, M + W)` are exactly the `L` candidates. By `nth_count_add_eq_of_window` they are
   `u_{k}, …, u_{k+L−1}` with `k = #{squarefree < M} ≥ N`, and `u_{k+t} ≡ w_t (mod 4)`. ∎

**Comparison with Mirsky.** Mirsky (1947/49) proves an asymptotic density
`c_J = ∏_p (1 − ρ_J(p)/p²) > 0` for every admissible pattern `J`, by inclusion–exclusion over
squares. For non-periodicity only *existence* is needed. The gap `G = (K!)²` makes every prime
`≤ K` harmless at once. That leaves a tail `Σ_{p>K} 1/p² < 1/(2L)` small enough for a naive union
bound, which is the "|J| = 1 sieve" of the task statement extended to any `|J|`. The price is
that the windows produced are astronomically far out, while numerically every word of length
`≤ 4` occurs among the first `4·10^6` squarefree numbers (§5).

### 4.3 Extensions (paper)

* **Other moduli.** For a modulus `m`, call a residue `r` *admissible* if some squarefree number
  is `≡ r (mod m)`, equivalently if `gcd(r, m)` is squarefree. The same proof shows that every
  word over the admissible residues occurs: pick squarefree representatives `r'_t` of the
  letters, and take `G` divisible by `m` and by `(K!)²`, with `K` larger than every `r'_t` and
  than `4L`. Hence every non-constant digit of `u_k mod m` (on the admissible residues) gives an
  irrational constant.
* **`r`-free numbers.** Replace squares by `r`-th powers. The tail is `Σ_{n>K} n^{-r}`.
* **Frequencies.** Each residue `1, 2, 3` has density `1/3` among the squarefree numbers. This is
  elementary (`Q(x; 4, a) = (2/π²)x + O(√x)`), not formalized. So the constant `[u_k ≡ 3 mod 4]`
  is not normal in base `2`.
* **The analytic route** (`sequences.md` §2.4) needs the zeros of `ζ`, so the combinatorial proof
  is strictly better here.

### 4.4 Open

Transcendence of any of these constants. Every criterion that needs low complexity is excluded,
since the complexity is maximal (`3^L`). The question is open for the same reasons as for `ρ`
(`transcendence.md` §2).

## 5. Numerics (`scripts/two_squares.py`)

All digits are exact (integer sieves to `10^7`: `1 985 458` sums of two squares, `6 079 291`
squarefree numbers). Each value is certified by an enclosure from `3400` binary digits. Periods
are searched up to `1000` in the first `2·10^5` digits. PSLQ is run on `[1, x, …, x^d]`, `d ≤ 6`,
at `300` digits with `maxcoeff = 10^25`.

| Constant (base 2) | Value | Density of 1s | Period ≤ 1000 | PSLQ |
|---|---|---|---|---|
| `[s_k ≡ 3 mod 4]` | `0` | `0` | `1` | trivial |
| `[s_k odd]` | `0.583163161899006641417966108957403026222839604505388196161845` | `0.4851` | none | none |
| `[s_k ≡ 0 mod 4]` | `0.158467325178351787824772061689679294768440735448617586477240` | `0.2657` | none | none |
| `[s_k ≡ 2 mod 4]` | `0.258369512922641570757261829352917679008719660045994217360913` | `0.2492` | none | none |
| `[s_k ≡ 1 mod 8]` | `0.516724229923515307919856305241511326774695357522527229212751` | `0.2427` | none | none |
| `[s_k is a square]` | `0.642704131096366374640347063267539029360237572215442541708314` | `0.0048` | none | none |
| `[s_k is prime]` | `0.317415733009124075286761798906194100943009884104051091868920` | `0.1818` | none | none |
| `[u_k ≡ 3 mod 4]` | `0.145157950763207290830828628322408224741010664101114683264767` | `0.3334` | none | none |
| `[u_k ≡ 1 mod 4]` | `0.564762659521097405689079051482059847483551042820869230003149` | `0.3333` | none | none |
| `[u_k ≡ 2 mod 4]` | `0.290079389715695303480092320195531927775438293078016086732082` | `0.3333` | none | none |
| `Σ (u_k mod 4)/4^{k+1}` | `0.428641191592240441080131406338596903910001190940257119772959` | — | — | — |

The values of rows 8 and 9 agree with `sequences.md`. The parity density `0.4851` and the
`0 mod 4` density `0.2657` drift slowly towards `1/2` and `1/4`, as Landau's secondary term
predicts.

**Landau and the quantities that periodicity would bound.**

| `x` | `B(x)` | `B√(log x)/x` | `O/B` | `B(x) − 2B(x/2)` | Landau pred. | `B(x) − 4B(x/4)` | `B(x/2) − B(x/4) − B(x)/4` | `B(x;8,1) − B(x;8,5)` |
|---|---|---|---|---|---|---|---|---|
| `10^3` | `329` | `0.8655` | `0.4650` | `−23` | `−15` | `−51` | `−1.2` | `3` |
| `10^4` | `2748` | `0.8341` | `0.4753` | `−136` | `−95` | `−292` | `−5.0` | `4` |
| `10^5` | `24027` | `0.8153` | `0.4815` | `−891` | `−678` | `−1901` | `−29.8` | `12` |
| `10^6` | `216340` | `0.8041` | `0.4852` | `−6416` | `−5158` | `−13432` | `−150.0` | `42` |
| `10^7` | `1985458` | `0.7971` | `0.4877` | `−48850` | `−40930` | `−101538` | `−959.5` | `128` |

`B√(log x)/x` decreases slowly towards `K = 0.7642…`, as expected from the secondary term
`∝ 1/log x`. Each of the three columns that periodicity of a self-similar digit would make `O(1)`
grows roughly like `x/(log x)^{3/2}`.

**Runs.** The longest run of `0`s below `10^7` is `1223` for the square digit (at `k = 1979035`)
and `54` for the prime digit (at `k = 912792`, `s_k = 4468897…4469140`). The Lean windows for
the prime digit sit at `t = R!·(N+1)`, far beyond any computation.

**Squarefree words.** All `3^L` words occur for `L ≤ 4`, and `225` of the `243` words of length
`5` occur among the first `6·10^6` squarefree numbers. The `18` missing words (`11111`, `22222`,
`33333`, `11113`, …) all need several specific numbers not divisible by `4` to be
non-squarefree, so they are rare, not impossible: the theorem guarantees each of them. The first
runs of length `L` of each residue occur at index

| residue | `L = 2` | `L = 3` | `L = 4` |
|---|---|---|---|
| `1` | `60` | `26997` | `3694408` |
| `2` | `257` | `1537` | `1017842` |
| `3` | `30` | `28904` | `809585` |

No run of length `5` occurs below `10^7`, which is consistent with the `L = 5` gaps above.

## References

* E. Landau, *Über die Einteilung der positiven ganzen Zahlen in vier Klassen nach der Mindestzahl
  der zu ihrer additiven Zusammensetzung erforderlichen Quadrate*, Arch. Math. Phys. (3) 13
  (1908), 305–312.
* L. Mirsky, *Note on an asymptotic formula connected with r-free integers*, Quart. J. Math. 18
  (1947), 178–182; *Arithmetical pattern problems relating to divisibility by rth powers*, Proc.
  London Math. Soc. (2) 50 (1949), 497–508.
* P. Fermat / L. Euler: primes `p ≡ 1 (mod 4)` are sums of two squares (Mathlib
  `Nat.Prime.sq_add_sq`).
