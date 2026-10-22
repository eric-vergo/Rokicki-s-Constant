# Beatty residue constants: irrational (formalized), transcendental (literature)

**Status.** Irrationality is proved and formalized in `RokickiConstant/General/Beatty.lean`, with
no `sorry`. This is the Beatty item of Direction 4 in `PROGRAM.md` (see also `sequences.md` §2.5).
Transcendence is known from the literature (§4) but out of reach in Lean (§5). The numbers in §7
come from `python3 scripts/beatty.py`.

Notation: `α` is a real number, `m ≥ 2`, `a ∈ ℤ` is a residue, `b ≥ 2` is a base, `⌊·⌋ = Int.floor`,
`{·} = Int.fract`, and for `k = 0, 1, 2, …`

    d_k = [⌊kα⌋ ≡ a (mod m)],        x(α, m, a, b) = Σ_{k≥0} d_k / b^(k+1).

## 1. Theorems

**Theorem.** If `α` is irrational, then `(d_k)` is not eventually periodic. So
`x(α, m, a, b)` is irrational for every base `b ≥ 2`. If `α` is rational, then `(d_k)` is periodic
and `x(α, m, a, b)` is rational.

| Lean name | Statement |
|---|---|
| `Int.floor_emod_natCast_eq_floor_mul_fract` | `⌊y⌋ % m = ⌊m · {y/m}⌋` for `m > 0` |
| `Int.floor_emod_natCast_eq_iff` | `⌊y⌋ % m = j ↔ j ≤ m{y/m} < j + 1` |
| `Irrational.exists_nat_fract_add_mul_mem_Ico` | `γ` irrational, `[c, c+L) ⊆ [0,1)`, `L > 0` ⇒ `∃ n : ℕ, {x + nγ} ∈ [c, c+L)` |
| `Real.beattyDigit α m a k` | `if ⌊kα⌋ % m = a % m then 1 else 0` (as a `ℕ`) |
| `Real.not_eventuallyPeriodic_beattyDigit` | `Irrational α → 2 ≤ m → 0 < P → ¬ EventuallyPeriodic (beattyDigit α m a) P` |
| `Int.not_eventuallyPeriodic_floor_mul_emod` | the same, stated for the explicit `fun k ↦ if ⌊kα⌋ % m = a % m then 1 else 0` |
| `Real.beattyConstant α m a b` | `∑' k, (beattyDigit α m a k : ℝ) / b^(k+1)` |
| `Real.beattyConstant_eq` | the same value, with the indicator written as an `ℝ`-valued `if` |
| `Real.irrational_beattyConstant` | `Irrational α → 2 ≤ m → 2 ≤ b → Irrational (beattyConstant α m a b)` |
| `Real.beattyDigit_ratCast_add` | `beattyDigit r m a (k + r.den * m) = beattyDigit r m a k` for `r : ℚ` |
| `not_irrational_tsum_div_pow_of_periodic` | purely periodic base-`b` digits ⇒ rational value |
| `Real.not_irrational_beattyConstant_ratCast` | `0 < m → 2 ≤ b → ¬ Irrational (beattyConstant r m a b)` |

The statements allow any residue `a ∈ ℤ`, because only `a % m` matters. The case `m = 1` is
excluded and is genuinely different, since then `d ≡ 1`. The irrationality theorem reduces to
`irrational_tsum_div_pow` (`General/Expansion.lean`) with binary digits `d_k < 2 ≤ b`.

## 2. The rotation picture

Put `β = α/m`. Write `y/m = N + θ` with `N = ⌊y/m⌋` and `θ = {y/m} ∈ [0,1)`. Then
`⌊y⌋ = mN + ⌊mθ⌋` and `0 ≤ ⌊mθ⌋ < m`, so

    ⌊y⌋ mod m = ⌊m {y/m}⌋,    and    ⌊kα⌋ ≡ j (mod m)  ⟺  {kβ} ∈ I_j = [j/m, (j+1)/m).

So `d_k = 1_{I_{a'}}({kβ})` with `a' = a mod m`. In other words, `d` is the coding of the
rotation `R_β : t ↦ t + β` on `ℝ/ℤ`, started at `0`, with respect to the arc `I_{a'}` of length
`1/m`. The digit sequence of `sequences.md` row 10 is the case `α = √2`, `m = 4`, `a = 3`,
`β = √2/4`, `I = [3/4, 1)`.

## 3. Proof of non-periodicity (as formalized)

The formal proof is simpler than the endpoint argument (orbit points approaching `∂I` from both
sides). It needs only the forward orbit of one irrational rotation.

1. *Constancy along a progression.* Suppose `d(n + P) = d(n)` for all `n ≥ N`, with `P ≥ 1`. By
   induction, `d(N + tP) = d(N)` for every `t ∈ ℕ`.
2. *The progression sees every residue.* We have `(N + tP)α/m = Nβ + t·γ` with `γ = Pα/m`, and
   `γ` is irrational. The forward-orbit lemma (step 3) gives, for each `j ∈ {0, …, m-1}`, some
   `t` with `{Nβ + tγ} ∈ I_j`, that is `⌊(N + tP)α⌋ ≡ j (mod m)`.
3. *The forward orbit meets every arc* (`Irrational.exists_nat_fract_add_mul_mem_Ico`).
   Dirichlet's theorem (`Real.exists_nat_abs_mul_sub_round_le`) gives `k ≥ 1` with
   `δ = kγ - round(kγ)` satisfying `|δ| ≤ 1/(M+2) < L`. Also `δ ≠ 0`, since `kγ` is irrational.
   Modulo `1`, the points `x + s·kγ` are `x + sδ`, for `s ∈ ℕ`. They step by `|δ| < L` in one
   direction, so they cannot jump over the translate `[T, T + L)` of the arc. Take
   `T = ⌊x⌋ + 1 + c` and `s = ⌈(T - x)/δ⌉₊` if `δ > 0`, or `T = ⌊x⌋ - 1 + c` and
   `s = ⌊(x - T)/|δ|⌋₊` if `δ < 0`. Then `n = s·k` works.
4. *Contradiction.* Use step 2 with `j = a mod m` and with `j = (a+1) mod m`. These residues
   differ because `m ≥ 2`, so `d(N + t₁P) = 1` and `d(N + t₂P) = 0`. Both values equal `d(N)` by
   step 1.

*Rational slope.* If `α = p/q` in lowest terms, then `⌊(k + qm)p/q⌋ = ⌊kp/q⌋ + pm`, so `d` has
period `qm` from `k = 0`. A purely periodic expansion with period `P` has value
`S = A + S/b^P`, where `A = Σ_{k<P} d_k/b^(k+1)`, so `S = A·b^P/(b^P - 1) ∈ ℚ`. This lemma
(`not_irrational_tsum_div_pow_of_periodic`) is the converse half of `General/Expansion.lean`,
restricted to periodicity from the start.

## 4. Transcendence (literature, not formalized)

**These constants are transcendental.** This follows from two facts.

* **Complexity of the digit sequence.** A coding of an irrational rotation by `β` with respect to
  one interval of length `ℓ` has subword complexity `p(n) = 2n` for all large `n` when
  `ℓ ∉ ℤ + βℤ` (Rote 1994; Alessandri–Berthé 1998). When `ℓ ∈ ℤ + βℤ` the complexity is
  `n + const` eventually, and the coding is Sturmian (`p(n) = n + 1`) exactly when
  `ℓ ≡ ±β (mod 1)`. In our case `ℓ = 1/m` and `β = α/m`. If `1/m = j + kα/m`, then
  `1 = jm + kα`, which forces `k = 0` and then `jm = 1`. That is impossible for `m ≥ 2`. Hence
  `p(n) = 2n` for large `n`. The complete residue sequence `⌊kα⌋ mod m` codes `m` arcs. The `mn` points
  `j/m - iβ`, with `0 ≤ i < n` and `0 ≤ j < m`, are distinct mod `1`, so it has `p(n) = mn` for
  every `n` (checked for `m = 4` in §7).
* **Adamczewski–Bugeaud** (*On the complexity of algebraic numbers I. Expansions in integer
  bases*, Ann. of Math. 165 (2007)). The base-`b` expansion of an algebraic irrational number has
  `liminf p(n)/n = +∞`. So an irrational number with `p(n) = O(n)` in some integer base is
  transcendental.

Together with irrationality (§1, or directly because `p(n) = 2n` is unbounded), this gives:
**for irrational `α`, `m ≥ 2` and `b ≥ 2`, every Beatty constant `x(α, m, a, b)` is
transcendental.** In base `b > 2` the digits are still `0/1`, and the complexity is unchanged.

## 5. Why transcendence is not formalizable now

The Adamczewski–Bugeaud theorem is a consequence of the Schmidt subspace theorem, in the
`p`-adic form of Schlickewei (the "S-unit" subspace theorem). Mathlib has neither the subspace
theorem nor Roth's theorem, which is its one-dimensional case. Of the Diophantine approximation
results used for transcendence, it has only Liouville's. Formalizing Roth alone would be a large
project. The subspace theorem (geometry of numbers, Minkowski's second theorem, Schmidt's
parametric induction) is a much larger one. The irrationality proof above uses only Dirichlet's
pigeonhole theorem.

A Liouville-type shortcut does not apply in general either. Liouville's criterion needs very
good rational approximations, which come from very long repetitions near the start of the
expansion. For `α = √2`, which has bounded partial quotients, the digit sequence has no such
repetitions. Codings of rotations by very well approximable `α` can be Liouville numbers, but
that is a special case, not the theorem.

## 6. Contrast with the primes

| | Beatty: `[⌊kα⌋ ≡ a mod m]` | Primes: `[p_k ≡ a mod m]` (Rokicki) |
|---|---|---|
| shape | residue of an arithmetic sequence | same |
| underlying dynamics | rotation by `α/m` (zero entropy) | none known; "pseudorandom" |
| subword complexity | `p(n) = 2n` (eventually; proved) | conjecturally `2^n` (every pattern occurs, a prime `k`-tuples-type statement) |
| irrational | yes (this file, via Dirichlet approximation) | yes (repo, via character sums) |
| transcendental | **yes** (Adamczewski–Bugeaud 2007) | **open** |
| normal in base 2 | **no**: `p(n) = 2n < 2^n` | conjecturally yes (`General/Normal.lean`: conditional) |

The two constants look alike, with the same digit rule applied to different sequences. They sit
at opposite ends of the complexity scale. For low complexity, a combinatorics-to-Diophantine
transfer (the subspace theorem) proves transcendence. High complexity, with all patterns
present, is what one expects of a "random" number, and no transcendence method uses it. The
Beatty case shows that `[a_k ≡ a mod m]` constants are not transcendental by their shape. The
difficulty for the primes lies in the sequence, not in the encoding.

## 7. Numerical appendix (`python3 scripts/beatty.py`)

`α = √2`, `m = 4`, `a = 3`, `b = 2`. All digits are exact, since `⌊k√2⌋ = isqrt(2k²)`. The value
comes from 400 binary digits with an exact enclosure, `A/2^400 ≤ x ≤ (A+1)/2^400`.

    x = Σ_{k≥0} [⌊k√2⌋ ≡ 3 mod 4] 2^{-(k+1)}
      = 0.017852919410090714193070934252527836444225199127209007594861…   (60 decimals)

    d_0 … d_63 = 0000010010010010000000100100100100000001001001001000000010010010

The first `1` is `d_5`, since `⌊5√2⌋ = 7 ≡ 3`. The `1`s come in runs of period `3`, because
`3√2 ≈ 4.24 ≡ 0.24 (mod 4)`, which drifts slowly. `sequences.md` (row 10) lists `0.0357058388`.
That number weights `d_k` by `2^{-k}` instead of `2^{-(k+1)}`, so it is exactly `2x`.

Subword complexity over the prefix `k < 10^6`:

| `n` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11–20 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `p(n)`, `[⌊k√2⌋ ≡ 3 mod 4]` | 2 | 3 | 4 | 6 | 8 | 11 | 14 | 16 | 18 | 20 | `2n` |
| `p(n)`, Sturmian `⌊(k+1)√2⌋ - ⌊k√2⌋ - 1` | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | `n + 1` |
| `p(n)`, `⌊k√2⌋ mod 4` | 4 | 8 | 12 | 16 | 20 | 24 | 28 | 32 | 36 | 40 | `4n` |

So `p(n) = 2n` for `n = 1` and for all `7 ≤ n ≤ 20`. For `2 ≤ n ≤ 6` the value is below `2n`, as
expected before the eventual regime. This matches `sequences.md` §2.5 ("`p(L) = 2L` for
`L ≥ 7`").
