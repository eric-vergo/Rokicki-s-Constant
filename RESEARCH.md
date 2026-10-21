# Research fork: beyond χ₄

This branch (`research/general-character`) extends the development on `main` without changing
it: everything new lives under `RokickiConstant/General/`, and `main`'s files are untouched.

## 1. The general theorem

**Theorem.** Let `q ≥ 1` and let `χ` be a Dirichlet character modulo `q` that is *quadratic*
(takes values in `{0, 1, -1}`) and nonprincipal. Write `p_0 = 2 < p_1 = 3 < …` for the primes and
`S(n) = Σ_{k<n} χ(p_k)`. Then

* `S` is not bounded, and
* `S(n)` is not of the form `c·n + O(1)` with `c ≠ 0`.

Equivalently, `Σ_{p ≤ x} χ(p)` is unbounded and is not `c·π(x) + O(1)` with `c ≠ 0`.

The proof is the one on `main` with `χ₄` replaced by `χ`: the Euler product
`L(s, χ) = exp(primePart + primePowerPart)` on `re s > 1`, the prime-power part holomorphic on
`re s > 1/2` and bounded on `re s ≥ 1`, its real part blowing up as `s → 1/2⁺` (this is where
`χ(p)² = 1` for all but finitely many primes is used: the finitely many primes dividing `q` only
shift the lower bound by a constant), and the identity theorem for the bounded case. Nothing
about `4` was ever used except `χ₄(p)² = 1`.

What is *not* covered: complex characters of order `> 2`. For those the `m = 2` terms of the
prime-power part involve `χ²`, a nontrivial character, whose Dirichlet series over primes does
not blow up at `1/2`; the bounded-partial-sum argument then only shows `L(s, χ) ≠ 0` on
`re s > 1/2`, which is consistent with GRH. Unboundedness of `Σ_{p≤x} χ(p)` for complex `χ` is
still true (Littlewood-type oscillation results) but needs genuinely more analytic input.

## 2. Corollaries: other bases, other moduli

**Digits are the invariant, the base is a reading.** If `d : ℕ → {0, …, b-1}` is not eventually
periodic then `Σ_k d_k / b^{k+1}` is irrational for every base `b ≥ 2`
(`irrational_tsum_div_pow` in `General/Expansion.lean`, the base-`b` version of the binary
lemma on `main`). The irrationality of Rokicki's constant is really the statement that the
*digit sequence* `[p_k ≡ 3 (mod 4)]` is not eventually periodic, which has nothing to do with
`2`. So:

* **Ternary, or any base.** `ρ_b = Σ_k [p_{k+2} ≡ 3 (mod 4)] / b^{k+1}` is irrational for every
  `b ≥ 2` (`Real.irrational_rokickiConstantBase`). These are different numbers for different
  `b` (`ρ_2 = 0.70040…`, `ρ_3 = 0.38334…`, `ρ_10 = 0.10110…`; see `scripts/constants.py`), not affine images of one another: the map
  "same digits, different base" is highly nonlinear (it is not even continuous in the usual
  topology). The question is uninteresting only in the sense that it is *free*: the proof is the
  same, because it was never about the base.

* **Other moduli, Legendre constants.** For any quadratic nonprincipal `χ` mod `q` and any
  encoding `f` of the values of `χ` as digits `< b` with `f(1) ≠ f(-1)`, the number
  `Σ_k f(χ(p_k)) / b^{k+1}` is irrational (`DirichletCharacter.IsQuadratic.irrational_tsum`).
  For an odd prime `ℓ`, taking `χ = (·/ℓ)` the Legendre symbol gives: the number whose `k`-th
  digit records whether `p_k` is a quadratic non-residue modulo `ℓ` is irrational
  (`Real.irrational_legendreConstant`); numerically `λ_(3,2) = 0.66716…`, `λ_(5,2) = 0.83824…`,
  `λ_(7,2) = 0.40299…`. Modulo `4` this recovers Rokicki's constant, modulo `8` there are two
  more such constants (`χ₈`, `χ₈'`), and so on.

* **Encoding the full residue `p mod q`.** For `q ≥ 3` the number
  `Σ_k (p_k mod q) / b^{k+1}` (any `b > q`) is irrational: its digits determine the residues,
  hence the values of any quadratic character mod `q`, and `(ℤ/q)^×` has even order so such a
  character exists. The existence step is not formalized on this branch; the prime-modulus
  case is, via the Legendre symbol.

## 3. Transcendence

Is `ρ` transcendental? Almost certainly, but this looks out of reach.

* The available transcendence criteria for digit expansions all require the digit sequence to
  be *simple* in some sense: automatic sequences (Adamczewski–Bugeaud, 2007), sequences of
  sublinear subword complexity, or Mahler-type functional equations. The sequence
  `[p_k ≡ 3 (mod 4)]` is expected to be the opposite: every finite `0/1` pattern should occur
  among consecutive primes (this is known: Shiu's theorem gives arbitrarily long constant
  strings, and Maynard–Tao type results give every pattern), so its subword complexity is
  maximal, `2^n`. Those criteria say nothing.

* Conversely, proving algebraicity is hopeless too: an algebraic irrational is conjectured to
  be normal in every base, and the Chebyshev bias says the digits `1` of `ρ` are "ahead" of the
  digits `0` for most `n`, although both have density `1/2`.

* What *can* be said with the present framework: the digit sequence is not eventually periodic
  (done), and, with more work, quantitative irrationality measures could follow from
  quantitative versions of the character-sum oscillation (how often and how far `S(n)` moves).
  Likewise, normality of `ρ` in base `2` would follow from a strong form of equidistribution of
  consecutive-prime residue patterns, which is far beyond current technology.

So the honest status: `ρ` is irrational (proved here, with the mechanism identified), its
transcendence is open and no current method applies, and the natural next theorems in this
framework are about the oscillation of `S(n)` rather than about the arithmetic nature of `ρ`.

A detailed treatment is in `research/transcendence.md` (the criteria, what each would need
from the primes, what is known about residues of consecutive primes, a rigorous bound on dyadic
approximations, and the ranked research directions) and `research/transcendence-evidence.md`
(computational evidence: PSLQ algebraicity tests, certified continued fraction statistics, digit
statistics; reproduced by `scripts/transcendence_evidence.py`).

## 4. Files

| File | Contents |
|---|---|
| `RokickiConstant/General/Expansion.lean` | base-`b` expansions: rationals have eventually periodic digits |
| `RokickiConstant/General/EulerProduct.lean` | `primeTerm`, `primePart`, `primePowerPart` for any Dirichlet character; Euler product; analytic properties; blow-up for quadratic characters |
| `RokickiConstant/General/CharacterSums.lean` | the general theorem: `Σ χ(p_k)` neither bounded nor linear |
| `RokickiConstant/General/Irrational.lean` | irrationality of `Σ f(χ(p_k)) / b^{k+1}`; Rokicki's constant in every base; Legendre constants |
| `research/transcendence.md` | the transcendence question: criteria, obstructions, directions |
| `research/transcendence-evidence.md` | computational evidence (PSLQ, continued fractions, digits) |
| `scripts/transcendence_evidence.py` | reproduces the evidence |
