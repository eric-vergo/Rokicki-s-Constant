# Rokicki's constant

A Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4) formalization of
**Rokicki's constant**

    ρ = Σ_{k ≥ 2} [p_k ≡ 3 (mod 4)] / 2^(k-1) = 0.70040013796579773…

where `3 = p_2 < p_3 < …` are the odd primes, and of the theorem that `ρ` is irrational.

`ρ` is the limit of `A362583(n) / 2^(n-1)`, where [OEIS A362583](https://oeis.org/A362583) is the
integer whose binary digits record, prime by prime, whether `p_k ≡ 3 (mod 4)`. Tom Rokicki
observed that this normalized sequence converges.

## Main result

```lean
theorem Real.irrational_rokickiConstant : Irrational Real.rokickiConstant
```

The proof does not use the prime number theorem. If `ρ` were rational its binary digits would be
eventually periodic, so the partial sums `Σ_{k<n} χ₄(p_{k+2})` of the nontrivial Dirichlet
character modulo `4` over the odd primes would be `c·n + O(1)`. Both `c ≠ 0` and `c = 0` are
ruled out by the Euler product `L(s, χ₄) = exp(Σ_p χ₄(p) p^{-s} + Σ_p Σ_{m≥2} χ₄(p)^m p^{-ms}/m)`:
the first by letting `s → 1⁺` (where `L(1, χ₄) ≠ 0`), the second by continuing the identity to
`re s > 1/2` and letting `s → 1/2⁺`, where the prime-power part blows up while the entire
function `L(·, χ₄)` stays bounded.

## Layout

| File | Contents |
|---|---|
| `RokickiConstant/Defs.lean` | `Real.rokickiDigit`, `Real.rokickiConstant`, the odd primes, link to `ZMod.χ₄` |
| `RokickiConstant/BinaryExpansion.lean` | rationals have eventually periodic binary expansions |
| `RokickiConstant/PartialSums.lean` | partial sums of eventually periodic sequences; summation by parts; Abel series |
| `RokickiConstant/LSeriesChi4.lean` | Euler product of `L(s, χ₄)`; the character sums are neither bounded nor linear |
| `RokickiConstant/Irrational.lean` | the main theorem |
| `scripts/rho.py` | numerical reference computation of `ρ` |

## Building

Requires [elan](https://github.com/leanprover/elan). Then

```bash
lake exe cache get && lake build
```
