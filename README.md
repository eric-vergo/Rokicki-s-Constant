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
noncomputable def rho : ℝ :=
  ∑' k : ℕ, (if Nat.nth Nat.Prime (k + 1) % 4 = 3 then (1 : ℝ) else 0) / 2 ^ (k + 1)

theorem rho_irrational : Irrational rho
```

stated in `Comparator/Challenge.lean` and proved in `Comparator/Solution.lean`.

The proof does not use the prime number theorem. If `ρ` were rational its binary digits would be
eventually periodic, so the partial sums `Σ_{k<n} χ₄(p_{k+2})` of the nontrivial Dirichlet
character modulo `4` over the odd primes would be `c·n + O(1)`. Both `c ≠ 0` and `c = 0` are
ruled out by the Euler product `L(s, χ₄) = exp(Σ_p χ₄(p) p^{-s} + Σ_p Σ_{m≥2} χ₄(p)^m p^{-ms}/m)`:
the first by letting `s → 1⁺` (where `L(1, χ₄) ≠ 0`), the second by continuing the identity to
`re s > 1/2` and letting `s → 1/2⁺`, where the prime-power part blows up while the entire
function `L(·, χ₄)` stays bounded.

### A second proof, by the prime number theorem

```lean
theorem RokickiConstant.PNT.rho_irrational : Irrational rho
```

in `RokickiConstantPNT/MainTheorem.lean` proves the same statement with the case `c ≠ 0` handled
by the prime number theorem in arithmetic progressions, taken from the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project
(`WeakPNT_AP`). If `Σ_{k<n} χ₄(p_{k+2}) = c·n + O(1)`, summation by parts against the weights
`log p` gives `(1 - c)·ϑ(x; 4, 1) - (1 + c)·ϑ(x; 4, 3) = O(log x)` along the primes `x`, where
`ϑ(x; 4, a) = Σ_{p < x, p ≡ a (mod 4)} log p`. The prime number theorem gives
`ϑ(x; 4, a) = x/2 + o(x)` for `a = 1, 3`, so the left side is `-c·x + o(x)` and `c = 0`.

The case `c = 0` is the same in both proofs. The prime number theorem does not decide it: it
gives `π(x; 4, 1) - π(x; 4, 3) = o(π(x))`, which is what bounded partial sums predict.

## Layout

| File | Contents |
|---|---|
| `RokickiConstant/Defs.lean` | `Real.rokickiDigit`, `Real.rokickiConstant`, the odd primes, link to `ZMod.χ₄` |
| `RokickiConstant/BinaryExpansion.lean` | rationals have eventually periodic binary expansions |
| `RokickiConstant/PartialSums.lean` | partial sums of eventually periodic sequences; summation by parts; Abel series |
| `RokickiConstant/Chi4.lean` | the character `chi4` at the odd primes; sums over the primes; divergence of `Σ_p p^(-σ)` as `σ → 1⁺` |
| `RokickiConstant/EulerProduct.lean` | Euler product of `L(s, χ₄)` as `exp (primePart + primePowerPart)`; analytic properties of the prime-power part |
| `RokickiConstant/CharacterSums.lean` | the partial sums of `χ₄` over the odd primes are neither bounded nor linear |
| `RokickiConstantPNT/CharacterSums.lean` | second proof that the partial sums of `χ₄` over the odd primes are not linear, by the prime number theorem in arithmetic progressions |
| `RokickiConstantPNT/MainTheorem.lean` | `RokickiConstant.PNT.rho_irrational`, the second proof of the main theorem |
| `Comparator/Challenge.lean` | the comparator as a challenge: `rho` defined directly from the specification and `theorem rho_irrational : Irrational rho := by sorry` |
| `Comparator/Solution.lean` | the same file with the proof filled in, by identifying `rho` with `Real.rokickiConstant` |
| `blueprint/` | the Verso blueprint: introduction, chapters, dependency graph |
| `scripts/rho.py` | numerical reference computation of `ρ` |

## Comparator

`Comparator/Challenge.lean` states the problem in the most direct terms, with no reference to the
development: `rho` as the specified series over `Nat.nth Nat.Prime`, and `Irrational rho` left as
`sorry`. `Comparator/Solution.lean` is the same file with the proof filled in. The two files differ
only in imports, docstring prose and the proof body, so `diff` on them is the audit.

## Status

Complete: `lake build` (the development and the comparator solution) succeeds with no `sorry` and
no warnings, and `#print axioms rho_irrational` reports only `propext`, `Classical.choice` and `Quot.sound`. `lake build ComparatorChallenge`
elaborates the challenge alone and reports its one intentional `sorry`.

The second proof is the library `RokickiConstantPNT`, which is not a default target:
`lake build RokickiConstantPNT` builds it, together with the part of PrimeNumberTheoremAnd it
imports (compiled from source, a few minutes). It has no `sorry`, and
`#print axioms RokickiConstant.PNT.rho_irrational` reports only `propext`, `Classical.choice` and
`Quot.sound`. The build prints two `sorry` warnings from `PrimeNumberTheoremAnd/Wiener.lean`; they
belong to two lemmas of that file (`prelim_decay_2`, `prelim_decay_3`) that `WeakPNT_AP` does not
use, as the axiom check confirms. PrimeNumberTheoremAnd is pinned in `lakefile.toml` to its
`v4.34.0` tag.

## Blueprint

The project has a [Verso blueprint](blueprint/README.md): an introduction, one chapter per file of
the development, a chapter for the second proof, and a dependency graph whose nodes are linked to the Lean declarations and
coloured by their formalization status. Build and serve it locally with

```bash
lake exe vbp build --serve
```

and open <http://localhost:8000>. The first build compiles Verso, which takes a few minutes.

## Building

Requires [elan](https://github.com/leanprover/elan). Then

```bash
lake exe cache get && lake build
```
