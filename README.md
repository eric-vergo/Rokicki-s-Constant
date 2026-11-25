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

stated in `Comparator/RhoIrrational/Challenge.lean` and proved in
`Comparator/RhoIrrational/Solution.lean`.

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
by the prime number theorem in arithmetic progressions, `WeakPNT_AP` of the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project. If `Σ_{k<n} χ₄(p_{k+2}) = c·n + O(1)`, summation by parts against the weights
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
| `vendor/PrimeNumberTheoremAnd/` | vendored part of PrimeNumberTheoremAnd proving `WeakPNT_AP`; generated, do not edit |
| `scripts/vendor-pnt.py` | regenerates `vendor/PrimeNumberTheoremAnd/` from the pinned upstream commit |
| `Comparator/RhoIrrational/Challenge.lean` | the comparator as a challenge: `rho` defined directly from the specification and `theorem rho_irrational : Irrational rho := by sorry` |
| `Comparator/RhoIrrational/Solution.lean` | the same file with the proof filled in, by identifying `rho` with `Real.rokickiConstant` |
| `blueprint/` | the Verso blueprint: introduction, chapters, dependency graph |
| `scripts/rho.py` | numerical reference computation of `ρ` |

The files of `RokickiConstant/` and `Comparator/` are Lean
[modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-scopes), as
in Mathlib: `module`, `public import` for what the statements need (`import` for what only the
proofs need), and `@[expose] public section` in the files with definitions, so that their bodies
unfold in downstream proofs. The blueprint chapters are not modules; see `blueprint/README.md`.

## Comparator

`Comparator/RhoIrrational/Challenge.lean` states the problem in the most direct terms, with no
reference to the development: `rho` as the specified series over `Nat.nth Nat.Prime`, and
`Irrational rho` left as `sorry`. `Comparator/RhoIrrational/Solution.lean` is the same file with
the proof filled in. The two files differ only in imports, docstring prose and the proof body, so
`diff` on them is the audit. `Comparator/RhoIrrational/comparator.json` names the judged theorem
`rho_irrational` and the permitted axioms, `propext`, `Quot.sound` and `Classical.choice`, in the
form `lake comparator --config Comparator/RhoIrrational/comparator.json` reads. The second proof
below proves the same statement about the same `rho`; it is a second proof, not a second
challenge.

## Status

Complete: `lake build` (the development and the comparator solution) succeeds with no `sorry` and
no warnings, and `#print axioms rho_irrational` reports only `propext`, `Classical.choice` and `Quot.sound`. `lake build ComparatorChallenge`
elaborates the challenge alone and reports its one intentional `sorry`.

The second proof is the library `RokickiConstantPNT`, which is not a default target:
`lake build RokickiConstantPNT` builds it, together with the vendored part of
PrimeNumberTheoremAnd it imports. The build has no `sorry`, its only warnings are
Lake's notes that the vendored files are not written for the module system, and
`#print axioms RokickiConstant.PNT.rho_irrational` reports only `propext`, `Classical.choice` and
`Quot.sound`.

### Vendored PrimeNumberTheoremAnd

`vendor/PrimeNumberTheoremAnd/` holds the six files of PrimeNumberTheoremAnd (tag `v4.34.0`) that
`WeakPNT_AP` needs. They are generated by `scripts/vendor-pnt.py`, which removes that project's
LeanArchitect annotations (its `blueprint` attribute clashes with Verso Blueprint's), cuts
`Wiener.lean` after `WeakPNT_AP`, drops three unused lemmas that rest on `sorry`, and replaces 16
proof steps that no longer elaborate on Mathlib `v4.36.0` (renamed lemmas, and tactic steps that
run out of heartbeats or meet a changed normal form). No statement is modified, and every other
proof that is kept is the upstream proof. See [`vendor/README.md`](vendor/README.md).

## Blueprint

The blueprint is published at **<https://eric-vergo.github.io/Rokicki-s-Constant/>**.

It is a [Verso blueprint](blueprint/README.md): an introduction, one chapter per file of the
development, a chapter for the second proof, a dependency graph covering both proofs whose nodes
are linked to the Lean declarations and coloured by the status of their Lean code, and a Project
Stats page. Each statement is shown beside the Lean source of its declarations. The site is built
with the fork [eric-vergo/verso-blueprint](https://github.com/eric-vergo/verso-blueprint) at commit
`02159cd8cb5b69babf94817cdeabb93064d6f0e1` (pinned in `lakefile.toml`).

While the site is built, two kernel checkers that ship with Lean, `con-leche` and `con-ron`, replay
the project's compiled modules; the headline and the green marks and counts appear only if both
accepted them, and the Project Stats page reports the replay. Declarations that rest on axioms
beyond the standard three are marked as not checked.

The status marks and counts on the site are about the Lean code only: they say whether the linked
Lean declarations, and what they use, are free of `sorry`, as read from the build the site was
generated from. No tool checks that an informal statement says the same as its Lean statement.

To build and serve it locally, from the repository root:

```bash
lake exe cache get            # Mathlib's prebuilt files
lake build                    # the development and the comparator solution
lake exe vbp build --serve    # the site, served at http://localhost:8000
```

The first site build compiles Verso and Verso Blueprint, which takes several minutes. The site is
written to `_out/site/html-multi/`. GitHub Actions (`.github/workflows/blueprint.yml`) rebuilds and
publishes it on every push to `main`.

## Building

Requires [elan](https://github.com/leanprover/elan). Then

```bash
lake exe cache get && lake build
```
