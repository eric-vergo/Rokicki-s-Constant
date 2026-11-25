# Blueprint

The blueprint of this project is written with
[Verso Blueprint](https://github.com/leanprover/verso-blueprint), the Verso-based successor of
`leanblueprint`, in the version of the fork
[eric-vergo/verso-blueprint](https://github.com/eric-vergo/verso-blueprint) (branch `v4.36.0`,
for Lean `v4.36.0`). The fork adds the side-by-side layout (each statement beside the Lean source
of its declarations, with the prose proof and the Lean proof opened by one toggle), formulas
typeset when the site is built, a Project Stats page and a headline card for the Comparator
challenge, with a page for the challenge. `lakefile.toml` pins it to commit
`cc82fb88974659b6890997a1975d21f7cd4d280c`, together with the fork of Verso at
`94cea086b880f61f5b3847d30151b8e5f80e1259` and the fork of SubVerso at
`27c7e30ea5c25f3bbb7fad1badafd7a3d3eeb19f`; the published site is built with these commits.
The dependency graph is laid out and drawn while the site is built, by the Lean library
[PILean](https://github.com/eric-vergo/PILean) (which the fork requires, at the revision recorded in
`lake-manifest.json`), so the page ships no graph-layout program.

## Layout

| File | Role |
|---|---|
| `BlueprintMain.lean` (repository root) | generator entry point; `lake exe vbp build` finds it there. It turns on the side-by-side layout and adds a link to this repository to the sidebar |
| `blueprint/RokickiBlueprint.lean` | top-level document: title, chapter list, dependency graph, progress summary |
| `blueprint/RokickiBlueprint/*.lean` | one module per chapter |

The blueprint is the Lake library `RokickiBlueprint` (`srcDir = "blueprint"`). It is not a default
target, so `lake build` does not build it.

## Building

From the repository root, after `lake exe cache get` (the first build also compiles Verso and
Verso Blueprint, which takes several minutes):

```bash
lake exe vbp build            # writes the site to _out/site/html-multi/
lake exe vbp build --serve    # same, then serves it at http://localhost:8000 (or the next free port)
```

To view a site that is already built without rebuilding:

```bash
python3 -m http.server --directory _out/site/html-multi 8000
```

then open <http://localhost:8000>. (Opening `index.html` directly from disk does not work well:
the previews and the graph load data with `fetch`.) The dependency graph, the progress summary and
the Project Stats page are pages of the site.

Other useful commands:

```bash
lake build RokickiBlueprint   # elaborate the blueprint only (fast feedback while writing)
lake exe vbp query labels     # list the blueprint nodes
lake exe vbp query work-queue # nodes that are ready to be worked on
lake exe vbp check            # check the consistency of the generated site
lake exe vbp build --pdf      # also build _out/site/pdf/main.pdf (needs lualatex)
```

`_out/` is ignored by git. The site needs no network access when it is viewed: its scripts,
styles and fonts are part of it, and every link inside it is relative, so it also works from a
sub-path such as the GitHub Pages address.

`require mathlib` comes after the blueprint requirements in `lakefile.toml` on purpose: the last
requirement's pins of shared dependencies (ProofWidgets, Plausible) win, which keeps them equal to
Mathlib's and keeps `lake exe cache get` working. `subverso` and `verso` are required before
`VersoBlueprint` so that the workspace uses the forks' commits named above. To move the blueprint
tool to a newer commit, change the `rev` of `VersoBlueprint` (and, if its own `lake-manifest.json`
asks for them, those of `verso` and `subverso`), run `lake update VersoBlueprint verso subverso`,
and check afterwards that the Mathlib, ProofWidgets and Plausible entries of `lake-manifest.json`
did not change.

## Publishing

`.github/workflows/blueprint.yml` builds the project and the site on every push to `main` (and
when started by hand from the Actions tab) and publishes the site with GitHub Pages at
<https://eric-vergo.github.io/Rokicki-s-Constant/>. It runs `scripts/ci-pages.sh`, which builds the
default targets, `ComparatorChallenge` and `RokickiConstantPNT`, checks the layout of the
Comparator challenge (`lake exe vbp comparator-check`), then builds the site, and fails when a
build fails, `lake exe vbp check` reports a problem with the generated site, or the Project Stats
page does not show the judged theorem as proved with both kernel checkers accepting the replay.

## Writing

The chapter files are ordinary (non-`module`) Lean files, unlike the development. A module may only
import modules, and Verso Blueprint (`VersoBlueprint`) is not one yet at this version. Also, a
non-module file sees the proofs of the modules it imports, which lets the blueprint check that
the linked declarations are free of `sorry`. A module importing them normally would only see their
statements.

`blueprint/RokickiBlueprint/RokickiConstant.lean` contains a worked example: a definition and a
theorem, both linked to Lean declarations with `(lean := "...")`, and a dependency `{uses "..."}[]`
between them. The status colours of the graph are computed from the linked Lean declarations
(complete, contains `sorry`, missing); there is no manual `\leanok`. See the
[manual](https://github.com/eric-vergo/verso-blueprint/blob/v4.36.0/doc/MANUAL.md) for the full
syntax.
