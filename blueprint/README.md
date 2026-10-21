# Blueprint

The blueprint of this project is written with
[Verso Blueprint](https://github.com/leanprover/verso-blueprint), the Verso-based successor of
`leanblueprint`. It is pinned in `lakefile.toml` to commit
`a1cf70667112dcffe15faea9f8783e63dd9644e8` (head of its `v4.34.0` release branch, built for Lean
`v4.34.1`), which in turn pins Verso, SubVerso and verso-slides.

## Layout

| File | Role |
|---|---|
| `BlueprintMain.lean` (repository root) | generator entry point; `lake exe vbp build` finds it there |
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
the previews and the graph load data with `fetch`.) The dependency graph and the progress summary
are pages of the site.

Other useful commands:

```bash
lake build RokickiBlueprint   # elaborate the blueprint only (fast feedback while writing)
lake exe vbp query labels     # list the blueprint nodes
lake exe vbp query work-queue # nodes that are ready to be worked on
lake exe vbp check            # check the consistency of the generated site
lake exe vbp build --pdf      # also build _out/site/pdf/main.pdf (needs lualatex)
```

`_out/` is ignored by git. The graph page draws the graph in the browser with `d3-graphviz`
loaded from `cdn.jsdelivr.net`, so viewing it needs network access (no local Graphviz is needed).

`require mathlib` comes after `require VersoBlueprint` in `lakefile.toml` on purpose: the last
requirement's pins of shared dependencies (ProofWidgets, Plausible) win, which keeps them equal to
Mathlib's and keeps `lake exe cache get` working. Update the blueprint tool with
`lake update VersoBlueprint` after changing its `rev`, and check afterwards that the Mathlib,
ProofWidgets and Plausible entries of `lake-manifest.json` did not change.

## Writing

`blueprint/RokickiBlueprint/RokickiConstant.lean` contains a worked example: a definition and a
theorem, both linked to Lean declarations with `(lean := "...")`, and a dependency `{uses "..."}[]`
between them. The status colours of the graph are computed from the linked Lean declarations
(complete, contains `sorry`, missing); there is no manual `\leanok`. See the
[manual](https://github.com/leanprover/verso-blueprint/blob/v4.34.0/doc/MANUAL.md) for the full
syntax.
