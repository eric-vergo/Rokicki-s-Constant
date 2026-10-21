#!/usr/bin/env bash
# Build the Verso blueprint site for GitHub Pages (used by .github/workflows/blueprint.yml).

set -euo pipefail

lake exe vbp build

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
