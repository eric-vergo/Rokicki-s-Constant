#!/usr/bin/env bash
# Build the project and its Verso blueprint site for GitHub Pages
# (used by .github/workflows/blueprint.yml). Run from the repository root; the site is
# written to _out/site/html-multi/. Any failed step fails the script.

set -euo pipefail

# The development and the comparator solution (the default targets), the challenge on its own,
# and the second proof.
lake build
lake build ComparatorChallenge RokickiConstantPNT

# The site.
lake exe vbp build

# The consistency check of the generated site prints a JSON report with "ok": true or false.
report=$(lake exe vbp check | tail -n 1)
echo "$report"
case "$report" in
  *'"ok":true'*) ;;
  *) echo "vbp check reported problems" >&2; exit 1 ;;
esac

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
