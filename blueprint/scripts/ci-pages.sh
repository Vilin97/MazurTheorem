#!/usr/bin/env bash

set -euo pipefail

BLUEPRINT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$BLUEPRINT_ROOT"

export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
lake exe vbp build
lake exe vbp check

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
