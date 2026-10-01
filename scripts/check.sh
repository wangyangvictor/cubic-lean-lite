#!/bin/sh
set -eu
repo_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
if ! command -v lake >/dev/null 2>&1; then
  printf '%s
' 'Lake is not on PATH. Install Lean through elan: https://lean-lang.org/install/' >&2
  exit 1
fi
cd "$repo_dir/formalization/CubicTenVariables"
lake build CubicTenVariables HessianTheorem11 TranslatedDepthSeven
lake env lean PublicationAudit.lean
