#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake env bash -euo pipefail -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for mod in DeltaNordhaus DeltaClasses DeltaConjecture4; do
    lean --root="$PWD" -o "$1/$mod.olean" -j1 -DwarningAsError=true "$mod.lean"
  done
' bash "$tmp"
