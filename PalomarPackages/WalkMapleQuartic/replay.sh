#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -v LEAN_BIN ]]; then lean_bin="$LEAN_BIN"; else lean_bin=lean; fi
root="$(mktemp -d)"
trap 'rm -rf "$root"' EXIT
pkg="Palomar/WalkMapleQuartic"
mkdir -p "$root/challenge/$pkg" "$root/solution/$pkg"
"$lean_bin" --version
printf '%s\n' 'Isolated Challenge: one intentional theorem hole.'
LEAN_PATH="$root/challenge" "$lean_bin" -j1 -o "$root/challenge/$pkg/Challenge.olean" "$pkg/Challenge.lean"
printf '%s\n' 'Isolated Solution: warnings are errors.'
LEAN_PATH="$root/solution" "$lean_bin" -j1 -DwarningAsError=true -o "$root/solution/$pkg/Solution.olean" "$pkg/Solution.lean"
printf '%s\n' 'Isolated Lean replay passed.'
