#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean="${LEAN_BIN:-lean}"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
src=Palomar/FourTerminalPacking
mkdir -p "$out/challenge/$src" "$out/solution/$src"
"$lean" --version
printf 'Isolated Challenge: two intentional statement holes expected.\n'
env LEAN_PATH="$out/challenge" "$lean" -j1 \
  -o "$out/challenge/$src/Challenge.olean" "$src/Challenge.lean"
printf 'Isolated Solution: warnings as errors.\n'
env LEAN_PATH="$out/solution" "$lean" -j1 -DwarningAsError=true \
  -o "$out/solution/$src/Solution.olean" "$src/Solution.lean"
printf 'Strict isolated replay complete.\n'
