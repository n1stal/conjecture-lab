#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean="${LEAN_BIN:-lean}"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
dir=Palomar/WeightedTerminalPacking
mkdir -p "$out/challenge/$dir" "$out/solution/$dir/Data"
"$lean" --version
printf 'Isolated Challenge: two intentional statement holes expected.\n'
env LEAN_PATH="$out/challenge" "$lean" -j1 -o "$out/challenge/$dir/Challenge.olean" "$dir/Challenge.lean"
export LEAN_PATH="$out/solution"
for f in Core Data/Initial Data/Step{00..14} Solution; do
  printf 'Strict isolated Solution dependency: %s\n' "$f"
  "$lean" -j1 -DwarningAsError=true -o "$out/solution/$dir/$f.olean" "$dir/$f.lean"
done
printf 'Strict isolated replay complete.\n'
