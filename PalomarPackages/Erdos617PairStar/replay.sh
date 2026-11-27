#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean="${LEAN_BIN:-lean}"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
prefix=Palomar/Erdos617PairStar
mkdir -p "$scratch/challenge/$prefix" "$scratch/solution/$prefix/Support"
"$lean" --version
printf 'Isolated Challenge: precisely three intentional theorem placeholders expected.\n'
env LEAN_PATH="$scratch/challenge" "$lean" -j1 \
  -o "$scratch/challenge/$prefix/Challenge.olean" "$prefix/Challenge.lean" 2>&1 |
  tee "$scratch/challenge.log"
test "$(grep -c 'declaration uses `sorry`' "$scratch/challenge.log")" -eq 3
printf 'Isolated Solution: warnings as errors; Challenge unavailable.\n'
for name in AnchorGeometry ColoredCaps FromColoring ParallelMantel ShortestOdd \
  PentagonTypes PentagonLedger AnchorTransfer OddExistence ParallelBoundary EvenBoundary \
  PairColoring NonbipartiteMantel CanonicalPair GlobalPalette; do
  env LEAN_PATH="$scratch/solution" "$lean" -j1 -DwarningAsError=true \
    -o "$scratch/solution/$prefix/Support/$name.olean" "$prefix/Support/$name.lean"
done
env LEAN_PATH="$scratch/solution" "$lean" -j1 -DwarningAsError=true \
  -o "$scratch/solution/$prefix/Solution.olean" "$prefix/Solution.lean"
printf 'Strict isolated replay complete.\n'
