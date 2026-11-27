#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean="$(printenv LEAN_BIN || printf lean)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
prefix=Palomar/Erdos617PairBound
mkdir -p "$scratch/challenge/$prefix" "$scratch/solution/$prefix/Support"
"$lean" --version
printf 'Isolated Challenge: one intentional statement hole expected.\n'
env LEAN_PATH="$scratch/challenge" "$lean" -j1 \
  -o "$scratch/challenge/$prefix/Challenge.olean" "$prefix/Challenge.lean"
printf 'Isolated Solution: warnings as errors; Challenge unavailable.\n'
for name in AnchorGeometry ColoredCaps FromColoring ParallelMantel ShortestOdd \
  PentagonTypes PentagonLedger AnchorTransfer OddExistence ParallelBoundary EvenBoundary; do
  env LEAN_PATH="$scratch/solution" "$lean" -j1 -DwarningAsError=true \
    -o "$scratch/solution/$prefix/Support/$name.olean" "$prefix/Support/$name.lean"
done
env LEAN_PATH="$scratch/solution" "$lean" -j1 -DwarningAsError=true \
  -o "$scratch/solution/$prefix/Solution.olean" "$prefix/Solution.lean"
printf 'Strict isolated replay complete.\n'
