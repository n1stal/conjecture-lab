#!/usr/bin/env bash
# A local declaration-dump comparison; not a substitute for official Comparator.
set -euo pipefail
cd "$(dirname "$0")"
lake build Erdos617PairStarChallenge Erdos617PairStarSolution >&2
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
for side in Challenge Solution; do
  cat >"$tmp/PrintCandidate.lean" <<LEAN
import Palomar.Erdos617PairStar.$side
set_option pp.universes true
set_option pp.fullNames true
#check ParallelMantel.Pentagon.NormalizedPair.high_parallel_multiplicity_bound
#check ParallelMantel.Pentagon.NormalizedStar.refined_star_impossible
#check ParallelMantel.Pentagon.NormalizedStar.unit_margin_star_impossible
#print ParallelMantel.mantelBound
#print ParallelMantel.Pentagon.pairSlots
#print ParallelMantel.Pentagon.NormalizedPair.residual
#print ParallelMantel.Pentagon.NormalizedPair.exteriorBudget
#print Erdos617Geometry.Compatible
#print Erdos617Geometry.Private
#print Erdos617Geometry.Double
#print Erdos617Geometry.orderedColors
#print Erdos617Geometry.Balanced
#print ParallelMantel.Pentagon.NormalizedPair
#print ParallelMantel.Pentagon.NormalizedStar
LEAN
  lake env lean "$tmp/PrintCandidate.lean" >"$tmp/$side.types"
done
diff -u "$tmp/Challenge.types" "$tmp/Solution.types"
cat "$tmp/Solution.types"
