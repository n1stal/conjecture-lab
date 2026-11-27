#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
project=$(cd -- "${1:?Pass the absolute path to the pinned conjecture-lab checkout}" && pwd)
cd "$project"
expected=8673a57d26ea1c8d2752635bd2dae5fe8665a171
[[ $(git rev-parse HEAD) = "$expected" ]] || { echo 'Wrong base checkout (see README)' >&2; exit 1; }
lean --version | grep -q '4.35.0-rc2'
lake build --wfail SpectralRank
standard=$(lake env printenv LEAN_PATH)
out=${2:-$(mktemp -d)}
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$standard"
echo "Checking certificates and proof sources into $out"
(cd "$src"; sha256sum -c MANIFEST.sha256)
for m in C20Weighted C20Structure C20Catalogue C20Triangle C20ProfileProbe C20Bench C20Balance C20HubRepEarly C20Scope C20Minimizer C20RankMin C20TriBranch C20Classify C20NumericalCore C20Limit IndependentSourceAudit ManhattanLocal ManhattanSpectral ManhattanGraph ManhattanMoment ManhattanClose ManhattanTarget ManhattanTransport ManhattanFinite ManhattanMass ManhattanPawIsolate ManhattanSign ManhattanResidual ManhattanSmall ManhattanSmallFinal ManhattanLarge ManhattanWinner Conjecture20Nearest Conjecture20Complete; do
  echo "=== $m ==="
  lean -R "$src" -j1 -DwarningAsError=true -o "$out/$m.olean" "$src/$m.lean"
done

