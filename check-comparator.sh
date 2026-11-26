#!/usr/bin/env bash
# Verify using the installed Lean distribution, including its independent kernels.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
prefix="$(lean --print-prefix)"
for tool in leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool" || { echo "Missing toolchain component: $tool" >&2; exit 1; }
done
command -v bwrap >/dev/null
config="$(mktemp)"
trap 'rm -f "$config"' EXIT
python3 - "$config" "$prefix" "${1:-comparator.json}" <<'PY'
import json, sys
from pathlib import Path
local, prefix, source = sys.argv[1:]
data = json.loads(Path(source).read_text())
assert "external_kernels" not in data
data.pop("enable_nanoda", None)
data["external_kernels"] = {
    "nanoda": [str(Path(prefix) / "bin/nanoda_bin")],
    "con-ron": [str(Path(prefix) / "bin/con-ron")],
}
Path(local).write_text(json.dumps(data))
PY
lake comparator --config "$config"
