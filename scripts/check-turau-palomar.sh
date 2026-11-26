#!/usr/bin/env bash
# Lightweight local checks before the independent-kernel Comparator run.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
python3 - <<'PY'
import json, re
from pathlib import Path
d = Path("Palomar/Turau")
statement = (d/"Challenge.lean").read_text()
solution = (d/"Solution.lean").read_text()
config = json.loads((d/"comparator.json").read_text())
assert len(statement.encode()) <= 32768 and len(statement.splitlines()) <= 300
assert re.findall(r"^(?:public )?import (.+)$", statement, re.M) == ["Lean"]
assert set(config) == {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
assert config["challenge_module"] == "Palomar.Turau.Challenge"
assert config["solution_module"] == "Palomar.Turau.Solution"
names = ["ConjectureLab.TurauSubmission." + n for n in
         ("conjecture_false", "concrete_counterexample", "infinite_family")]
assert config["theorem_names"] == names
assert config["permitted_axioms"] == ["propext", "Classical.choice", "Quot.sound"]
assert len(re.findall(r":= by sorry$", statement, re.M)) == len(names)
assert not re.search(r"\b(sorry|admit|native_decide)\b", solution)
assert (d/"formalization.yaml").is_file()
print(f"Statement surface: {len(statement.splitlines())} lines, {len(statement.encode())} bytes, core-only imports.")
PY
lake build --wfail TurauSolution
# Challenge's three admissions are deliberate and only check statements.
lake build TurauChallenge
lake env lean -DwarningAsError=true --run scripts/check-turau-statement.lean
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lake env lean -DwarningAsError=true Palomar/Turau/Solution.lean | tee "$report"
python3 - "$report" <<'PY'
import json, re, sys
from pathlib import Path
report = Path(sys.argv[1]).read_text()
config = json.loads(Path("Palomar/Turau/comparator.json").read_text())
for name in config["theorem_names"]:
    found = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", report)
    if not found:
        assert f"'{name}' does not depend on any axioms" in report, name
        continue
    used = set(found[1].replace("\n", "").replace(" ", "").split(",")) - {""}
    assert used <= set(config["permitted_axioms"]), (name, used)
print("All 3 Solution proof axiom sets are permitted.")
PY
