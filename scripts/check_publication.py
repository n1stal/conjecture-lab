"""Fail closed on missing result/audit metadata or unapproved theorem axioms."""
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
APPROVED = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)+", re.ASCII)
SLUG = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")


def registry():
    rows = json.loads((ROOT / "results/registry.json").read_text())
    ids, names = set(), set()
    for row in rows:
        ident = row["id"]
        assert SLUG.fullmatch(ident) and ident not in ids, ident
        ids.add(ident)
        assert row["title"].strip() and row["scope"].strip(), ident
        decls = row["declarations"]
        assert decls and len(decls) == len(set(decls)), ident
        for d in decls:
            assert NAME.fullmatch(d) and d not in names, d
            names.add(d)
        audit = f"results/{ident}/audit.md"
        assert row["priority_audit"] == audit and (ROOT / audit).is_file(), audit
        assert row["disposition"] in {
            "known-baseline", "credited-prior-work", "no-prior-found"
        }, ident
        assert row["sources"] and all(url.startswith("https://") for url in row["sources"]), ident
        audit_text = (ROOT / audit).read_text()
        assert all(url in audit_text for url in row["sources"]), audit
    paths = {p.name for p in (ROOT / "results").iterdir() if p.is_dir()}
    assert paths == ids, f"Public result directories must match registry: {paths ^ ids}"
    return rows, sorted(names)


def catalogue(rows):
    lines = ["# Lean-checked results", "",
             "Generated from the publication registry. Each entry links its exact scope and prior-work audit.", ""]
    for r in rows:
        lines.extend((f"- [{r['title']}]({r['id']}/audit.md): {r['scope']}",))
    return "\n".join(lines) + "\n"


def check_axioms(output, names):
    for name in names:
        head = rf"^'{re.escape(name)}' "
        if re.search(head + r"does not depend on any axioms\s*$", output, re.M):
            continue
        receipt = re.search(head + r"depends on axioms: \[([^\]]*)\]\s*$", output, re.M)
        assert receipt, f"No Lean axiom receipt for {name}"
        unknown = {x.strip() for x in receipt[1].split(",")} - APPROVED - {""}
        assert not unknown, f"{name} has unapproved axioms: {sorted(unknown)}"


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--write-catalogue", action="store_true")
    p.add_argument("--metadata-only", action="store_true")
    args = p.parse_args()
    rows, names = registry()
    index = ROOT / "results/README.md"
    rendered = catalogue(rows)
    if args.write_catalogue:
        index.write_text(rendered)
    assert index.read_text() == rendered, "Regenerate results/README.md from the registry"
    if not args.metadata_only:
        with tempfile.TemporaryDirectory() as tmp:
            check = Path(tmp) / "PublicationAudit.lean"
            check.write_text("import Proofs\n" + "".join(
                f"#check {n}\n#print axioms {n}\n" for n in names))
            proc = subprocess.run(["lake", "env", "lean", str(check)], cwd=ROOT,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  text=True)
            print(proc.stdout, end="")
            proc.check_returncode()
            check_axioms(proc.stdout, names)
    print(f"Publication gate: {len(rows)} entries, {len(names)} Lean declarations")


if __name__ == "__main__":
    main()
