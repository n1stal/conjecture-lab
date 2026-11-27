"""Fail closed on missing result/audit metadata or unapproved theorem axioms."""
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
APPROVED = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)+", re.ASCII)
SLUG = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
BEGIN = "<!-- BEGIN GENERATED RESULTS -->"
END = "<!-- END GENERATED RESULTS -->"
LINK = re.compile(r"(?<!!)\[[^\]\n]+\]\(([^)\s]+)\)")


def registry():
    rows = json.loads((ROOT / "results/registry.json").read_text())
    ids, names, featured = set(), set(), set()
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
        landing = landing_path(row)
        assert landing in {audit, f"results/{ident}/README.md"}, landing
        assert (ROOT / landing).is_file(), landing
        kind = row["kind"]
        assert kind in {"Counterexample", "Answer to a problem", "Partial theorem", "Theorem", "Known baseline"}, ident
        baseline = row["disposition"] == "known-baseline"
        assert (kind == "Known baseline") == baseline, ident
        if not baseline:
            assert landing == f"results/{ident}/README.md", f"{ident}: missing result README"
            page = re.sub(r"<!--.*?(?:-->|\Z)", " ", (ROOT / landing).read_text(), flags=re.S)
            links = LINK.findall(page)
            proof = row["proof"]
            assert Path(proof).name == proof and proof.endswith(".md") and proof not in {"README.md", "audit.md"}, ident
            assert proof in links, f"{ident}: link the written proof {proof}"
            assert {"audit.md", "../../docs/verification.md"}.issubset(links), f"{ident}: link audit and verification"
            assert any(Path(link).suffix == ".lean" and not urlsplit(link).scheme for link in links), f"{ident}: link Lean source"
            assert all(re.search(rf"(?<![\w.]){re.escape(d)}(?!\w)", page) for d in decls), f"{ident}: name the registered declarations"
        summary = row.get("summary", "")
        assert isinstance(summary, str) and summary.strip() and "\n" not in summary, ident
        order = row.get("featured")
        if order is not None:
            assert row["disposition"] != "known-baseline", ident
            assert type(order) is int and order > 0 and order not in featured, ident
            featured.add(order)
        assert row["sources"] and all(url.startswith("https://") for url in row["sources"]), ident
        audit_text = (ROOT / audit).read_text()
        assert all(url in audit_text for url in row["sources"]), audit
    paths = {p.name for p in (ROOT / "results").iterdir() if p.is_dir()}
    assert paths == ids, f"Public result directories must match registry: {paths ^ ids}"
    return rows, sorted(names)


def landing_path(row):
    return row.get("landing", row["priority_audit"])


def research_order(rows):
    order = len(rows) + max((r.get("featured", 0) for r in rows), default=0)
    return sorted(
        (r for r in rows if r["disposition"] != "known-baseline"),
        key=lambda r: r.get("featured", order),
    )


def result_line(row, from_root, field):
    path = landing_path(row)
    if not from_root:
        path = path.removeprefix("results/")
    return f"- [{row['title']}]({path}): {row[field]}"


def result_block(rows):
    research = [r for r in research_order(rows) if "featured" in r]
    baselines = [r for r in rows if r["disposition"] == "known-baseline"]
    return "\n".join((
        BEGIN, "", "## Featured results", "",
        *(result_line(r, True, "summary") for r in research),
        "", "## Checked baselines", "",
        *(result_line(r, True, "summary") for r in baselines),
        "", END,
    ))


def render_front_page(text, rows):
    assert text.count(BEGIN) == text.count(END) == 1, "Missing or duplicate README result marker"
    before, rest = text.split(BEGIN)
    assert END in rest, "README result markers out of order"
    _, after = rest.split(END)
    return before + result_block(rows) + after


def catalogue(rows):
    lines = ["# Lean-checked results", "",
             "The default build checks the claims below. [Palomar registrations](../docs/palomar-registrations.md) link to the source commits checked by the external registry.",
             "", "| Result | Kind | What the proof establishes |", "| --- | --- | --- |"]
    baselines = [r for r in rows if r["disposition"] == "known-baseline"]
    for row in research_order(rows) + baselines:
        title = row["title"].replace("|", r"\|")
        scope = " ".join(row["scope"].splitlines()).replace("|", r"\|")
        page = landing_path(row).removeprefix("results/")
        lines.append(f"| [{title}]({page}) | {row['kind']} | {scope} |")
    return "\n".join(lines) + "\n"


def check_local_markdown_links(paths):
    for document in paths:
        for href in LINK.findall(document.read_text()):
            url = urlsplit(href)
            if not url.path or url.scheme or url.netloc:
                continue
            target = (document.parent / unquote(url.path)).resolve()
            assert target.is_relative_to(ROOT) and target.exists(), f"{document.relative_to(ROOT)}: {href}"


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
    front_page = ROOT / "README.md"
    front_text = front_page.read_text()
    updated_front = render_front_page(front_text, rows)
    if args.write_catalogue:
        front_page.write_text(updated_front)
    assert front_page.read_text() == updated_front, "Regenerate README.md from the registry"
    documents = {front_page, index, ROOT / "CONTENTS.md", ROOT / "docs/research-process.md"}
    documents.update(ROOT / landing_path(r) for r in rows)
    documents.update(ROOT / r["priority_audit"] for r in rows)
    check_local_markdown_links(documents)
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
