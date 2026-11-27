"""Fail closed on missing result/audit metadata or unapproved theorem axioms."""
import argparse
import json
import math
import re
import subprocess
import tempfile
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
REPO_URL = "https://github.com/n1stal/conjecture-lab"
PALOMAR_ENTRY_URL = "https://palomar-registry.org/entry?id={id}&version={version}"
APPROVED = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)+", re.ASCII)
SLUG = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
PALOMAR_ID = re.compile(r"PALOMAR-\d{4}-\d{2}-\d{2}-\d{6}")
SHA40 = re.compile(r"[0-9a-f]{40}")
BEGIN = "<!-- BEGIN GENERATED RESULTS -->"
END = "<!-- END GENERATED RESULTS -->"
LINK = re.compile(r"(?<!!)\[[^\]\n]+\]\(([^)\s]+)\)")
BADGES = {
    "full": "✅",
    "partial-ca": "🟢",
    "partial": "🟡",
    "none": "⬜",
}
LEAN_LABELS = {
    "full": "Complete",
    "partial-ca": "Partial (computer-assisted)",
    "partial": "Partial",
    "none": "Not formalized",
}


def landing_path(row):
    return row.get("landing", row["priority_audit"])


def result_dir_link(row):
    if row["disposition"] == "known-baseline":
        return landing_path(row)
    return f"results/{row['id']}/"


def palomar_url(entry):
    return PALOMAR_ENTRY_URL.format(id=entry["id"], version=entry["version"])


def registry():
    rows = json.loads((ROOT / "results/registry.json").read_text())
    ids, main_names, all_names = set(), set(), set()
    for row in rows:
        ident = row["id"]
        assert SLUG.fullmatch(ident) and ident not in ids, ident
        ids.add(ident)
        assert row["title"].strip() and row["scope"].strip(), ident
        assert isinstance(row["problem"], str) and row["problem"].strip(), ident
        section = row["section"]
        assert section in {"results", "partial", "baseline"}, ident
        rank = row["rank"]
        assert type(rank) is int and rank > 0, ident
        lean_status = row["lean_status"]
        assert lean_status in BADGES, ident
        vscope = row["verification_scope"]
        assert vscope in {"main", "palomar-pinned"}, ident
        decls = row["declarations"]
        assert decls and len(decls) == len(set(decls)), ident
        for d in decls:
            assert NAME.fullmatch(d) and d not in all_names, d
            all_names.add(d)
            if vscope == "main":
                main_names.add(d)
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
        assert (section == "baseline") == baseline, ident
        palomar_list = row.get("palomar", [])
        assert isinstance(palomar_list, list), ident
        for p in palomar_list:
            assert PALOMAR_ID.fullmatch(p["id"]), p
            assert type(p["version"]) is int and p["version"] >= 1, p
            assert SHA40.fullmatch(p["commit"]), p
        if vscope == "palomar-pinned":
            assert SHA40.fullmatch(row["source_commit"]), ident
            assert isinstance(row["project_path"], str) and row["project_path"].strip(), ident
            assert palomar_list, f"{ident}: palomar-pinned entry must list its Palomar registration"
        if not baseline:
            assert landing == f"results/{ident}/README.md", f"{ident}: missing result README"
            page = re.sub(r"<!--.*?(?:-->|\Z)", " ", (ROOT / landing).read_text(), flags=re.S)
            links = LINK.findall(page)
            proof = row["proof"]
            assert Path(proof).name == proof and proof.endswith(".md") and proof not in {"README.md", "audit.md"}, ident
            assert (ROOT / f"results/{ident}/{proof}").is_file(), f"{ident}: missing {proof}"
            assert proof in links, f"{ident}: link the written proof {proof}"
            assert {"audit.md", "../../docs/verification.md"}.issubset(links), f"{ident}: link audit and verification"
            if vscope == "main":
                assert any(Path(link).suffix == ".lean" and not urlsplit(link).scheme for link in links), (
                    f"{ident}: link Lean source"
                )
            else:
                assert any(row["source_commit"] in link and link.endswith(".lean") for link in links), (
                    f"{ident}: link pinned Lean source at {row['source_commit']}"
                )
            for p in palomar_list:
                assert palomar_url(p) in links, f"{ident}: link Palomar entry {p['id']}"
            assert all(re.search(rf"(?<![\w.]){re.escape(d)}(?!\w)", page) for d in decls), (
                f"{ident}: name the registered declarations"
            )
        summary = row.get("summary", "")
        assert isinstance(summary, str) and summary.strip() and "\n" not in summary, ident
        assert row["sources"] and all(url.startswith("https://") for url in row["sources"]), ident
        audit_text = (ROOT / audit).read_text()
        assert all(url in audit_text for url in row["sources"]), audit
        citations = row.get("citations", [])
        assert isinstance(citations, list) and citations and all(isinstance(c, str) and c.strip() for c in citations), ident
    paths = {p.name for p in (ROOT / "results").iterdir() if p.is_dir()}
    assert paths == ids, f"Public result directories must match registry: {paths ^ ids}"
    return rows, sorted(main_names), sorted(all_names)


def section_rows(rows, section):
    return sorted(
        (r for r in rows if r["section"] == section),
        key=lambda r: (r["rank"], r["id"]),
    )


def table_cell(text):
    return " ".join(text.splitlines()).replace("|", r"\|")


def parse_uncatalogued_palomar(rows):
    reg_file = ROOT / "docs/palomar-registrations.md"
    if not reg_file.is_file():
        return []
    known = {p["id"] for row in rows for p in row.get("palomar", [])}
    uncatalogued = []
    row_re = re.compile(r"^\|\s*(\d{4}-\d{2}-\d{2})\s*\|\s*\[(.+?)\]\((https://palomar-registry\.org/entry\?id=(PALOMAR-\d{4}-\d{2}-\d{2}-\d{6})&version=\d+)\)\s*\|$")
    for line in reg_file.read_text().splitlines():
        m = row_re.match(line.strip())
        if m and m.group(4) not in known:
            uncatalogued.append((m.group(1), m.group(2), m.group(3), m.group(4)))
    return uncatalogued


def format_ranked_cell(row):
    star = " ★" if row.get("palomar") else ""
    label = table_cell(row["problem"]) + star
    return f"**{row['rank']}.** [{label}]({result_dir_link(row)})", BADGES[row["lean_status"]]


def result_block(rows):
    solved = section_rows(rows, "results")
    partial = section_rows(rows, "partial")

    lines = [
        BEGIN,
        "",
        "## Results",
        "",
        "| Problem | Lean verification status | Problem | Lean verification status |",
        "| :--- | :---: | :--- | :---: |",
    ]

    half = math.ceil(len(solved) / 2)
    left = solved[:half]
    right = solved[half:]
    for idx in range(half):
        l_prob, l_badge = format_ranked_cell(left[idx])
        if idx < len(right):
            r_prob, r_badge = format_ranked_cell(right[idx])
        else:
            r_prob, r_badge = "", ""
        lines.append(f"| {l_prob} | {l_badge} | {r_prob} | {r_badge} |")

    lines.extend([
        "",
        "Read down the left pair of columns, then down the right pair. Numbers are approximate editorial importance ranks based on mathematical significance, breadth, and consequences, not recency or Lean status. Equal numbers indicate no clear distinction in importance; tied ranks use competition ranking (1, 2, 2, 4).",
        "",
        "- ✅ Fully Lean-verified.",
        "- 🟢 Partially Lean-verified, with a computer-assisted proof.",
        "- 🟡 Partially Lean-verified.",
        "- ⬜ No Lean verification.",
        "- ★ Registered in [Palomar](docs/palomar-registrations.md): exact statement, pinned source commit, and independent multi-kernel verification report recorded publicly. This is separate from journal peer review.",
        "",
        "For Van Cott–Zhang’s coin-system conjectures, the prefix pattern is realized at every length $n \\ge 11$, refuting the general $3r+1$ ban in part (1) for $r \\ge 4$ and the two-family classification in part (3) at lengths $14, 17, 20, \\dots$; a separate Palomar-registered proof establishes the ban at length $7$. Length $10$ and part (2) at length $9$ remain open. [Proofs and scope](results/van-cott-zhang-521/)",
        "",
        "Turau’s conjecture, Problem 21, and the Van Cott–Zhang family proof (together with the inverse Z partial theorems and the Property P baseline) compile in the default `main` Lean build. Chen’s Conjecture 4, Berend–Ernst–Kontorovich–Kumar’s Conjecture 5.11, Cazenave’s Conjecture 2, the length-7 Van Cott–Zhang theorem, and the four-terminal distance-packing theorem are verified in standalone Lean 4 packages at their pinned commits and registered in Palomar. See [Lean status](docs/lean-status.md) for declarations, commits, and replay details.",
    ])

    if partial:
        lines.extend([
            "",
            "## Partial results on open problems",
            "",
            "This section is ordered by the significance of the partial contributions.",
            "",
        ])
        for row in partial:
            star = " ★" if row.get("palomar") else ""
            lines.append(
                f"- [{row['problem']}{star}]({result_dir_link(row)}). {row['summary']} "
                f"[Lean status](docs/lean-status.md#{row['id']})"
            )

    uncatalogued = parse_uncatalogued_palomar(rows)
    if uncatalogued:
        lines.extend([
            "",
            "## Newly registered in Palomar (pending catalogue entry)",
            "",
        ])
        for day, title, url, ident in uncatalogued:
            lines.append(f"- {day} · [{title}]({url}) (`{ident}`)")

    return "\n".join([*lines, "", END])


def render_front_page(text, rows):
    assert text.count(BEGIN) == text.count(END) == 1, "Missing or duplicate README result marker"
    before, rest = text.split(BEGIN)
    assert END in rest, "README result markers out of order"
    _, after = rest.split(END)
    return before + result_block(rows) + after


def evidence_links(row, prefix=""):
    links = []
    if row.get("proof"):
        links.append(f"[Proof]({prefix}results/{row['id']}/{row['proof']})")
    links.append(f"[Audit]({prefix}{row['priority_audit']})")
    links.append(f"[Lean status]({prefix}docs/lean-status.md#{row['id']})")
    for idx, p in enumerate(row.get("palomar", []), start=1):
        label = "Palomar" if len(row["palomar"]) == 1 else f"Palomar #{idx}"
        links.append(f"[{label}]({palomar_url(p)})")
    return " · ".join(links)


def lean_cell(row):
    badge = BADGES[row["lean_status"]]
    label = LEAN_LABELS[row["lean_status"]]
    where = "`main`" if row["verification_scope"] == "main" else "pinned commit"
    return f"{badge} {label} ({where})"


def render_contents(rows):
    solved = section_rows(rows, "results")
    partial = section_rows(rows, "partial")
    baselines = section_rows(rows, "baseline")

    lines = [
        "# Conjecture Lab: catalogue of results",
        "",
        "[Home](README.md) · [Verification](docs/verification.md) · [Lean status](docs/lean-status.md) · [Palomar registrations](docs/palomar-registrations.md)",
        "",
        "Each entry links to the mathematical argument, prior-work audit, and Lean verification record. Claims retain the exact scope stated in their proof notes and audits; all results are externally unrefereed.",
        "",
        "## Solved conjectures and answered problems",
        "",
        "| Result | Finding | Lean | Evidence |",
        "| :--- | :--- | :---: | :--- |",
    ]
    for row in solved:
        star = " ★" if row.get("palomar") else ""
        lines.append(
            f"| [{table_cell(row['problem'])}{star}]({result_dir_link(row)}) | "
            f"{table_cell(row['summary'])} | {lean_cell(row)} | {evidence_links(row)} |"
        )

    lines.extend([
        "",
        "## Partial results on open problems",
        "",
        "| Result | Finding | Lean | Evidence |",
        "| :--- | :--- | :---: | :--- |",
    ])
    for row in partial:
        star = " ★" if row.get("palomar") else ""
        lines.append(
            f"| [{table_cell(row['problem'])}{star}]({result_dir_link(row)}) | "
            f"{table_cell(row['summary'])} | {lean_cell(row)} | {evidence_links(row)} |"
        )

    if baselines:
        lines.extend([
            "",
            "## Checked baselines",
            "",
            "| Result | Finding | Lean | Evidence |",
            "| :--- | :--- | :---: | :--- |",
        ])
        for row in baselines:
            lines.append(
                f"| [{table_cell(row['title'])}]({result_dir_link(row)}) | "
                f"{table_cell(row['summary'])} | {lean_cell(row)} | {evidence_links(row)} |"
            )

    lines.extend([
        "",
        "## Precise scope",
        "",
    ])
    for row in solved + partial + baselines:
        lines.append(f"- **[{row['title']}]({result_dir_link(row)}).** {row['scope']}")

    lines.extend([
        "",
        "## Primary sources",
        "",
    ])
    seen_citations = set()
    for row in solved + partial + baselines:
        for cite in row["citations"]:
            if cite not in seen_citations:
                seen_citations.add(cite)
                lines.append(f"- {cite}")

    return "\n".join(lines) + "\n"


def render_lean_status(rows):
    solved = section_rows(rows, "results")
    partial = section_rows(rows, "partial")
    baselines = section_rows(rows, "baseline")
    ordered = solved + partial + baselines
    toolchain = (ROOT / "lean-toolchain").read_text().strip()

    lines = [
        "# Lean verification status",
        "",
        "[Home](../README.md) · [Full catalogue](../CONTENTS.md) · [Verification](verification.md) · [Palomar registrations](palomar-registrations.md)",
        "",
        f"Pinned repository toolchain: `{toolchain}`. Approved axioms across all verified declarations: `propext`, `Classical.choice`, `Quot.sound` (zero `sorry`s).",
        "",
        "| Result | Section | Lean status | Build scope | Palomar |",
        "| :--- | :--- | :---: | :--- | :--- |",
    ]
    section_names = {"results": "Solved", "partial": "Partial", "baseline": "Baseline"}
    for row in ordered:
        badge = BADGES[row["lean_status"]]
        scope_label = "`main` default build" if row["verification_scope"] == "main" else f"pinned `{row['source_commit'][:7]}`"
        palomar_cell = ", ".join(
            f"[{p['id']}]({palomar_url(p)})" for p in row.get("palomar", [])
        ) or "—"
        lines.append(
            f"| [{table_cell(row['problem'])}](#{row['id']}) | {section_names[row['section']]} | "
            f"{badge} | {scope_label} | {palomar_cell} |"
        )

    for row in ordered:
        if landing_path(row) == row["priority_audit"]:
            page_line = f"- **Audit:** [{row['problem']}](../{row['priority_audit']})"
        else:
            page_line = f"- **Result page:** [{row['problem']}](../{result_dir_link(row)}) · [Audit](../{row['priority_audit']})"
        lines.extend([
            "",
            f'<a id="{row["id"]}"></a>',
            "",
            f"## {row['title']}",
            "",
            page_line,
            f"- **Lean status:** {BADGES[row['lean_status']]} {LEAN_LABELS[row['lean_status']]}",
        ])
        if row["verification_scope"] == "main":
            lines.append("- **Build scope:** Compiled by `lake build --wfail` and axiom-checked by `python3 scripts/check_publication.py` on `main`.")
        else:
            commit = row["source_commit"]
            path = row["project_path"]
            lines.append(
                f"- **Build scope:** Standalone Lean 4 package at pinned commit "
                f"[`{commit[:7]}`]({REPO_URL}/tree/{commit}/{path}) (`{path}`)."
            )
        decls = ", ".join(f"`{d}`" for d in row["declarations"])
        lines.append(f"- **Checked declarations:** {decls}")
        if row.get("palomar"):
            reg_bits = []
            for p in row["palomar"]:
                extra = f" — {p['note']}" if p.get("note") else ""
                reg_bits.append(f"[{p['id']}]({palomar_url(p)}) (commit `{p['commit'][:7]}`){extra}")
            lines.append("- **Palomar registration:** " + "; ".join(reg_bits))
        lines.append(f"- **Scope:** {row['scope']}")

    return "\n".join(lines) + "\n"


def render_results_index(rows):
    solved = section_rows(rows, "results")
    partial = section_rows(rows, "partial")
    baselines = section_rows(rows, "baseline")
    lines = [
        "# Results directory index",
        "",
        "See the [full catalogue](../CONTENTS.md) for primary sources and scope notes, and [Lean status](../docs/lean-status.md) for formal declarations and replay details.",
        "",
        "| Result | Kind | Lean | Verification scope |",
        "| :--- | :--- | :---: | :--- |",
    ]
    for row in solved + partial + baselines:
        page = landing_path(row).removeprefix("results/")
        star = " ★" if row.get("palomar") else ""
        scope_label = "`main` build" if row["verification_scope"] == "main" else f"pinned `{row['source_commit'][:7]}`"
        lines.append(
            f"| [{table_cell(row['title'])}{star}]({page}) | {row['kind']} | "
            f"{BADGES[row['lean_status']]} | {scope_label} |"
        )
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
    rows, main_names, all_names = registry()

    outputs = [
        (ROOT / "results/README.md", render_results_index(rows)),
        (ROOT / "CONTENTS.md", render_contents(rows)),
        (ROOT / "docs/lean-status.md", render_lean_status(rows)),
    ]
    front_page = ROOT / "README.md"
    outputs.append((front_page, render_front_page(front_page.read_text(), rows)))

    for path, content in outputs:
        if args.write_catalogue:
            path.write_text(content)
        assert path.read_text() == content, f"Regenerate {path.relative_to(ROOT)} from results/registry.json"

    documents = {
        front_page,
        ROOT / "results/README.md",
        ROOT / "CONTENTS.md",
        ROOT / "docs/lean-status.md",
        ROOT / "docs/research-process.md",
        ROOT / "docs/verification.md",
    }
    documents.update(ROOT / landing_path(r) for r in rows)
    documents.update(ROOT / r["priority_audit"] for r in rows)
    check_local_markdown_links(documents)

    if not args.metadata_only:
        with tempfile.TemporaryDirectory() as tmp:
            check = Path(tmp) / "PublicationAudit.lean"
            check.write_text("import Proofs\n" + "".join(
                f"#check {n}\n#print axioms {n}\n" for n in main_names))
            proc = subprocess.run(["lake", "env", "lean", str(check)], cwd=ROOT,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  text=True)
            print(proc.stdout, end="")
            proc.check_returncode()
            check_axioms(proc.stdout, main_names)
    print(
        f"Publication gate: {len(rows)} entries, "
        f"{len(main_names)} main Lean declarations, "
        f"{len(all_names)} total registered declarations"
    )


if __name__ == "__main__":
    main()
