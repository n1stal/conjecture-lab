"""Refresh the public registration and research-branch indexes."""
import json
import re
import subprocess
from datetime import date
from html import escape
from pathlib import Path
from urllib.parse import urlencode

DATA = "https://data.palomar-registry.org/"
ID = re.compile(r"PALOMAR-\d{4}-\d{2}-\d{2}-\d{6}")
REPOS = {"n1stal/conjecture-lab", "rokaswk/conjecture-lab"}
DOCS = Path(__file__).resolve().parents[1] / "docs"
REPOSITORY = "https://github.com/n1stal/conjecture-lab"


def fetch(path):
    return json.loads(subprocess.check_output(
        ["curl", "--fail", "--silent", "--show-error", "--retry", "3",
         "--max-time", "30", DATA + path]
    ))


def search(repository):
    params = {"q": repository}
    cursors = set()
    while True:
        page = fetch("api/v1/results?" + urlencode(params))
        yield from page["entries"]
        cursor = page["next"]
        if cursor is None:
            return
        if not isinstance(cursor, str) or cursor in cursors:
            raise ValueError("Invalid or repeated Palomar cursor")
        cursors.add(cursor)
        params["cursor"] = cursor


def registrations():
    records = {}
    entries = (entry for repo in sorted(REPOS) for entry in search(repo))
    for entry in entries:
        ident, version = entry["id"], entry["version"]
        if not ID.fullmatch(ident) or type(version) is not int or version < 1:
            raise ValueError(f"Invalid Palomar identity: {ident}")
        record = fetch(f"entries/{ident}-v{version}.json")
        if (record["id"], record["version"]) != (ident, version):
            raise ValueError(f"Mismatched Palomar record: {ident}")
        if (record["status"] == "registered"
                and record["source"]["repository"].lower() in REPOS):
            title = " ".join(record["title"].split())
            title = re.sub(r"([\\\[\]|`*_<>])", r"\\\1", title)
            records[ident] = (date.fromisoformat(record["first_registered_on"]), ident, version, title)
    return sorted(records.values(), reverse=True)


def research_branches():
    output = subprocess.check_output(
        ["git", "ls-remote", "--heads", REPOSITORY, "refs/heads/results/*", "refs/heads/palomar/preflight-*",
         "refs/heads/verification/*"],
        text=True,
    )
    lines = ["# Research branches", "",
             "These source snapshots include experiments, preflights and earlier versions of published work.", "",
             "| Branch | Source commit |", "| --- | --- |"]
    for ref in sorted(output.splitlines(), key=lambda row: row.split()[1]):
        sha, name = ref.split()
        branch = name.removeprefix("refs/heads/")
        if not re.fullmatch(r"[0-9a-f]{40}", sha):
            raise ValueError(f"Invalid commit for {branch}")
        label = escape(branch).replace("|", "&#124;")
        lines.append(f"| <code>{label}</code> | [{sha[:7]}]({REPOSITORY}/tree/{sha}) |")
    return "\n".join(lines) + "\n"


def main():
    records = registrations()
    if not records:
        raise ValueError("Palomar returned no matching registrations")
    lines = ["# Palomar registrations", "",
             "Each registration links the exact statement, source commit and verification report.", "",
             "| Registered | Result |", "| --- | --- |"]
    for day, ident, version, title in records:
        lines.append(f"| {day} | [{title}](https://palomar-registry.org/entry?id={ident}&version={version}) |")
    branches = research_branches()
    (DOCS / "research-branches.md").write_text(branches)
    (DOCS / "palomar-registrations.md").write_text("\n".join(lines) + "\n")
    print(f"Found {len(records)} public registrations.")


if __name__ == "__main__":
    main()
