"""Validate a public, secret-free filing queue and select an immutable preflight."""
import hashlib
import json
import os
from pathlib import Path
import re
import sys

REPO = "n1stal/conjecture-lab"
FIELDS = {"id", "title", "commit", "project_path", "preflight_run", "status"}
STATUSES = {"needs_preflight", "awaiting_intake", "needs_resubmission", "filed", "registered"}


def validate(queue):
    if not isinstance(queue, dict) or set(queue) != {"schema", "repository", "candidates"}:
        raise ValueError("Invalid queue envelope")
    if queue["schema"] != 1 or queue["repository"] != REPO or not isinstance(queue["candidates"], list):
        raise ValueError("Invalid queue schema, repository or candidate list")
    rows = {}
    pins = set()
    for row in queue["candidates"]:
        if not isinstance(row, dict) or set(row) != FIELDS:
            raise ValueError("Invalid candidate fields")
        cid, title, sha, path, run, status = (row[k] for k in
            ("id", "title", "commit", "project_path", "preflight_run", "status"))
        if not isinstance(cid, str) or not re.fullmatch(r"[a-z0-9][a-z0-9-]{1,63}", cid):
            raise ValueError("Invalid candidate ID")
        if not isinstance(title, str) or not 1 <= len(title) <= 160 or not title.isprintable():
            raise ValueError(f"Invalid title: {cid}")
        if not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{40}", sha):
            raise ValueError(f"Expected an immutable commit: {cid}")
        if not isinstance(path, str) or not re.fullmatch(r"PalomarPackages/[A-Za-z0-9][A-Za-z0-9-]{0,63}", path):
            raise ValueError(f"Invalid nested project folder: {cid}")
        if not isinstance(status, str) or status not in STATUSES:
            raise ValueError(f"Invalid state: {cid}")
        if (run is not None and (type(run) is not int or run <= 0)) or (run is None and status != "needs_preflight"):
            raise ValueError(f"Missing or invalid Actions run: {cid}")
        if cid in rows or (sha, path) in pins:
            raise ValueError(f"Duplicate candidate or pin: {cid}")
        rows[cid] = row
        pins.add((sha, path))
    if not rows:
        raise ValueError("Empty queue")
    return rows


def main():
    rows = validate(json.loads(Path("docs/palomar-queue.json").read_text(encoding="utf-8")))
    print(f"Validated {len(rows)} immutable Palomar queue entries.")
    cid = os.environ.get("REQUESTED_CANDIDATE", "")
    if not cid:
        if os.environ.get("GITHUB_EVENT_NAME") == "workflow_dispatch":
            raise ValueError("Choose one known candidate ID")
        return
    if cid not in rows:
        raise ValueError("Unknown candidate ID")
    row = rows[cid]
    path = row["project_path"]
    run = os.environ["GITHUB_RUN_ID"]
    attempt = os.environ["GITHUB_RUN_ATTEMPT"]
    if not run.isascii() or not run.isdecimal() or not attempt.isascii() or not attempt.isdecimal():
        raise ValueError("Invalid Actions run identity")
    request = hashlib.sha256(f"{run}:{attempt}:{cid}".encode()).hexdigest()[:12]
    options = {
        "project_path": path,
        "comparator_config_path": f"{path}/comparator.json",
        "formalization_metadata_path": f"{path}/formalization.yaml",
        "authorization_relationship": "I am a responsible author or maintainer",
    }
    with Path(os.environ["GITHUB_OUTPUT"]).open("a", encoding="utf-8") as out:
        print(f"commit={row['commit']}", file=out)
        print(f"request_id={request}", file=out)
        print("options=" + json.dumps(options, separators=(",", ":")), file=out)
    print(f"Selected {cid} at {row['commit']}.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError) as exc:
        print(f"Palomar queue validation failed: {exc}", file=sys.stderr)
        sys.exit(1)
