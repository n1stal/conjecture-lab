# Palomar filing queue

[Queue data](palomar-queue.json) · [GitHub Actions](https://github.com/n1stal/conjecture-lab/actions/workflows/palomar-queue.yml) · [Palomar submission form](https://submit.palomar-registry.org/)

This is the durable queue for verified research. It records only public GitHub source pins, verification runs and filing status. Do not put credentials, private review links, submission access tokens or unpublished drafts here.

| Candidate | Mechanical preflight | Next filing step |
| --- | --- | --- |
| BEKA Conjecture 5.11 | [Passed](https://github.com/n1stal/conjecture-lab/actions/runs/45991319706) | Awaiting Palomar intake after a rate limit |
| Cazenave Conjecture 2 | [Passed](https://github.com/n1stal/conjecture-lab/actions/runs/45991715671) | Awaiting Palomar intake after a rate limit |
| Strong Arboricity Conjecture 3 | [Passed](https://github.com/n1stal/conjecture-lab/actions/runs/45990004344) | On hold: reframe as a distinct explicit Lean witness and credit [Axenovich et al., Theorem 7](https://arxiv.org/abs/1803.02152) |

The JSON is the operational source of truth. A successful preflight checks an exact commit but does not file anything, start editorial review, or register a result. A separate production run can still fail.

## Run or repeat a preflight

1. Add or update a candidate in the JSON through a pull request. Use the full commit SHA and exact project directory, not a branch or tag. Use `needs_preflight` and a null run ID until the first run completes.
2. Once merged, open **Actions → Palomar filing queue → Run workflow** on `main` and enter the candidate ID. GitHub validates the queue and runs Palomar's pinned full mechanical verification. Ordinary pushes and PRs validate the queue only.
3. Check the report artifact for the expected source commit, project directory, target, successful status and proof checker results. Record the run ID and update the status. See [Palomar's preflight documentation](https://github.com/PalomarRegistry/PalomarSubmission).

## File or register

Use the official Palomar form for the final filing if Palomar requires GitHub confirmation. Copy the repository, full commit, explicitly named **project folder**, and both `comparator.json` and `formalization.yaml` paths within that folder. Do not reuse a private review decision across different commits. Do not retry rapidly when Palomar limits submissions. After actual editorial review, separately confirm its findings and registration; mark a result registered only when its public entry is visible.

No long-lived token and no secrets are needed for GitHub Actions preflights. The workflow does not store Palomar login or attempt to bypass its rate limit.
