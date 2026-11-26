#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
mapfile -t modules < <(sed -nE 's/^(public )?import (Mathlib\.[A-Za-z0-9_.]+)$/\2/p' \
  Challenge.lean InverseZProofs/*.lean | sort -u)
(("${#modules[@]}" > 0))
lake exe cache get "${modules[@]}"
