#!/usr/bin/env bash
# Run the official Comparator at a revision compatible with the pinned Lean.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/compare.py "$@"
