#!/usr/bin/env bash
# Explicitly unsandboxed runner for trusted local sources on macOS or Linux.
set -euo pipefail
while (($#)); do
  case "$1" in
    --best-effort|-ldd|-add-exec) shift ;;
    --ro|--rw|--rwx|--rox|--env) shift 2 ;;
    lake|lean4export) exec "$@" ;;
    *) echo "Unsupported Comparator runner argument: $1" >&2; exit 2 ;;
  esac
done
exit 2
