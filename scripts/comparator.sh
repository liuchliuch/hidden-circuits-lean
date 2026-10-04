#!/usr/bin/env bash
# Run the official Comparator at a revision compatible with the pinned Lean.
set -euo pipefail
cd "$(dirname "$0")/.."
[[ $# -le 1 ]] || { echo "Usage: scripts/comparator.sh [--local]" >&2; exit 2; }
mode="${1:-}"
if [[ "$mode" != "" && "$mode" != "--local" ]]; then
  echo "Usage: scripts/comparator.sh [--local]" >&2
  exit 2
fi
if [[ "$mode" == "" ]]; then
  [[ "$(uname -s)" == Linux ]] || { echo "Use --local on macOS; sandbox mode requires Linux." >&2; exit 2; }
  command -v landrun >/dev/null
  command -v systemd-run >/dev/null
fi
revision=e6831abb2f76b7ce6f2fb28e6410a0df878e6e4b
tooldir="$PWD/.lake/tools/comparator"
if [[ ! -d "$tooldir/.git" ]]; then
  mkdir -p "$tooldir"
  git -C "$tooldir" init -q
  git -C "$tooldir" remote add origin https://github.com/leanprover/comparator.git
  git -C "$tooldir" fetch --depth 1 origin "$revision"
  git -C "$tooldir" checkout --detach FETCH_HEAD
fi
[[ "$(git -C "$tooldir" rev-parse HEAD)" == "$revision" ]]
[[ -z "$(git -C "$tooldir" status --porcelain --untracked-files=no)" ]]
cmp lean-toolchain "$tooldir/lean-toolchain"
lake -d "$tooldir" build comparator lean4export
export PATH="$tooldir/.lake/packages/lean4export/.lake/build/bin:$PATH"
if [[ "$mode" == "--local" ]]; then
  echo "Local Comparator: statement comparison, axiom checks, kernel replay; no sandbox." >&2
  mkdir -p .lake/tools/local-bin
  ln -sf "$PWD/scripts/local-runner.sh" .lake/tools/local-bin/landrun
  export PATH="$PWD/.lake/tools/local-bin:$PATH"
  lake env "$tooldir/.lake/build/bin/comparator" comparator.json
else
  systemd-run --user --wait --pipe --collect --property=RestrictAddressFamilies=~AF_UNIX \
    -E "PATH=$PATH" --working-directory="$PWD" \
    lake env "$tooldir/.lake/build/bin/comparator" comparator.json
fi
