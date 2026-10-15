#!/usr/bin/env bash
# Allocate extra swap only on disposable GitHub-hosted Linux runners.
set -euo pipefail
[[ "${GITHUB_ACTIONS:-}" == true && "${RUNNER_ENVIRONMENT:-}" == github-hosted ]]
[[ "$(uname -s)" == Linux ]]
sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc /usr/local/.ghcup /opt/hostedtoolcache/CodeQL
# Keep at least 50 GiB available for dependencies, objects, tools and the archive.
free_gib=$(df -Pk "$RUNNER_TEMP" | awk 'NR == 2 { print int($4 / 1024 / 1024) }')
swap_gib=$((free_gib - 50))
if (( swap_gib > 32 )); then swap_gib=32; fi
if (( swap_gib > 0 )); then
  sudo fallocate -l "${swap_gib}G" "$RUNNER_TEMP/lean-swap"
  sudo chmod 600 "$RUNNER_TEMP/lean-swap"
  sudo mkswap "$RUNNER_TEMP/lean-swap"
  sudo swapon "$RUNNER_TEMP/lean-swap"
fi
sudo apt-get update -qq
sudo apt-get install -y --no-install-recommends zstd time
free -h
df -h "$RUNNER_TEMP"
