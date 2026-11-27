#!/bin/bash
set -euo pipefail
cd "$RUNNER_TEMP"
if [[ "$RUNNER_ENVIRONMENT" = github-hosted ]] && (( $(df -Pk "$RUNNER_TEMP" | awk 'NR==2 {print $4}') < 45*1024*1024 )); then
  sudo rm -rf -- /usr/local/lib/android /usr/share/dotnet /opt/ghc /usr/local/.ghcup
fi
curl -fLsS --retry 3 -o pinned.tar.zst https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst
echo '890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235  pinned.tar.zst' | sha256sum -c
tar --zstd -xf pinned.tar.zst
rm pinned.tar.zst
echo "$RUNNER_TEMP/lean-4.33.1-linux/bin" >> "$GITHUB_PATH"
