#!/usr/bin/env bash
set -euo pipefail
entry=$(cd -- "$(dirname -- "$0")" && pwd -P)
root=$(mktemp -d "${RUNNER_TEMP:-/tmp}/zuo-ordinary.XXXXXXXX")
mode=${ORDINARY_AUDIT_MODE:-build}
jobs=${ORDINARY_AUDIT_JOBS:-1}
logdir=${ORDINARY_AUDIT_LOG_DIR:-"$root/logs"}
mkdir -p -- "$logdir"
printf 'ORDINARY_AUDIT_LOG_DIR=%s\n' "$logdir"
case "$mode" in build|full) ;; *) echo "Expected audit mode build or full" >&2; exit 2;; esac
case "$jobs" in 1|2|3|4|5|6) ;; *) echo "Expected one to six jobs" >&2; exit 2;; esac
test "$(uname -s):$(uname -m)" = Linux:x86_64
df -h "$root"
free -h
awk -v minimum=$((35 * 1024 * 1024)) 'NR==2 {exit ($4<minimum)}' \
  < <(df -Pk "$root") || { echo 'Upstream recommends at least 35 GiB free for this rebuild.' >&2; exit 2; }

project="$root/source"
git -c core.hooksPath=/dev/null clone --depth 1 --branch v1.0.0 \
    https://github.com/AlexZander-666/cycle-minimum-descent-real-roots.git "$project"
test "$(git -C "$project" rev-parse HEAD)" = e632c19bc246b819cd6b882cbf22c2fa9bc453de
test "$(cat "$project/formal/lean-toolchain")" = leanprover/lean4:v4.33.1
git -C "$project" rev-parse HEAD | tee "$logdir/source-revision.txt"

archive="$root/lean-4.33.1-linux.tar.zst"
curl --fail --location --silent --show-error --retry 3 \
    https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst \
    --output "$archive"
printf '890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235  %s\n' "$archive" \
    | sha256sum --check | tee "$logdir/toolchain-checksum.txt"
tar --zstd -xf "$archive" -C "$root"
unlink "$archive"
export PATH="$root/lean-4.33.1-linux/bin:$PATH"
unset LEAN_PATH LEAN_SRC_PATH LEAN_SYSROOT
export MATHLIB_NO_CACHE_ON_UPDATE=1
lean --version | tee "$logdir/lean-version.txt"
grep -F 'version 4.33.1' "$logdir/lean-version.txt"
lake --version | tee "$logdir/lake-version.txt"

cd "$project"
python3 -Bu scripts/verify.py | tee "$logdir/release-artifacts.log"
cd formal
# This caches external dependencies only. The project is rebuilt from an empty tree.
lake exe cache get | tee "$logdir/mathlib-cache.log"
git diff --exit-code -- lean-toolchain lake-manifest.json lakefile.toml
df -h "$root"

driver="$project/formal/verify_bounded.py"
if [ "$mode" = build ]; then
    # Retain the upstream scheduler, source checks, exact pin verification and axiom
    # audit. Omit only the second kernel pass in this resource-limited mode.
    python3 - "$driver" "$root/build-only.py" <<'PY'
from pathlib import Path
import sys
source, output = map(Path, sys.argv[1:])
s = source.read_text()
start = '            if any(m.startswith(mod+".") for m in modules):\n'
end = '        record=logs/(mod+".json")\n'
assert s.count(start) == 1 and s.count(end) == 1
i = s.index(start)
j = s.index(end, i)
block = s[i:j]
assert "leanchecker" in block and "replayFromImports" in block
s = s[:i] + s[j:]
s = s.replace("fresh local strict builds and independent kernel replays", "fresh local strict builds")
output.write_text(s)
PY
    driver="$root/build-only.py"
fi
ulimit -Sn 65536
python3 -Bu "$driver" "$project/formal" AllCutoffsManuscriptAudit "$root/rebuild" \
    --packages "$project/formal/.lake/packages" --jobs "$jobs" | tee "$logdir/formal-audit.log"
grep -F 'PASS: 499 fresh local strict builds' "$logdir/formal-audit.log"
grep -F '22 declarations audited.' "$logdir/formal-audit.log"

cd "$root/rebuild"
lake env lean -DwarningAsError=true "$entry/PrintOrdinary.lean" | tee "$logdir/exported-statements.log"
cp receipts/AllCutoffsManuscriptAudit.log "$logdir/axioms.log"
git -C "$project" status --porcelain --untracked-files=no | tee "$logdir/source-status.txt"
test ! -s "$logdir/source-status.txt"
