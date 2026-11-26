#!/usr/bin/env bash
# Replay the declaration-closed export from an already built v4.36.0 workspace.
set -euo pipefail

if [[ $# != 3 ]]; then
  echo 'Usage: replay-kernel.sh <built shared/lean directory> <artifact directory> prism|catalan' >&2
  exit 2
fi

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
workspace="$(cd -- "$1" && pwd -P)"
mkdir -p -- "$2"
artifact_root="$(cd -- "$2" && pwd -P)"
topic="$3"
case "$topic" in
  prism)
    modules=(PrismDimensions PrismFamilyInterlacing AuditPrismExportType)
    theorems=(PrismSplit.finBoxSplitCounterexample PrismFamily.familyBoxSplitCounterexample AuditExportType.prismSix AuditExportType.prismFamily)
    ;;
  catalan)
    modules=(CatalanStrictPeaksAllInterlacing AuditCatalanExportType AuditCatalanWordBridge)
    theorems=(CatalanStrictPeaks.strict_peaks_all_lengths AuditExportType.catalan AuditReference.catalanPolynomial_eq)
    ;;
  *)
    echo "Unknown audit topic: $topic" >&2
    exit 2
    ;;
esac

artifact_dir="$artifact_root/$topic"
mkdir -- "$artifact_dir"
cd -- "$workspace"
mathlib_expected=fc4f59e577feb1a4956671bc04ac18aaaf8cd842
mathlib_actual="$(git -C .lake/packages/mathlib rev-parse HEAD)"
if [[ "$mathlib_actual" != "$mathlib_expected" ]]; then
  echo "Wrong Mathlib revision: $mathlib_actual" >&2
  exit 1
fi

lean_prefix="$(lake env lean --print-prefix)"
exporter="$lean_prefix/bin/leanexport"
official_checker="$lean_prefix/bin/leanchecker"
independent_checker="$lean_prefix/bin/nanoda_bin"
for tool in "$exporter" "$official_checker" "$independent_checker"; do
  [[ -x "$tool" ]] || { echo "Missing release executable: $tool" >&2; exit 1; }
done
{
  "$lean_prefix/bin/lean" --version
  echo "Mathlib commit $mathlib_actual"
  echo 'Bundled Nanoda source 4c544ed4099c8227f07d5de77ad1e69fb0740a27'
  sha256sum -- "$lean_prefix/bin/lean" "$exporter" "$official_checker" "$independent_checker"
} > "$artifact_dir/toolchain.txt"

export_file="$artifact_dir/solution.ndjson"
lake env "$exporter" "${modules[@]}" -- "${theorems[@]}" \
  > "$export_file" 2> "$artifact_dir/export.stderr"
if [[ -s "$artifact_dir/export.stderr" ]]; then
  cat -- "$artifact_dir/export.stderr" >&2
fi
python3 -I "$script_dir/audit_export.py" "$export_file" "${theorems[@]}" \
  > "$artifact_dir/dependencies.json"

"$official_checker" --from-export "$export_file" 2>&1 | tee "$artifact_dir/leanchecker.log"
grep -Fxq 'Lean default kernel accepts the solution' "$artifact_dir/leanchecker.log"

cat > "$artifact_dir/nanoda.json" <<'EOF'
{
  "use_stdin": true,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true,
  "unsafe_permit_all_axioms": false,
  "nat_extension": true,
  "string_extension": true,
  "num_threads": 1,
  "print_axioms": false,
  "print_success_message": true
}
EOF
"$independent_checker" "$artifact_dir/nanoda.json" < "$export_file" \
  2>&1 | tee "$artifact_dir/nanoda.log"
declaration_count="$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["declaration_count"])' \
  "$artifact_dir/dependencies.json")"
grep -Fxq "Checked $declaration_count declarations with no errors" "$artifact_dir/nanoda.log"
printf '%s\n' 'PASS: exact export passed the official Lean kernel and independent Rust Nanoda.' \
  | tee "$artifact_dir/VERDICT.txt"
