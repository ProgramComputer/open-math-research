#!/bin/sh
set -eu

topic=$(CDPATH='' cd "$(dirname "$0")" && pwd)
shared=$(CDPATH='' cd "$topic/../../../shared/rocq" && pwd)
build=$(mktemp -d "${TMPDIR:-/tmp}/prism-rocq.XXXXXX")
trap 'rm -rf "$build"' EXIT
mkdir "$build/shared" "$build/topic"
for module in BoundedCompositions FiniteDifferences PolynomialSeparation
do
    cp "$shared/$module.v" "$build/shared/"
done
for module in PrismEndpoint PrismDisproof Audit
do
    cp "$topic/$module.v" "$build/topic/"
done

cd "$build"
rocq --version
for source in shared/BoundedCompositions.v shared/FiniteDifferences.v \
              shared/PolynomialSeparation.v topic/PrismEndpoint.v \
              topic/PrismDisproof.v topic/Audit.v
do
    rocq compile -q -Q shared OpenMath -Q topic PrismSplit "$source"
done
rocq check -silent -Q shared OpenMath -Q topic PrismSplit PrismSplit.PrismDisproof
echo "Rocq kernel recheck passed for PrismSplit.PrismDisproof."
