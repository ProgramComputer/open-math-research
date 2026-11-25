#!/bin/sh
set -eu

topic=$(CDPATH='' cd "$(dirname "$0")" && pwd)
shared=$(CDPATH='' cd "$topic/../../../shared/rocq" && pwd)
build=$(mktemp -d "${TMPDIR:-/tmp}/prism-rocq.XXXXXX")
trap 'rm -rf "$build"' EXIT
mkdir "$build/shared" "$build/topic"
shared_modules="BoundedCompositions FiniteDifferences PolynomialSeparation BoxReflection NumeratorTable PositiveSeries MonicRoots"
topic_modules="PrismEndpoint PrismDisproof PrismFamilyCounts PrismAffine PrismFamily Audit"

for module in $shared_modules
do
    cp "$shared/$module.v" "$build/shared/"
done
for module in $topic_modules
do
    cp "$topic/$module.v" "$build/topic/"
done

cd "$build"
rocq --version
for module in $shared_modules
do
    rocq compile -q -Q shared OpenMath -Q topic PrismSplit "shared/$module.v"
done
for module in $topic_modules
do
    rocq compile -q -Q shared OpenMath -Q topic PrismSplit "topic/$module.v"
done
rocq check -silent -Q shared OpenMath -Q topic PrismSplit PrismSplit.PrismFamily
echo "Rocq kernel recheck passed for PrismSplit.PrismFamily."
