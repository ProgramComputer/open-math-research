# Lean verification for the prism split

[PrismGeometry.lean](PrismGeometry.lean) proves the finite noninterlacing certificate starting from the integer points in the actual dilations of the two real box slices. The ordered coordinate lists have length fixed by the bound vectors.

- `realSliceDilation` proves that scaling every coordinate by the dilation factor agrees with scaling the bounds and the prescribed sum, including at dilation zero. `integerPoint_iff_in_dilation` identifies the corresponding integer lattice points.
- `integerPointEquiv` maps each integer point to a bounded composition by taking natural values of its nonnegative coordinates. The inverse casts the coordinates back to integers. `cardinality_eq_boundedCount` uses the duplicate-free enumeration in [PrismSplit.lean](PrismSplit.lean) to identify the cardinality with the certified count.
- `ehrhartNumerator_eq_series_prefix` identifies the finite coefficient vector with the first $D+1$ coefficients of the count series multiplied by $(1-X)^{D+1}$. [PrismCounts.lean](PrismCounts.lean) checks every count needed for the two coefficient vectors. `integerPointNumeratorsDoNotInterlace` proves noninterlacing for those vectors.
- `integerPointSeriesPolynomialsDoNotInterlace` concludes noninterlacing for the polynomial evaluations given the normalized count-series identities and degree bounds $10$ and $11$. The accompanying mathematical proof supplies the lattice-polytope Ehrhart theorem and dimension calculation for these bounds, as well as the identification with two-row transportation polytopes.

## Reproduction

With `elan` on `PATH`, run from this directory. The project pins Lean and mathlib to version 4.19.0.

```sh
lake update
awk '/^import Mathlib\./ {print $2}' PrismSplit.lean PrismCounts.lean PrismGeometry.lean | sort -u | xargs lake exe cache get
mkdir -p .lake/build/lib/lean
export LEAN_NUM_THREADS=1
lake env lean -j1 -o .lake/build/lib/lean/PrismSplit.olean PrismSplit.lean
lake env lean -j1 -o .lake/build/lib/lean/PrismCounts.olean PrismCounts.lean
lake env lean -j1 PrismGeometry.lean
```

The macOS cache fallback in the [reproduction guide](README.md) also applies. The `PrismCounts.lean` check can take a few minutes.

## Recorded check

The source check exited successfully on Lean 4.19.0, commit `6caaee842e94`, using mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The ten printed theorem dependencies were identical.

```text
[propext, Classical.choice, Quot.sound]
```

The checked SHA-256 digests are recorded below.

| File | SHA-256 |
|---|---|
| `PrismSplit.lean` | `3ca6c87546927ddd0fef7427adcda14e06766f05f2323611eb5430373d11335a` |
| `PrismCounts.lean` | `38ee045e0ab84335216213f33e3eed6c21e2561d9d8c21ac46e4c36d52b29288` |
| `PrismGeometry.lean` | `b2ac968ccef79338ec761f172a6f3a245fa86b0d049a7e0362219bcf6bc60b87` |
