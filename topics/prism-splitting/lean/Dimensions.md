# Finite-coordinate verification of the prism split

`PrismSplit.finBoxSplitCounterexample` gives integer polynomials of degrees $9$ and $10$ that equal the full normalized lattice-point series of the two prism slices and whose complete real-root lists cannot weakly alternate. It uses the affine dimension of each real slice in the normalization. [Lean source](PrismDimensions.lean)

The starting slice has bound vector $(1^{10},2)$ and coordinate sum $6$. The split slice has bound vector $(1^{12})$ and the same sum. The theorem `realFinSlice_eq_box_intersection` gives the box intersected with the coordinate-sum hyperplane, as in equation (1) of Ferroni and McGinnis. `splitReplacesLastBound` verifies the exact replacement from Conjecture 5.12. [Ferroni and McGinnis, equation (1)](https://arxiv.org/pdf/2202.11808v2#page=1) · [Conjecture 5.12](https://arxiv.org/pdf/2202.11808v2#page=20)

- `unsplitAffineDimension` and `splitAffineDimension` prove the affine dimensions $10$ and $11$. The direction of each affine span is the kernel of the coordinate-sum map. The proof scales an arbitrary sum-zero vector until adding it to the box midpoint preserves the bounds, and then applies rank–nullity to the coordinate-sum map.
- `finLatticeEquiv` identifies integer vectors in each geometric dilation with the ordered lists used by the duplicate-free bounded-composition count. This includes dilation zero.
- `unsplitFinEhrhartSeries` and `splitFinEhrhartSeries` give full formal power-series identities for these counts. `unsplitEhrhartDegree` and `splitEhrhartDegree` use the certified coefficient lists to establish the exact polynomial degrees, which fix the orientation of the interlacing test. [Whole-series proof](PrismSeriesClosure.lean)

## Kernel check

Run from `shared/lean` with elan available, after the [shared dependency and cache setup](../../../shared/lean/README.md).

```sh
export LEAN_NUM_THREADS=1
lake build PrismSeriesClosure
lake env lean -j1 ../../topics/prism-splitting/lean/PrismDimensions.lean
```

The source passed a serial check with Lean 4.19.0, commit `6caaee842e94`, and mathlib 4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The ten printed theorem dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The checked SHA-256 for `PrismDimensions.lean` is `1ba0a0455a8a13ba2739afc7da173ecc5d44c8d5fc7137929e253dc79615df59`.
