# Small-height cutoff logarithm on the common pin

[NumeratorCutoffAdapter.lean](NumeratorCutoffAdapter.lean) connects the [small-height odd-pole estimate](../fourier-circle/numerator-small-height.md) to the literal cutoff logarithm. It identifies every coefficient below the cutoff after multiplying by the corresponding power of the principal radius. The finite normalized sum in the contraction theorem is therefore the original cutoff polynomial.

The exported theorem is numerator_original_cutoff_series_contraction. The hypotheses and budget are the same as in the original small-height series estimate. Its contracted values are explicit infinite series. The [point form](NumeratorSmallHeightPoints.lean) uses the literal sample points and takes the analytic HasSum identity as a premise. The [full-disk logarithm identity](../fourier-stable/analytic-log-series.md) independently checks that premise.

The [checker](check.py) reuses the authenticated original cutoff import and the Lean 4.33.1 pin from the [real-axis check](../fourier-stable/README.md). It hashes the 4.19 research sources, applies the [compatibility patches](ports) and checks the resulting inputs with warnings treated as errors. The shared [pole and series definitions](../fourier-circle/NumeratorLogDefinitions.lean) are unchanged across pins.

From the repository root, with Lean 4.33.1 first on the path, run:

    python3 -Bu topics/long-cycle-excedances/lean/fourier-numerator/check.py /tmp/fourier-numerator

The [hosted workflow](../../../../.github/workflows/long-cycle-small-height-common-pin.yml) also accepts the authenticated import archive recorded by the common-pin checker.

The [verification record](verification.md) gives the exact pins, source hashes, axiom audit and LeanChecker replay.
