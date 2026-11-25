# Formal proof of the prism counterexample

The final theorem `PrismSplit.finBoxSplitCounterexample` identifies the two full Ehrhart numerators for the published split at level six and proves they cannot interlace. It has no additional hypotheses. [Final Lean source](PrismDimensions.lean) · [Definitions, dimensions and verification](Dimensions.md)

The proof goes from [bounded compositions](PrismSplit.lean) and [count certificates](PrismCounts.lean) to [geometric dilations](PrismGeometry.lean), the [entire count series](PrismSeriesClosure.lean), and the actual affine dimensions and root obstruction. The separate [infinite-family module](PrismFamily.lean) proves the algebraic obstruction given the identified coefficients.

From the [shared Lean project](../../../shared/lean/README.md), run `lake build PrismDimensions`. [Recorded source digests and kernel reports](../verification.json)
