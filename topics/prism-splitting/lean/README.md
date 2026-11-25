# Formal proof of the prism counterexample

The final theorem `PrismSplit.finBoxSplitCounterexample` identifies the two full Ehrhart numerators for the published split at level six and proves they cannot interlace. It has no additional hypotheses. [Final Lean source](PrismDimensions.lean) · [Definitions, dimensions and verification](Dimensions.md)

The endpoint proof goes from [bounded compositions](PrismSplit.lean) and [count certificates](PrismCounts.lean) to [geometric dilations](PrismGeometry.lean), the [entire count series](PrismSeriesClosure.lean), and the actual affine dimensions and root obstruction. For every $a\ge7$, use $b=a-1$ in the [family theorem](PrismFamilyInterlacing.lean). Its proof checks the [integer count extension](PrismFamilyCounts.lean), [direct reciprocity](PrismFamilyReciprocity.lean), [exact top coefficients](PrismFamilyTop.lean), and [geometric series and dimensions](PrismFamilyGeometry.lean). The two theorems cover all $a\ge6$.

From the [shared Lean project](../../../shared/lean/README.md), run `lake build PrismDimensions PrismFamilyInterlacing`. [Recorded source digests and kernel reports](../verification.json)
