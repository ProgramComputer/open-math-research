# Lean verification of prism-slice splitting

[PrismSplit](PrismSplit.lean) defines the bounded-composition count and proves the root separation. [PrismCounts](PrismCounts.lean) checks each of the 23 samples. [PrismGeometry](PrismGeometry.lean) identifies these counts with lattice points in actual dilations and relates their finite differences to the normalized count series. [PrismFamily](PrismFamily.lean) proves the binomial and Vieta obstruction for the infinite family.

The [geometry report](Geometry.md) states the remaining Ehrhart hypotheses in this version. [Kernel outputs](../verification.json) give the source digests and printed axiom dependencies. [Shared build instructions](../../../shared/lean/README.md)
