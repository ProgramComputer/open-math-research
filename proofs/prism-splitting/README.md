# Prism-slice splitting fails

At level \(a\), separating the double bound in \((1^{2a-2},2)\) into two unit bounds gives a pair of Ehrhart numerators that fail to interlace for every \(a\ge6\). At \(a=6\), one polynomial has a real root below \(-850\) and the other is positive there. At larger parameters the sums of the roots violate a necessary inequality for interlacing.

[Complete disproof](../../output/pdf/prism-splitting.pdf) · [Source](../../prism-splitting.tex) · [Exact coefficient vectors](../../certificates/transport_split.json) · [Standalone verifier](../../verify_counterexample.py)

Lean 4 proves that integer points in both dilated slices correspond to the counted compositions, computes the normalized count-series coefficients through the two dimensions, and rules out interlacing for those vectors. It also verifies the binomial and Vieta obstruction for the infinite family. The paper supplies Ehrhart polynomiality and its degree bound. [Geometric formalization and hypotheses](../../formalization/PRISM_GEOMETRY.md) · [Reproduction](../../formalization/README.md)
