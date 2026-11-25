# Prism-slice splitting fails

At level \(a\), separating the double bound in \((1^{2a-2},2)\) into two unit bounds gives a pair of Ehrhart numerators that fail to interlace for every \(a\ge6\). At \(a=6\), one polynomial has a real root below \(-850\) and the other is positive there. At larger parameters the sums of the roots violate a necessary inequality for interlacing.

[Complete disproof](../../output/pdf/prism-splitting.pdf) · [Source](../../prism-splitting.tex) · [Exact coefficient vectors](../../certificates/transport_split.json) · [Standalone verifier](../../verify_counterexample.py)

Lean 4 verifies all 23 bounded-composition counts at the endpoint, the root obstruction and the algebraic coefficient gap at every larger parameter. The manuscript gives the Ehrhart interpretation. [Formal scope and reproduction](../../formalization/README.md)
