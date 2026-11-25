# Splitting a prism-slice bound can destroy interlacing

For every integer $a\ge6$, the slice of level $a$ with bounds $(1^{2a-2},2)$ and the slice obtained by splitting the final bound into $(1,1)$ have Ehrhart numerators that fail to interlace. This disproves the splitting clause of Ferroni–McGinnis Conjecture 5.12. Individual real-rootedness for general prism slices remains open. [Original conjecture](https://doi.org/10.4153/S0008414X24000233)

At $a=6$, the degree-nine numerator has a root below $-850$ and the degree-ten numerator is strictly positive there. Both have simple negative roots. For $a\ge7$, their next leading coefficients contradict the ordering of root sums that interlacing requires. [Full disproof](paper.pdf) · [Manuscript source](paper.tex) · [Exact coefficient vectors](certificates/transport_split.json)

**🟩 Full · Lean 4 for the disproof.** The explicit split at $a=6$ is fully formalized. Lean starts with the integer points of the actual geometric dilations, proves affine dimensions 10 and 11, identifies the entire normalized count series, establishes numerator degrees 9 and 10, and proves that the roots cannot alternate. The final theorem has no Ehrhart or dimension hypotheses. [Final theorem](lean/PrismDimensions.lean) · [Formal statement and build](lean/Dimensions.md) · [Kernel verification](verification.json)

**🟨 Partial · Lean 4 for the infinite-family strengthening.** The mathematical proof covers every $a\ge6$. Lean verifies the binomial inequality and Vieta obstruction for $a\ge7$. The identification of those two general coefficients with the family of slice numerators remains in the paper. [Family theorem](lean/PrismFamily.lean)

The standalone verifier requires only Python. Run from this folder.

~~~sh
python3 -I -O verify_counterexample.py
~~~
