# Splitting a prism-slice bound can destroy interlacing

For every integer $a\ge6$, the slice of level $a$ with bounds $(1^{2a-2},2)$ and the slice obtained by splitting the final bound into $(1,1)$ have Ehrhart numerators that fail to interlace. This disproves the splitting clause of Ferroni–McGinnis Conjecture 5.12. Individual real-rootedness for general prism slices remains open. [Original conjecture](https://doi.org/10.4153/S0008414X24000233)

At $a=6$, the degree-nine numerator has a root below $-850$ and the degree-ten numerator is strictly positive there. Both have simple negative roots. For $a\ge7$, their next leading coefficients contradict the ordering of root sums that interlacing requires. [Full disproof](paper.pdf) · [Manuscript source](paper.tex) · [Exact coefficient vectors](certificates/transport_split.json)

**🟩 Full · Lean 4 for the disproof.** The explicit split at $a=6$ is fully formalized. Lean starts with the integer points of the actual geometric dilations, proves affine dimensions 10 and 11, identifies the entire normalized count series, establishes numerator degrees 9 and 10, and proves that the roots cannot alternate. The final theorem has no Ehrhart or dimension hypotheses. [Final theorem](lean/PrismDimensions.lean) · [Formal statement and build](lean/Dimensions.md) · [Kernel verification](verification.json)

**🟩 Full · Lean 4 for the infinite family.** For $a\ge7$ use $b=a-1$ in the family theorem. Lean identifies the geometric counts and affine dimensions, constructs the full numerators, checks the top coefficients and degrees, and excludes weak interlacing of the real-root multisets. The proof bounds the split numerator's real roots above by one and uses the strict gap between the two next coefficients. Together with the separate $a=6$ theorem, this verifies every case $a\ge6$. [Family theorem](lean/PrismFamilyInterlacing.lean) · [Direct reciprocity and reproduction](lean/FamilyFeasibility.md)

The standalone verifier requires only Python. Run from this folder.

~~~sh
python3 -I -O verify_counterexample.py
~~~
