# Splitting a prism-slice bound can destroy interlacing

For every integer $a\ge6$, the slice of level $a$ with bounds $(1^{2a-2},2)$ and the slice obtained by splitting the final bound into $(1,1)$ have Ehrhart numerators that fail to interlace. This disproves the splitting clause of Ferroni–McGinnis Conjecture 5.12. Individual real-rootedness for general prism slices remains open. [Original conjecture](https://doi.org/10.4153/S0008414X24000233)

At $a=6$, the degree-nine numerator has a root below $-850$ and the degree-ten numerator is strictly positive there. Both have simple negative roots. For $a\ge7$, their next leading coefficients contradict the ordering of root sums that interlacing requires. [Full disproof](paper.pdf) · [Manuscript source](paper.tex) · [Exact coefficient vectors](certificates/transport_split.json)

**🟨 Partial · Lean 4.** Lean checks the finite lattice counts, the root separator, and the algebraic obstruction for the infinite family. The manuscript supplies the remaining geometric dimensions and Ehrhart identifications. [Checked theorems](lean/README.md) · [Kernel verification record](verification.json) · [Prior work and independent review](review.md)

The standalone verifier requires only Python. Run from this folder.

~~~sh
python3 -I -O verify_counterexample.py
~~~
