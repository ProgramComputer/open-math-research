# Eventual extension concavity at every quota in fixed dimension

Let $`a_k`$ count labeled binary arrays with $`n`$ rows, $`d`$ columns, common column sum $`k`$ and row cap $`r`$. Put $`D=\lfloor nr/d\rfloor`$ and $`u_k=(k+1)(a_{k+1}/a_k)^{1/d}`$ for $`0\le k<D`$.

For each $`d\ge2`$ there is an $`N(d)`$ such that for all $`n\ge N(d)`$ and all $`1\le r<d`$, the effective extension counts are strictly concave at every $`1\le k\le D-2`$. Empty ranges are vacuous. Full cap gives equality. The proof combines the compact interior regime with fixed and moving quotas at both ends. At the upper edge two negative contributions reinforce one another when the deficit is of order $`n^{1/3}`$.

- [Theorem and proof](proof.md)
- [Lower mesoscopic edge](sparse-edge.md) and [signed review](lower-edge-review.md)
- [Upper mesoscopic edge](upper-edge-mesoscopic.md) and [signed review](upper-edge-review.md)
- [LaTeX manuscript](paper.tex)

**Formal verification**　⬜ None. Both mesoscopic arguments were independently reviewed with agent assistance.

The threshold is existential and depends on the fixed dimension. The finite inequality over all parameter choices remains open. This supporting theorem concerns the original coefficients in [Per Alexandersson’s balanced-array conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays). It leaves the unrestricted real-rootedness question open.

From this directory, build the manuscript with `tectonic paper.tex`.
