# Simple negative zeros for balanced arrays with at least linearly many columns

**Theorem.** Fix any $\epsilon>0$. For all sufficiently large $n$, for every $d\ge\epsilon n$ and every cap $1\le r\le d$, the balanced-array polynomial has exactly $\lfloor nr/d\rfloor$ distinct negative zeros. The row threshold depends only on $\epsilon$. Its value is unknown.

An array here is a labeled binary $n\times d$ matrix whose row sums are at most $r$. The coefficient of $q^k$ counts arrays in which every column sums to $k$. The theorem allows the cap and dimension to change at every row count. Together with the fixed-dimension eventual theorem, it confines any infinite sequence of distinct counterexamples to dimensions tending to infinity with $d/n\to0$. The conjecture for every finite triple remains open. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Related work and search record](literature.md)

The [proof](proof.md) passes from exact labeled column margins to a scalar coefficient via the dense binary-matrix enumeration theorem. Away from saturation the normalized alternating sum converges to a positive Gaussian theta sum. Near saturation the neighboring coefficients are strongly separated. [Central estimate](central.md) · [Saturated endpoint](saturated.md) · [Manuscript](paper.pdf) · [LaTeX source](paper.tex) · [Independent blind review](review.md)

**⬜ None.** The theorem has a written proof. It has no checked Lean or Rocq formalization.
