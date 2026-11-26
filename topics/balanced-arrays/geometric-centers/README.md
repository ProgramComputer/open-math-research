# Failure density of the geometric-center sign test

For fixed $d\ge2$ and $1\le r\le d$, let $a_{n,k}$ count labeled $n\times d$ binary arrays with common column sum $k$ and each row sum at most $r$. Write $P_n(q)=\sum_k a_{n,k}q^k$ and let $t_{n,k}=(a_{n,k-1}/a_{n,k+1})^{1/2}$ at each internal quota.

**Theorem.** As $n\to\infty$, the proportions of internal quotas where $(-1)^kP_n(-t_{n,k})$ is positive or negative both tend to one half. The proportion of zero evaluations tends to zero. These limits hold within every fixed positive-length closed quota-ratio interval strictly inside $(0,r/d)$, and over the entire row. The case $d=r=1$ is outside the theorem. [Proof](bulk-center-density.md) · [Coefficient estimate](bulk-center-coefficients.md) · [Compact saddle estimate](bulk-center-phase.md) · [Independent review](bulk-center-density-review.md)

An alternating sign at every geometric center is a sufficient test for simple negative zeros. This theorem limits the test and gives no counterexample to the balanced-array real-rootedness conjecture. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

The full-cap endpoint limit gives related sign reversals in the entire function $E_d$. A fixed-dimension asymptotic gives density one half there, and exact alternating-series certificates cover all 450 cases $2\le d\le10$, $1\le k\le50$. [Endpoint result and reproduction](hyperbessel-centers.md) · [Exact checker](certify-hyperbessel-centers.py) · [Data](hyperbessel-centers.json)

**⬜ None.** The obstruction has a written proof and exact computational checks. It has no checked Lean or Rocq formalization.
