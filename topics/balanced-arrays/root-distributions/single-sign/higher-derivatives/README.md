# Root counts at every coefficient curvature

Let $`P(z)=\sum_{j=0}^D a_jz^j`$ have positive coefficients and let each internal quotient $`a_j^2/(a_{j-1}a_{j+1})`$ be at least $`e^\lambda`$, with $`\lambda>0`$. For $`0<k<D`$ set $`v_k=\sqrt{a_{k-1}/a_{k+1}}`$. Write $`N_{<}`$ and $`N_{\le}`$ for the open and closed root counts at $`v_k`$, with multiplicity. Then

$$
k-\frac{e\pi^2}{8\lambda}\le N_{<}\le N_{\le}\le k+\frac{e\pi^2}{8\lambda}.
$$

The dependence on $`1/\lambda`$ has optimal order as $`\lambda`$ decreases to zero. The polynomial $`(1+z)^{2k}`$ shows this at its middle circle. The best universal constant remains open. The proof compares the two coefficient tails with a discrete Gaussian and counts real projection zeros using Jensen’s formula and periodicity. [Proof, Theorem 1](paper.pdf) · [LaTeX source](paper.tex) · [Review of the disk estimate](literature.md#jensen-count-bound)

A second bound gives an integer error $`m`$ whenever the common quotient bound is at least $`[2(m+1)]^{2/(2m+1)}`$. This is the sharp threshold for positivity of the $`m`$th derivative of the projection as a polynomial in $`\cos\theta`$ whenever its degree is at least $`m`$. A symmetric polynomial gives a counterexample to that derivative assertion below the threshold. Disk counts can obey the same error bound at smaller quotients. [Theorem 2 and its corollary](paper.tex) · [Independent review of the derivative threshold and boundary cases](review.md) · [Sharp one-root disk-count threshold](../README.md)

## Balanced arrays

For **every** row count, dimension and cap with an internal quota, the open and closed counts are within $`e\pi^2(n+2)/(32d)`$ of that quota at its geometric radius. These radii depend on the array coefficients. At fixed positive dimension-to-height ratio the error stays bounded as the degree grows. The result also gives counts in an annulus by subtracting the disk estimates. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Earlier limiting distributions](../../README.md)

| Rows | Columns | Maximum certified error at each geometric radius, every cap |
|---:|---:|---:|
| 1,000,000 | 125,000 | 5 |
| 1,000,000 | 100,000 | 7 |
| 1,000,000 | 1,000 | 838 |

**Formal verification**　⬜ None. Two agent-assisted reviews cover the proofs, including roots exactly on a counting circle. The exact checker tests the Chebyshev identities, quartic and higher-degree examples, and numerical bounds. The general real-rootedness conjecture remains open. [Source comparisons](literature.md) · [Exact checker](verify.py)

~~~sh
python3 -IB verify.py
tectonic paper.tex
~~~
