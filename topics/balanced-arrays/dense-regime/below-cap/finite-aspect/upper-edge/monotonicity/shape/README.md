# The shape of the row-slack error

Fix the number of columns $`d`$ and the row cap $`2\le r<d`$. For a total of $`nr-s`$ ones, choose labeled column sums as equal as possible and take a uniform capped binary matrix with these margins. Let $`M`$ count the rows containing fewer than $`r`$ ones. Define

$$
E_n(s)=\mathbb E M-\frac{ns}{n+s-1},\qquad E_n(0)=0.
$$

**Theorem.** For all sufficiently large numbers of rows $`n`$, the sequence of $`E_n(s)`$ at each fixed residue of $`s`$ modulo $`d`$ is unimodal. There are at most two maximizing grid points, consecutive in that residue. Their distance from $`nt_*`$ is bounded independently of $`n`$, where $`t_*`$ is the unique maximum of an explicit tilted-binomial function. The maximum satisfies

$$
\max\lbrace 1,\sqrt{r(d-r)/d}\rbrace <t_*<r.
$$

Across individual steps, including changes of residue, $`E_n(s+1)>E_n(s)`$ for $`1\le s`$ and $`s+1\le n\sqrt{r(d-r)/d}`$. The first two values coincide at zero. Beyond the maximum the one-step differences are strictly negative outside a bounded number of grid points near $`nt_*`$. The height threshold and the bound on this number may depend on $`d,r`$. At $`r=1`$ the exact function is $`s(s-1)/(n+s-1)`$, with the stated convention at zero.

This settles the scale-one row-switching comparison at every fixed dimension for all sufficiently large heights. The limiting scalar function alone does not give this conclusion. The proof uses the symmetry of the first finite-height correction and a uniform expansion when few entries or few units of slack remain. The sign of the array polynomial throughout the finite transition, and uniform bounds as both $`n`$ and $`d`$ grow, remain open. [Original balanced-array conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Earlier finite obstruction above this scale](../README.md) · [Row switching](../../README.md) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/2)

**Formal verification**　⬜ None. [Proof](proof.md) · [Scalar review](scalar-review.md) · [Finite transfer review and literature](review.md) · [Exact checks](verify.py)

~~~sh
python3 -IB verify.py
~~~

The exact checker covers 10,875 rational tilt values and 3,115 labeled fibers at 119 parameter triples. It checks every slack for $`2\le n\le12`$, $`2\le d\le5`$ and every proper cap, and every slack at $`n\in\{16,32,64\}`$, $`d\in\{3,5,8\}`$ with cap $`d-1`$. The ensuing fixed-phase sequences were unimodal. Every positive-slack unit step tested below the stated cutoff was strictly increasing. The archive records every fiber count and its total number of deficient rows. [Exact finite data](finite-checks.json.gz)
