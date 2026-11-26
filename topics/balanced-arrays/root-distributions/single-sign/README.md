# Sharp coefficient thresholds for counting polynomial zeros in disks

For a polynomial $`P(z)=\sum_{j=0}^D a_jz^j`$ with strictly positive coefficients, write $`G_j=a_j^2/(a_{j-1}a_{j+1})`$ for each internal index. At $`0<k<D`$ set $`v_k=\sqrt{a_{k-1}/a_{k+1}}`$. Let $`N_{<}`$ and $`N_{\le}`$ count zeros, with multiplicity, in the open and closed disks of radius $`v_k`$.

**Disk-count theorem.** If every $`G_j>9/4`$, then

$$
k-1\le N_{<}\le N_{\le}\le k+1.
$$

Both counts equal $`k`$ exactly when $`(-1)^kP(-v_k)>0`$. At equality in the sign test, the only boundary zero is $`-v_k`$. For a negative test, one further imaginary-part sign distinguishes the two possible boundary-free counts and the case of a boundary conjugate pair. The threshold for the one-root error is sharp: $`(1+z)^4`$ has minimum quotient $`9/4`$, but at its middle radius the open count is zero and the closed count is four. The equivalence for the positive sign alone also holds when all quotients are at least $`9/4`$. [Manuscript, Theorem 2](paper.pdf) · [LaTeX source](paper.tex)

**Angular monotonicity.** If all quotients are at least $`\sqrt[3]{16}`$, the real part of $`P(v_ke^{i\theta})/(a_k(v_ke^{i\theta})^k)`$ decreases strictly for $`0<\theta<\pi`$. A reciprocal quartic gives sharpness. The proof uses the classical positivity of sine sums with convex coefficients. Under ordinary log-concavity alone a local $`G_k>4`$ already guarantees a boundary-free count of $`k`$, regardless of the size of the other quotients. [Proofs of Theorems 1 and 3](paper.tex) · [Classical antecedents and search record](literature.md)

## Balanced arrays

The disk-count theorem applies simultaneously at **every quota and every row cap** when $`2d\ge(n+2)\log(3/2)`$. This includes all geometric circles in the million-row example, even at quotas where the root type remains unknown. The radii depend on the actual array coefficients. In a different example with $`n=10^8`$, $`d=100`$ and $`r=50`$, the local factor-four theorem upgrades 64 distinct negative outer roots to **64 simple negative outer roots**. General balanced-array real-rootedness remains open. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Finite counts for the million-row example](../../dense-regime/below-cap/finite-aspect/upper-edge/README.md)

**Formal verification**　⬜ None. An independent agent-assisted reviewer checked the two sharp thresholds, the boundary classification, the factor-four result and the application to arrays. A second agent independently derived the convex-sine proof of angular monotonicity. The exact rational regression checker also implements the real sign test for a supplied coefficient vector. [Mathematical review](review.md) · [Exact checker](verify.py)

Run from this directory using Python 3.9 or later. The second command evaluates the sign of the polynomial at the negative geometric radius for $`k=1`$, with coefficients in ascending order.

~~~sh
python3 -IB verify.py
python3 -IB verify.py --sign 1 3 68 108 63
tectonic paper.tex
~~~
