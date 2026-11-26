# A finite coefficient bound from the marked-row comparison

Suppose $`2\le r<d`$. Let $`a_k`$ count balanced arrays, $`D=\lfloor nr/d\rfloor`$, and write $`e_i(\boldsymbol q)`$ for the saturation probability of one row conditional on missing column $`i`$ at margins $`\boldsymbol q`$. Raising that column multiplies the count normalized by $`\prod_h\binom n{q_h}`$ by $`1-e_i`$. Each $`e_i`$ increases coordinatewise on feasible bases by the orientation inequality. The cyclic construction gives full support up through $`D`$. Degrees zero and one need no further test. [Identities and orientation comparison](../orientation-normalization.md)

Fix $`1\le k<D`$. Along the path from equal quota $`k-1`$ to equal quota $`k`$, let $`\boldsymbol q`$ be a base and $`i`$ its next column. The corresponding base on the next path is $`\boldsymbol q+\mathbf1`$. Every coordinate of $`\boldsymbol q`$ is at most $`k<n`$, so the [marked-size comparison](likelihood.md) applies with $`K=k`$ and $`\lambda=1+1/k`$. Give the marked cell of column $`i`$ zero weight in both fibers and restrict the marked size to $`0,\ldots,r`$. The probability of size $`r`$ in the plus law is at least its probability in the original missing-cell law tilted by $`\lambda^{|S|}`$. Both conditional fibers have positive mass by feasibility and row symmetry.

Let $`e=e_i(\boldsymbol q)`$, $`e^+=e_i(\boldsymbol q+\mathbf1)`$ and $`U=r-|S|`$ in the original missing-cell law. Let $`v=\mathbb E[\lambda^{-U}\mid U>0]`$. Since the positive deficits are integers, $`v\le1/\lambda`$. The tilted bound and its consequence for the survival probabilities are

$$
e^+\ge\frac e{e+(1-e)v},\qquad
\frac{1-e}{1-e^+}\ge 1-e+\frac e v\ge1+\frac e k .
$$

The survival probabilities in both phases are positive, because the next insertion is feasible. At every phase $`e\ge e_0`$, the balanced missing-cell loss at $`k-1`$. Set $`y=d(k-1)/n`$. Row and column symmetry give $`e_0=(d-r)\Pr(J=r)/(d-y)`$ for the size $`J`$ of an unrestricted marked row in that fiber. Since $`J\le r-1+{\bf1}_{J=r}`$ and $`\mathbb EJ=y`$, we have

$$
e_0\ge \frac{d-r}{d-y}(y-r+1)_+ .
$$

Telescoping the normalized counts along the two paths and restoring their binomial factors now gives

$$
\left(\frac{a_k^2}{a_{k-1}a_{k+1}}\right)^{1/d}
\ge (1+1/k)(1+1/(n-k))(1+e_0/k).
$$

To obtain one bound at every index, observe that $`1+e_0+k/(n-k)\ge\max(1,y/(r-1))`$. For $`y\le r-1`$ this is immediate. Otherwise write $`h=y-r+1\in[0,1]`$. We have $`k/(n-k)\ge y/(d-y)`$ and $`y\ge h(r-y)`$, so the preceding lower bound yields $`e_0+k/(n-k)\ge h`$. Also $`1+h\ge y/(r-1)`$ for $`r\ge2`$.

Expanding the three positive factors through their linear terms and using $`k=1+ny/d`$, the second quotient to the power $`1/d`$ is therefore at least

$$
1+\frac{\max(1,y/(r-1))}{1+ny/d}\ \ge\ 1+\frac d{d+n(r-1)} .
$$

The last inequality follows by multiplying the maximum by $`1+n(r-1)/d`$, bounding the constant term by one and the other term by $`ny/d`$. When the $`d`$th power exceeds four, all internal second quotients exceed four. At each geometric radius $`\sqrt{a_{k-1}/a_{k+1}}`$ both adjacent terms have magnitude below half the central term. The remaining alternating tails from distance two give nonnegative contributions relative to its sign, by log-concavity. The radii increase strictly. The signs at zero, these radii on the negative axis, and negative infinity therefore isolate $`D`$ distinct negative roots. [Coefficient-separation argument](../orientation-normalization.md)

For each fixed cap $`r\ge2`$, consider $`d`$ tending to infinity with $`d^2/n`$ tending to a constant $`c`$ strictly between $`(r-1)\log4`$ and $`r\log4`$. The logarithm of our uniform lower bound tends to $`c/(r-1)>\log4`$. At the largest internal index $`k=\lfloor nr/d\rfloor-1`$, the logarithm of the unrestricted binomial second quotient tends to $`c/r<\log4`$, since $`k\sim nr/d`$ and $`d/n\to0`$. This gives infinitely many triples for which the improvement crosses the factor-four threshold.
