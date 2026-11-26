# Independent review of the quota Schur bound

**Verdict.** The claimed determinant bound and the stated dimension condition are correct. The binomial-basis consequence uses identical caps. The skew Schur reduction applies to the original cap model, where $`a_0=1`$.

For a nonzero permutation term, an adjacent inversion has a positive difference $`t=\sigma(i)-\sigma(i+1)`$. The two quota indices in descending order are $`b=\lambda_i-i+\sigma(i)`$ and $`a=\lambda_{i+1}-i-1+\sigma(i+1)`$. They satisfy $`b-a=t+1+\lambda_i-\lambda_{i+1}\ge t+1`$, so the swap is a strictly internal transfer to $`b-t,a+t`$. The factorial improvement is

$$
\frac{b!a!}{(b-t)!(a+t)!}\ge\frac b{a+1}\ge\frac b{b-1}.
$$

Indeed the factorial ratio is symmetric about the middle of the transfer interval and its consecutive ratios decrease, so its minimum among internal transfers occurs at either endpoint. Since $`2\le b\le K`$, the old product is at most $`y=(1-1/K)^d`$ times the new product in coefficient order. Multiplication by the other factors preserves this order. A nonzero old product forces a nonzero new one by the same inequality. A permutation product that starts at zero already satisfies the desired bound.

Adjacent inversion swaps sort the permutation in exactly its inversion count. Thus each term is coefficientwise at most $`y^{\ell(\sigma)}\prod_i a_{\lambda_i}`$. Keeping the identity term and bounding the odd terms by the sum of all nonidentity terms gives the factor $`2-\sum_\sigma y^{\ell(\sigma)}`$. Insertion of the largest letter gives the stated product enumerator, and the geometric-series comparison gives $`\sum_\sigma y^{\ell(\sigma)}\le(1-y)^{-(h-1)}`$. The condition $`2h(K-1)^d\le K^d`$ implies $`y\le1/(2h)`$, hence $`(1-y)^{h-1}\ge(h+1)/(2h)>1/2`$. This proves the claimed positivity threshold.

At unit weights, each monomial of a straight determinant identifies its union of occupied rows. Restricting to an exact union and relabeling it therefore gives the same count for every $`s`$-element union under identical caps. This yields the nonnegative coefficients of $`\binom ns`$. The sum is finite because every permutation term has total cell degree $`d|\lambda|`$. The coefficientwise estimate itself also allows identical row-specific intervals in all factors, including lower bounds.

For the skew reduction, choose increasing row and column indices $`p_i,q_i`$. If any $`q_i<p_i`$, the minor is zero because its first $`i`$ columns can use only the first $`i-1`$ rows in a nonzero permutation term. Otherwise, reverse both index lists and transpose the matrix. Taking

$$
\lambda_i=q_{h+1-i}+i-(p_1+h),\qquad \mu_i=p_{h+1-i}+i-(p_1+h)
$$

gives partitions with $`\mu\subseteq\lambda`$, and the minor is the specialization of $`s_{\lambda/\mu}`$ by $`h_j\mapsto a_j`$. This uses $`a_0=1`$ and $`a_j=0`$ for $`j<0`$. Arbitrary row intervals can have $`a_0=0`$, so the Schur step requires the stated original cap hypothesis. Each straight Littlewood–Richardson constituent $`\nu`$ is contained in $`\lambda`$ by symmetry of the coefficients, giving $`\ell(\nu)\le h`$ and $`\nu_1+\ell(\nu)-1\le q_h-p_1`$. Thus the same sufficient threshold, with $`K=q_h-p_1`$, also controls skew minors in that index range. Constituents of length zero or one have immediate positivity.

The all-minor finite Aissen–Schoenberg–Whitney implication is correctly scoped. This bound leaves straight partitions outside its dimension condition, so it establishes positivity of a specified class of higher minors without settling real-rootedness.

**Signed** — Independent mathematical reviewer, agent-assisted.
