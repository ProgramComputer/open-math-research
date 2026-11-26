# Independent check of the fixed-shape factorial cutoff

Signed by agent-assisted reviewer four_blind, 2026-11-26.

**Verdict.** The domination criterion is valid for straight and fixed skew minors, and it gives a terminating decision algorithm for every fixed shape. The cutoff alone is sufficient and can fail even when every remaining Newton coefficient at the exceptional dimension is nonnegative.

## Inversions and the factorial factor

Pad $`\lambda,\mu`$ to a common length with $`\mu_i\le\lambda_i`$, and set $`x_i=\lambda_i-i`$, $`y_i=\mu_i-i`$. Each sequence is strictly decreasing. Write $`q_i(\sigma)=x_i-y_{\sigma(i)}`$ for the quotas of a determinant term, with negative quotas giving zero. If $`i<j`$ and $`\sigma(i)>\sigma(j)`$, then $`t=y_{\sigma(j)}-y_{\sigma(i)}>0`$ and $`q_i-q_j=(x_i-x_j)+t>t`$. Swapping these two assignments changes the paired quotas to $`q_i-t,q_j+t`$. Nonnegative quotas stay nonnegative and the swap uses a permitted balancing transfer in every column. Sorting by adjacent inversions terminates at the identity. The factorial factors telescope over the whole path and give

$$
\prod_i a_{q_i(\sigma)}(\mathbf w)
\preceq
\rho_\sigma^d\prod_i a_{\lambda_i-\mu_i}(\mathbf w),
\qquad
\rho_\sigma=\prod_i\frac{(\lambda_i-\mu_i)!}{q_i(\sigma)!}.
$$

All other factors have nonnegative coefficients and can multiply each two-factor comparison. Each individual inversion swap strictly decreases the factorial product: transferring $`t`$ from $`b`$ to $`a`$, with $`0<t<b-a`$, gives product ratio $`\prod_{j=0}^{t-1}(b-j)/(a+j+1)>1`$ by reversing the denominator factors and using $`b>a+t`$. Thus $`0<\rho_\sigma<1`$ for every contributing nonidentity term. Negative-quota terms can be omitted even in polynomial identities. Terms that vanish only at particular $`n,d,r`$ can still be included in the upper bound. [Cellwise balancing input](../cellwise-balancing.md)

Keeping the identity term and subtracting the odd permutations yields coefficientwise nonnegativity when $`\sum_{\sigma\ \mathrm{odd}}\rho_\sigma^d\le1`$. The same coefficientwise estimate implies nonnegative binomial-basis coefficients in the number of rows for uniform caps: the multidegree in cell marks records the exact row union of all factors, and labeled row symmetry identifies the contributions for every union of a given cardinality. Straight shapes take $`\mu=0`$.

## Effective finite reduction

At fixed shape, discard all negative-quota permutations and compute the exact rational odd-permutation sum at successive integer dimensions. If it is empty, the criterion holds immediately. Otherwise all its bases are strictly below one and the sum decreases to zero, so the first dimension where it is at most one is found in finite time. Only dimensions below that cutoff require further testing, and each has only $`d`$ ranks.

Put $`S=|\lambda|-|\mu|`$. Every product of array counts in the determinant uses exactly $`dS`$ occupied sites counted across the factors. Its row union has size at most $`dS`$, so the determinant as a function of $`n`$ is an integer-valued polynomial of degree at most $`dS`$, even when a few small $`n`$ have infeasible positive quotas. Values at $`n=0,\ldots,dS`$ recover all binomial-basis coefficients by forward differences. Nonnegative basis coefficients give immediate positivity for all nonnegative integers. In the general case, check the zero polynomial and constant cases separately. A negative leading coefficient rules out nonnegativity for all heights. For positive leading coefficient $`c_m`$, an exact root bound $`1+\max_{j<m}|c_j/c_m|`$ in the ordinary monomial basis places all roots in a finite interval. The polynomial is strictly positive to the right of that bound by its eventual positive sign and continuity. Exact evaluation up through its ceiling decides the remaining heights. The algorithm is shape-by-shape. It does not give a single bound over all partitions.

## Exact small exceptions to the cutoff

[The standard-library checker](check.py) enumerates all straight partitions through the first exceptional weight in each of dimensions two and three. The initial cutoff failure in each dimension is unique at its weight.

| Dimension | First weight | Shape | Odd-permutation bound | First positive height by cap in ascending order |
| ---: | ---: | --- | --- | --- |
| 2 | 5 | $`(1^5)`$ | $`293/288`$ | $`2,1`$ |
| 3 | 9 | $`(1^9)`$ | $`935292579533443/884902330368000`$ | $`3,2,1`$ |

For both exceptional shapes and every cap in the respective dimension, all binomial-basis coefficients are nonnegative. The [manifest](manifest.jsonl) records first positive values, the number of positive basis coefficients, and the highest-degree basis coefficient. The checker forms each determinant by its signed permutation expansion, counts labeled rows by exact margin dynamic programming and obtains the basis coefficients by independent forward differences. No numerical root isolation is needed for these exceptions.

~~~sh
python3 -B check.py | diff - manifest.jsonl
~~~
