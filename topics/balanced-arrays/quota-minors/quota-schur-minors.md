# A coefficientwise bound for higher unnormalized quota minors

Use the original common-quota counts $`a_j(\mathbf w)`$ with independent cell weights and a common set of row intervals, and take $`a_j=0`$ for impossible or negative quotas. For a partition $`\lambda`$ of length $`h\ge2`$ set $`K=\lambda_1+h-1`$, $`y=(1-1/K)^d`$. Then

$$
\det\left(a_{\lambda_i-i+j}\right)_{i,j=1}^h \succeq \left(2-(1-y)^{-(h-1)}\right)\prod_{i=1}^h a_{\lambda_i}.
$$

In particular every coefficient is nonnegative whenever $`2h(K-1)^d\le K^d`$. This covers arbitrarily high orders with an explicit dimension condition per partition. It does not assert higher-order total positivity of the factorial-normalized sequence.

Expand the determinant by permutations. For a term with indices $`u_i=\lambda_i-i+\sigma(i)`$ all nonnegative and nonzero product, sort $`\sigma`$ into the identity by swapping adjacent inversions. If the inversion at $`i,i+1`$ has difference $`t=\sigma(i)-\sigma(i+1)>0`$, the two current indices are $`b=u_i`$ and $`a=u_{i+1}`$ with $`b-a=t+1+\lambda_i-\lambda_{i+1}\ge t+1`$. After the swap they are $`b-t,a+t`$. The cellwise balancing inequality gives the ratio lower bound for the new product in coefficient order, namely $`[b!a!/((b-t)!(a+t)!)]^d`$. The factorial factor is symmetric in $`t`$ and $`b-a-t`$, and is minimized for an internal integer transfer at $`t=1`$ or $`b-a-1`$. Thus it is at least $`b/(a+1)\ge b/(b-1)`$. Since $`2\le b\le K`$, the old permutation term is at most $`y`$ times the new one, coefficientwise. Terms with an impossible quota contribute zero to the needed upper bound. After $`\ell(\sigma)`$ swaps, where $`\ell`$ counts inversions, the original term is at most $`y^{\ell(\sigma)}`$ times the identity term.

Ignoring positive even terms except for the identity, and bounding the sum of the negative terms by the sum over all nonidentity permutations, gives the theorem by the inversion enumerator

$$
\sum_\sigma y^{\ell(\sigma)}=\prod_{j=1}^h(1+y+\cdots+y^{j-1})\le(1-y)^{-(h-1)} .
$$

Inserting each new maximal element proves the product formula. If $`y\le1/(2h)`$, Bernoulli's inequality gives $`(1-y)^{h-1}\ge1-(h-1)y>1/2`$.

For identical uniform caps, setting cell weights to one and grouping each sign by its union of occupied row labels also gives nonnegative coefficients in the basis $`\binom ns`$ of these unnormalized straight determinants in this dimension range. Each monomial in the fixed-label inequality has a fixed union support, and the number of copies of a fixed $`s`$-label support in $`n`$ available labels is $`\binom ns`$. The partition and dimension are fixed while $`n`$ varies. This is relevant because Jacobi–Trudi and the nonnegative Littlewood–Richardson expansion express the other nontrivial Toeplitz minors as nonnegative linear combinations of straight Schur determinants for the specialization $`h_j\mapsto a_j`$, for the original cap model where $`a_0=1`$. [Stanley, Enumerative Combinatorics, Vol. 2, §§7.16 and 7.18](https://math.mit.edu/~rstan/ec/) By the finite Aissen–Schoenberg–Whitney criterion, nonnegativity of all its Toeplitz minors at unit weights would prove real-rootedness. [Aissen–Schoenberg–Whitney, I](https://doi.org/10.1007/BF02786970) Neither the dimension condition here nor finite computations remove the missing partitions.


## Polynomial degree for the finite screen

In the identical-cap model, the quota count $`a_j`$ is a polynomial in the row count $`n`$ of degree at most $`dj`$: an array has exactly $`dj`$ occupied cells and therefore uses at most $`dj`$ nonempty rows. Grouping by the set of occupied row labels gives its expansion in $`\binom ns`$. In each nonzero determinant term, the quota indices sum to $`|\lambda|`$ because the permutation displacements sum to zero. Its degree is therefore at most $`d|\lambda|`$, and the same is true of the determinant. Values at $`n=0,\ldots,d|\lambda|`$ determine the entire polynomial by forward differences. Positivity of its coefficients in this basis is stronger than nonnegative integer evaluations.
