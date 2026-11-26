# Raising every column quota tilts the marked row toward larger sizes

Fix $`n`$ labeled rows and $`d`$ labeled columns. Rows other than the marked row have prescribed intervals of allowed sizes. Each occupied cell has a nonnegative weight and the weight of an array is the product of these weights. A zero weight can forbid a cell. Let $`F_{\boldsymbol q}(u)`$ be the sum of the weights of arrays with exact column margins $`\boldsymbol q`$ and marked row size $`u`$. Assume $`0\le q_j<n`$ for all columns. Take any positive integer $`K`$ at least $`\max_j\min(q_j,n-q_j-1)`$, and write $`\lambda=1+1/K`$.

**Proposed comparison.** For $`0\le s<t\le d`$,

$$
F_{\boldsymbol q}(s)F_{\boldsymbol q+\mathbf1}(t)
\ge \lambda^{t-s}F_{\boldsymbol q}(t)F_{\boldsymbol q+\mathbf1}(s).
$$

With indeterminate cell weights the difference of the left side and the right side has nonnegative coefficients. Each cell monomial fixes its common and exclusive cells, as used in the proof below. The calculation also allows either total weight to vanish. A common size interval may be imposed on the marked row by restricting the two size indices.

**Proof.** Color the array with margins $`\boldsymbol q`$ red and the array with margins $`\boldsymbol q+\mathbf1`$ blue on both sides. In each column $`j`$, fix all jointly occupied cells and all cells exclusive to one of the two colors, without fixing the color of an exclusive cell. Let $`h_j`$ be the number of red-exclusive cells. The margins and the number of common cells fix $`h_j`$. There are $`h_j+1`$ blue-exclusive cells. The red-only cells are a subset of the complement of the blue column, so $`h_j\le\min(q_j,n-q_j-1)\le K`$. The product of the two array weights is constant on these data.

Add one red dummy cell in each column, on a distinct auxiliary row. Pair the $`h_j+1`$ red-exclusive slots bijectively with the blue-exclusive slots. Put $`\rho=K/(K+1)`$. Give a pairing a factor

$$
b_j=1-\frac{h_j+1}{K+1}
$$

if the dummy is paired with the marked cell, and factor one otherwise. These factors are nonnegative and depend only on the uncolored pairing. When the marked cell is blue-exclusive, precisely a $`1/(h_j+1)`$ fraction of bijections incur the factor. The total weighted number of pairings in this column is then $`(h_j+1)!\rho`$. For every other disposition of the mark it is $`(h_j+1)!`$.

Hold all these unordered pairings fixed. Each pair gives a labeled edge between its endpoint rows, oriented from red to blue. Conversely, orientations satisfying the dummy requirements reconstruct the array pairs uniquely. At every ordinary unmarked row both colors have the same interval. If there are $`H`$ incident edges and $`c`$ common ones, the interval $`[l,u]`$ forces both in- and outdegree to be at least $`\max(0,l-c,H+c-u)`$. At the dummy vertices the outdegree must be one. At the marked vertex write $`c_*`$ for the number of common ones. We may discard data unless the total size of its two colored rows is $`s+t`$.

In the product on the right before the factor $`\lambda^{t-s}`$, the red row has size $`t`$ and the blue row has size $`s`$. The required outdegree and indegree at the mark are $`t-c_*`$ and $`s-c_*`$. On the left these two requirements interchange. If $`c_*>s`$ neither product contributes. All other degree constraints stay fixed. Write $`\boldsymbol a,\boldsymbol b`$ for the source out- and indegree lower bounds and $`\boldsymbol c,\boldsymbol e`$ for the target. At every vertex $`\boldsymbol a`$ dominates both target bounds, and $`\boldsymbol a+\boldsymbol b=\boldsymbol c+\boldsymbol e`$. Kahn and Neiman’s Lemma 8 therefore bounds the source orientation count above by the target count on this very same graph. [Kahn and Neiman, §4, Lemma 8](https://arxiv.org/pdf/1001.0610#page=9)

Multiply that inequality by the pairing factors and sum over unordered pairings while the underlying uncolored cell data are still fixed. Apart from the common product of factorials, every source array pair now has multiplicity $`\rho^{s-c_*}`$ and every target pair has multiplicity $`\rho^{t-c_*}`$. Thus the unweighted target count for these data is at least $`\rho^{-(t-s)}`$ times the source count. The same holds after restoring the fixed cell weights. The factor is independent of the data, so summing proves the assertion.

In particular, within a marked size interval the law at the larger margins dominates in likelihood ratio the law at the smaller margins tilted by $`\lambda^u`$. For example, if the upper permitted size is $`r`$, multiply each of the displayed inequalities with $`t=r`$ by $`\lambda^s`$ and sum over $`s`$. This gives the top-probability comparison directly, without any common-support assumption.

## Sharpness with indeterminate weights

Fix any positive integer $`K`$ and any number $`d`$ of columns. Take $`2K+1`$ rows, no row restrictions, and $`q_j=K`$ in every column. In the products comparing $`s=0`$ with $`t=d`$, take the cell monomial in which every cell of the whole matrix appears exactly once. In each contributing pair the two arrays are complementary. In the target the marked row is blue in every column; the red $`K`$ cells in that column are any $`K`$ of the $`2K`$ other cells. In the source the marked row is red, so there are $`K-1`$ more red cells to choose. Independent choices in the columns give the monomial-coefficient ratio

$$
\left(\frac{\binom{2K}{K}}{\binom{2K}{K-1}}\right)^d=(1+1/K)^d .
$$

Thus the base and its exponent are attained coefficientwise at every $`K`$ and every gap $`d`$. Passing to unit cell weights sums many cell monomials and can give a larger ratio.
