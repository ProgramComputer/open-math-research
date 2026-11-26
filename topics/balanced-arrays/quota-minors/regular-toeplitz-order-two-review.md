# Independent review of cellwise order-two Toeplitz positivity

**Verdict.** The dummy-pairing comparison proves the proposed coefficientwise order-two inequality, including the stronger comparison in each fixed common/exclusive fiber. At unit cell weights it also proves nonnegative binomial-basis coefficients in the common row count for every order-two Toeplitz minor. Higher-order positivity of the factorial-normalized sequence fails already at order three.

## Fixed-cell comparison

Fix $`0\le a\le b\le n`$, $`0\le t\le\delta=b-a`$, and common and exclusive row sets $`C_j,D_j`$ in each real column. Write $`x_j=a-|C_j|`$ and $`y_j=b-|C_j|`$. A fiber with zero source count already satisfies the desired inequality, so in the argument below $`x_j\ge0`$ and $`y_j=x_j+\delta`$. Augment column $`j`$ by $`\delta`$ labeled degree-one dummy rows. In the target specify a fixed set of $`t`$ dummies that will turn blue. Each array pair on either side has a unique prescribed dummy extension. In each color and column the augmented quota is $`b`$. Use the same set of unordered matchings of the augmented exclusive locations on both sides, forbidding dummy–dummy pairs. Orient each edge away from its red endpoint.

If a real row has $`c`$ common entries and paired degree $`H`$, its outgoing and incoming minimum requirements are both $`\max(0,H+c-r)`$. These symmetric bounds are unchanged in the target. The dummy bounds are $`(1,0)`$ at the source and either $`(1,0)`$ or $`(0,1)`$ at the target. Thus in every fixed multigraph skeleton, the source outdegree requirements dominate both target vectors, while the coordinatewise sums of the requirements are equal across the comparison. These are exactly the hypotheses of Kahn–Neiman's orientation inequality. Distinct parallel edges are allowed. [Kahn–Neiman, §4, Lemma 8](https://arxiv.org/pdf/1001.0610#page=9)

At the source there are $`y_j!`$ allowed pairings in column $`j`$. At the target there are $`x_j+t`$ red real and $`y_j-t`$ blue real locations. Assign the $`t`$ blue dummies injectively to red real locations, the $`\delta-t`$ red dummies injectively to blue real locations, and biject the remaining $`x_j`$ locations in each color. This gives $`(x_j+t)!(y_j-t)!/x_j!`$. The set of flipped dummies was fixed, so this multiplicity has no extra binomial factor. The ratio of source and target refinements is

$$
\frac{y_j!x_j!}{(x_j+t)!(y_j-t)!}
=\prod_{\ell=1}^t\left(1+\frac{\delta-t}{x_j+\ell}\right)
\ge \frac{b!a!}{(a+t)!(b-t)!}.
$$

The product bound uses $`x_j\le a`$. The empty product at $`t=0`$ and the factors at $`t=\delta`$ give equality as expected. Summing the orientation comparisons and dividing by the refinement factors proves the claimed bound in each fiber. If the source count is zero, handling that fiber directly avoids factorials at negative arguments.

## Polynomial consequences and scope

The fixed common/exclusive data specify the cell monomial, since common cells have exponent two and exclusive cells have exponent one. Thus, with $`T_k=(k!)^d A_{n,k}(\mathbf w)`$,

$$
T_{a+t}T_{b-t}-T_aT_b
$$

has nonnegative coefficients in the individual cell weights. Any order-two Toeplitz minor of $`[T_{j-i}]`$ has this form when its extreme indices are in range. Indexing the sequence by zero outside its legal support handles all remaining minors. The same reasoning gives coefficientwise order-two positivity for the unnormalized counts, since the factorial ratio is at least one.

At unit weights, group array pairs by the union of the occupied real rows. Each common/exclusive fiber has a fixed union, so the difference stays nonnegative when restricted to any chosen union. Relabeling a union of size $`s`$ to $`[s]`$ shows that its count depends only on $`s`$. Summing gives a finite expansion in $`\binom ns`$ with nonnegative coefficients. This refers to the row count shared by all entries of a Toeplitz minor indexed by quota. Arbitrary separately weighted rows have the cellwise inequality, while the binomial-basis statement uses row symmetry.

The existing orientation argument already proves a stronger numerical normalization by $`\binom nk^{-d}`$ at unit weights, and it includes a weighted mixed comparison in two quota coordinates. The additional conclusions checked here are the factorial-normalized comparison in each cell monomial across arbitrary inward quota shifts and its fixed-union consequence. This review verifies those differences in scope and makes no priority claim.

For a higher-order limitation, at $`n=9,d=2,r=1`$ and unit weights the normalized counts are $`T_k=(9)_{2k}`$. Thus $`(T_0,T_1,T_2,T_3)=(1,72,3024,60480)`$. The minor of rows $`0,1,2`$ and columns $`1,2,3`$ is $`72^3-2\cdot72\cdot3024+60480=-1728`$. Hence the same factorial-normalized Toeplitz matrices can fail at order three. The original unnormalized higher minors remain a separate question.

I independently enumerated capped rows for $`0\le n\le4`$, $`1\le d\le4`$, and all caps. Exact counts verified 150 interior quota comparisons across the shapes, with 1,076,812 cell-monomial comparisons overall. In the 42,087 fibers with positive source count, I also checked the sharper refinement factor before replacing it by the uniform factorial ratio.

**Signed** — Independent mathematical reviewer, agent-assisted.
