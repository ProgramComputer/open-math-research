# Exact binomial odds for exchangeable unmarked rows

Consider an array with $`n\ge1`$ rows and $`d\ge1`$ columns. Let the unmarked rows have a common interval of allowed sizes and identical nonnegative weights within each column. The marked row may have its own nonnegative cell weights, including zeros. For integer column margins $`0\le a_i\le b_i\le n`$, write $`F_{\boldsymbol a}(j)`$ for the marked size weight. In a column with $`a_i<b_i`$, define

$$
\rho_i=\frac{a_i(n-b_i)}{b_i(n-a_i)} .
$$

In a column with $`a_i=b_i`$ put $`\rho_i=1`$. Set $`\rho=\max_i\rho_i`$. For all integers $`0\le s<t\le d`$,

$$
F_{\boldsymbol a}(t)F_{\boldsymbol b}(s)
\le \rho^{t-s}F_{\boldsymbol a}(s)F_{\boldsymbol b}(t).
$$

In particular if all columns rise from $`k`$ to $`k+1`$ with $`1\le k<n-1`$, the likelihood tilt is at least $`(k+1)(n-k)/[k(n-k-1)]`$ per size step. Unrestricted rows attain this factor since their marked bits are independent Bernoulli variables. The [coefficientwise theorem](likelihood.md) applies without exchangeability and has its own smaller sharp factor.

## Mark one unpaired cell

First take $`t=s+1`$. Use red for the smaller margins in both products, and blue for the larger. The source has the larger red marked size. Fix common and exclusive cells as in the coefficientwise proof. In column $`i`$ let $`h_i`$ be the count of red-only cells and $`\delta_i=b_i-a_i`$. Give the column $`\delta_i`$ distinct red-only auxiliary cells on separate rows and pair opposite colors within it. The number of unrestricted column refinements is $`\prod_i(h_i+\delta_i)!`$.

Independently pair opposite-colored exclusive cells **within the marked row**, leaving one exclusive cell unpaired there. If $`c`$ denotes the number of common marks, there are $`t-c`$ exclusive marks of the majority color and $`s-c=t-c-1`$ of the minority color. The number of these row refinements is $`(t-c)!`$ on either side. The single unpaired cell is uniform over the majority-color marks if the refinement is uniform.

Forbid a column auxiliary cell from being paired with the unpaired marked cell. This restriction depends only on the two uncolored pairings. In the source the unpaired mark is red and all auxiliaries are red, so every refinement is retained. Fix both pairings. In the orientation graph replace the marked vertex by one degree-two vertex for each row pair and one degree-one vertex for the unpaired mark. The degree-two vertices require one edge in each direction. The degree-one marked vertex points out in the source and in in the target. All column auxiliaries point out in both. Other vertices have symmetric degree constraints. Therefore Kahn and Neiman’s Lemma 8 bounds the source count above by the target count for every allowed refinement. [Orientation inequality](https://arxiv.org/pdf/1001.0610#page=9)

Divide the resulting counts for each cell monomial by $`\prod_i(h_i+\delta_i)!(t-c)!`$ before summing these data. The source becomes its full product count. The target becomes its weighted count with each array pair multiplied by its fraction of retained refinements. The pair weight is fixed on a cell monomial. If the target product count is zero, this comparison forces the source product count to be zero as well. Otherwise the weighted target count is its full product count times the retention probability under the target product law.

Under the target product law first fix both marked masks. The two arrays are independent and permutation of the $`N=n-1`$ unmarked rows preserves each of their laws separately. Choose the unpaired blue mark uniformly among the blue-only marks. This choice is independent of the unmarked parts, since the row pairing acts on labeled marked cells. Suppose the chosen column is $`i`$. If $`\delta_i=0`$ it is always retained. Otherwise put $`a=a_i`$, $`b=b_i`$, $`\delta=b-a`$. Among the unmarked rows the red column is a uniform $`a`$-subset and the blue column is an independent uniform $`(b-1)`$-subset. Their red-only count $`H`$ is hypergeometric. The retained fraction of column pairings is $`H/(H+\delta)`$. With the falling-outside-range convention for binomial coefficients, Vandermonde’s identity gives

$$
\mathbb E\frac{\delta}{H+\delta}
=\frac{\delta}{\binom Na}\sum_{h\ge0}
\frac{\binom{b-1}{a-h}\binom{N-b+1}h}{h+\delta}
=\frac{\delta}{b}\frac{\binom{N+1}a}{\binom Na}
=\frac{\delta n}{b(n-a)} .
$$

For the middle equality use $`\binom{b-1}{a-h}/(h+\delta)=\binom{b}{a-h}/b`$. The retained fraction averages to exactly $`\rho_i`$. Averaging over unpaired columns and marked masks gives at most $`\rho`$, as required.

## All size gaps

For any fixed margins and either law, the marked-size support is an interval. In the unweighted paired graph on equal margins, lowering the larger mark from $`t`$ to $`t-1`$ and raising the other from $`s`$ to $`s+1`$ for $`t\ge s+2`$ only balances its two degree requirements. Lemma 8 gives $`F(t)F(s)\le F(t-1)F(s+1)`$ also with cell weights. Moreover for any gap $`t-s`$, pairing the minority marked cells injectively with majority marked cells leaves $`t-s`$ degree-one vertices. Flipping their outgoing requirements to incoming with all other constraints fixed proves $`F_{\boldsymbol a}(t)F_{\boldsymbol b}(s)\le F_{\boldsymbol a}(s)F_{\boldsymbol b}(t)`$ before imposing the extra prohibition. Both orientations have the same refinement multiplicities. Hence when the source product is positive, both distributions have positive mass at every index from $`s`$ to $`t`$. Multiplying the adjacent comparisons and cancelling these positive intermediate masses proves the theorem. If $`\rho=0`$, positive source mass would already contradict the adjacent comparison. If the source vanishes the displayed inequality is immediate.

For the million-row application all unmarked rows have the same cap. For the two quotas $`q_i\in\{k-1,k\}`$ on the lower path, $`1-\rho_i=n/[(q_i+1)(n-q_i)]\ge4n/(n+1)^2`$. Thus the published inner and outer signs can be joined using the same [deficit transform and numerical brackets](finite.md), with this exact tilt replacing the concentration estimate.

[Lean verification of the overlap count and retention probability](lean/README.md) · [Exact numerical sign replay](exact-odds-output.txt)
