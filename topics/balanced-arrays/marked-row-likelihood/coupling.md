# From paired arrays to a normalized matching

Give each array weight equal to the product of the weights of its occupied cells. Only positive-weight arrays need be considered. Prescribe all column sums, put interval constraints on the other rows and condition the marked row to have one of two adjacent feasible sizes $`j,j+1`$. Fix any event increasing under inclusion of its marked set. Its probability increases from the first slice to the second if and only if

$$
\sum_{A,B} w(A)w(B)\bigl({\bf1}_{\mathcal U}(B_{\star})-{\bf1}_{\mathcal U}(A_{\star})\bigr)\ge0 ,
$$

where $`A,B`$ range over the indicated slices in that order and the star denotes the marked set. Constraints on the marked row depending only on its size have no effect within the slices.

In each column fix the cells occupied in both arrays and the cells occupied in exactly one. The latter split equally between the two arrays, say $`h`$ of each color. Pair the two colors bijectively within the column. Every array pair in these data admits $`h!`$ pairings in that column, and its product weight is fixed by the underlying cell data. Thus we may fix the unordered pairs in every column, prove the desired unnormalized comparison there, and divide by the product of the factorials on summation. This pairing is also used in the earlier array orientation argument. [Paired-array counting](../orientation-normalization.md)

The graph vertices are the rows. An edge connects the two exclusive row slots of each pair, and points away from the slot occupied by $`A`$. Each orientation recovers the two arrays with their prescribed column sums. If a row has $`c`$ common ones and $`t`$ incident edges, the two row sizes are $`c+i,c+t-i`$ for outdegree $`i`$. In a nonmarked row with interval $`[l,u]`$, both constraints are equivalent to

$$
L\le i\le t-L,\qquad L=\max(0,l-c,t+c-u).
$$

Discard infeasible data. When $`u\le3`$, put $`b=u-c\le3`$. We have $`t\le2b`$. Every allowed interval is one of the following.

| Constraint | Action on the graph |
| --- | --- |
| $`L=0`$ | Leave the vertex unrestricted. |
| $`L=1`$ | Require at least one edge in each direction. |
| $`t=2L`$ | Require equal in- and outdegrees. |
| $`t=2L+1`$ | Attach one edge to a new unrestricted leaf and require equal in- and outdegrees at the original vertex. |

For the last line every allowed orientation has a unique extension. The list is exhaustive because $`L\ge2`$ gives $`t\le b+L\le3+L\le2L+1`$. The four actions can be applied in the listed order whenever descriptions overlap.

At every vertex requiring $`a`$ edges in and $`a`$ out, pair its incident edge ends in opposite directions. Each admissible orientation has exactly $`a!`$ pairings at that vertex. Fix an unordered pairing and split the vertex into $`a`$ degree-two vertices, each carrying one pair of ends. Require one edge in each direction at each of these new vertices. Summing over such refinements and dividing by the factorial recovers the original counts. This operation leaves the marked vertex and its incident edge labels intact. [Chan, §4.1, Lemma 4.3](https://arxiv.org/html/2509.06273v1#S4.SS1)

Label the constrained vertices first and the marked vertex last to apply Chan’s Lemma 3.1. The constrained vertices require at least one incoming and one outgoing edge. The lemma allows parallel edges. At the marked vertex there are $`2s+1`$ incident edges, since its two original sizes differ by one and its common cells have fixed size $`j-s`$. The lemma couples by inclusion the outgoing subsets of sizes $`s`$ and $`s+1`$ with weights given by the counts of orientations. The two total weights agree by reversal. When these totals vanish the refinement contributes zero. If $`s=0`$ the inclusion is automatic. Each incident edge identifies a distinct marked column. Adding back the same common columns preserves inclusion. Reversal identifies the marked set of $`B`$ from the original lower slice with the outgoing set in the upper slice. The signed sum is consequently nonnegative for every fixed refinement. All multiplicities on summation are positive and independent of the orientations. This proves the result. [Swee Hong Chan, §3, Lemma 3.1](https://arxiv.org/html/2509.06273v1#S3)

At upper bound four the case $`c=0,t=6,l=0`$ permits outdegrees two, three and four. This is the first interval outside the four actions. The reduction makes no claim for that interval.
