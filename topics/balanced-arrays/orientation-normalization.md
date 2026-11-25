# An orientation proof of normalized log-concavity for balanced arrays

Fix $n,d\ge1$ and $1\le r\le d$. For a quota vector $\mathbf k=(k_1,\ldots,k_d)\in\{0,\ldots,n\}^d$, choose independent uniform $k_j$-subsets of $[n]$ as columns. Write $A(\mathbf k)$ for the number of arrays in which every row has at most $r$ ones and
$$
p(\mathbf k)=\frac{A(\mathbf k)}{\prod_j\binom n{k_j}}
$$
for the probability of this event.

**Theorem.** For all $n,d,r$, the extension ratio $p(\mathbf k+\mathbf e_i)/p(\mathbf k)$ is nonincreasing as any coordinate of $\mathbf k$ increases, wherever both ratios are defined. In particular, if $a_k=A(k,\ldots,k)$, then the sequence $\bigl(a_k/\binom nk^d\bigr)_{k=0}^n$ is log-concave.

**Real-rootedness consequence.** The polynomial $\sum_k a_k q^k$ has only simple negative zeros if
$$
(1+2/n)^{2d}>4.
$$
In particular, $d\ge(n+1)\log 2/2$ suffices for every row cap. A second sufficient condition is $d\ge\sqrt{nr\log 4}$, which is stronger when the row cap is small. The universal real-rootedness conjecture also covers sizes outside these bounds. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs).

## The orientation comparison and its use with two arrays

For a finite multigraph $G$, write $N_G(\mathbf a,\mathbf b)$ for the number of orientations with outdegree at least $a_v$ and indegree at least $b_v$ at every vertex $v$. Kahn and Neiman's graph orientation inequality states that, for nonnegative integer vectors,
$$
\mathbf a\ge\mathbf c,\mathbf e,\quad \mathbf a+\mathbf b\ge\mathbf c+\mathbf e
\quad\Longrightarrow\quad
N_G(\mathbf a,\mathbf b)\le N_G(\mathbf c,\mathbf e).
\tag{1}
$$
The inequalities between vectors are coordinatewise. This is Lemma 8 of the linked preprint in §4. Its multigraph formulation allows distinct edges with the same two endpoints. The use below is a reduction to this graph theorem. The independent-ball model of that paper and Chan's normalized matching theorems for competing urns have different sampling hypotheses, since a column here samples distinct rows. [Kahn–Neiman, Lemma 8](https://arxiv.org/pdf/1001.0610) · [Chan, Theorems 1.4 and 1.5](https://arxiv.org/pdf/2509.06273).

Consider an ordered pair of binary arrays, red and blue, in which their column quotas agree. The arrays may have different row degree constraints. In each column $j$ fix its set $C_j$ of rows occupied in both arrays and its set $D_j$ of rows occupied in exactly one array. Then $|D_j|=2m_j$ for an integer $m_j\ge0$, and each array occupies exactly $m_j$ of those rows. Refine this information by choosing a partition of each $D_j$ into unordered pairs, requiring each pair to contain one red-only row and one blue-only row. Every original ordered array pair with this common and exclusive row data admits exactly $\prod_j m_j!$ such partitions, by choosing the bijection of its $m_j$ red-only rows with its $m_j$ blue-only rows in each column.

For a fixed choice of the common and exclusive row data and of the unordered pairs, put a multigraph on the rows and give each pair one edge labeled by its column and its pair of rows. Orient each edge from the red-only row to the blue-only row. Conversely, every orientation determines both arrays uniquely and automatically gives their fixed column quotas. Parallel edges in different columns remain distinct.

Let $H_v$ be the degree of a vertex $v$ in this graph, and $c_v$ the number of columns with $v\in C_j$. The real row loads are $c_v+d^+(v)$ and $c_v+d^-(v)$, respectively. Suppose their required intervals are $[L_R,U_R]$ and $[L_B,U_B]$. Since $d^+(v)+d^-(v)=H_v$, these intervals are equivalent to the lower bounds
$$
a_v=\max\{0,L_R-c_v,H_v+c_v-U_B\},\qquad
b_v=\max\{0,L_B-c_v,H_v+c_v-U_R\}.
\tag{2}
$$
The clamping to zero is part of the conversion, even if the original constraints are infeasible. Swapping the row intervals of the two arrays interchanges $a_v,b_v$. If for all swapped rows $a_v\ge b_v$, then this swap gives new bounds $\mathbf c,\mathbf e$ with $\mathbf a\ge\mathbf c,\mathbf e$ at those rows and $\mathbf a+\mathbf b=\mathbf c+\mathbf e$. At an unswapped row, the same inequalities hold if $a_v\ge b_v$. In each comparison below this holds at every row. Thus (1) compares orientation counts for every fixed choice of the paired data. Summing and dividing by $\prod_j m_j!$ for each choice of $C_j,D_j$ compares the original counts. This division does not depend on which row constraints are used.

In two of the applications the actual quotas differ by one in a column. We then give that column its own extra row label, called its dummy row. The dummy cell in that column is occupied in the array with the lower quota. It is empty in the other array, and all other columns are zero at that dummy row in both arrays. The augmented column quotas now agree. The dummy row is always in the exclusive data of its own column, giving a vertex of degree one and with no common cell. A forced red dummy therefore has $(a_v,b_v)=(1,0)$ and a forced blue dummy has $(0,1)$. Deleting these auxiliary cells recovers the original arrays uniquely. The unordered real-cell data and the forced membership of the dummy row in the exclusive data specify exactly the same set of augmented skeletons on both sides of a comparison when the total original quotas are equal and the augmented quotas in each copy agree.

## Extension within one coordinate

Fix every column quota except that of column $i$. For $S\subseteq[n]$ let $F(S)$ count the arrays of the other columns with row cap $r-1$ on $S$ and row cap $r$ off $S$. The number $F(S)$ depends only on $|S|$ by row symmetry. For any $S,T\subseteq[n]$ we claim
$$
F(S\cap T)F(S\cup T)\le F(S)F(T).
\tag{3}
$$
In the product on the left let the red array have the lowered caps on $S\cap T$, and let the blue array have them on $S\cup T$. At a row of $S\triangle T$, their respective caps are $r$ and $r-1$, so (2) gives $a_v=\max(0,H_v+c_v-r+1)\ge b_v=\max(0,H_v+c_v-r)$. Elsewhere the two intervals agree and $a_v=b_v$. Changing the lowered-cap sets to $S$ for red and $T$ for blue swaps the two intervals just at rows in $S\setminus T$ and keeps them elsewhere. The quotas are identical throughout. This is the comparison (1), giving (3).

If column $i$ has quota $q$, conditioning on its occupied rows gives $p(\ldots,q,\ldots)=F(S)/\prod_{j\ne i}\binom n{k_j}$ for any $S$ of size $q$. Take $S,T$ of size $q+1$ intersecting in $q$ elements, possible for $0\le q\le n-2$. Then (3) gives the exact log-concavity inequality between quotas $q,q+1,q+2$. This proves the own-coordinate ratio comparison after division by its positive denominators.

## Extension across two coordinates

Fix distinct $i,j$ and a quota vector $\mathbf k$ with $k_i,k_j<n$. We claim
$$
A(\mathbf k)A(\mathbf k+\mathbf e_i+\mathbf e_j)
\le A(\mathbf k+\mathbf e_i)A(\mathbf k+\mathbf e_j).
\tag{4}
$$
In the product on the left the red quota vector is $\mathbf k$ and the blue vector is $\mathbf k+\mathbf e_i+\mathbf e_j$. Add one dummy row for each of the columns $i,j$. Both dummy cells must be red. In the product on the right, use the displayed order for red and blue. The $i$th dummy is blue and the $j$th dummy is red. Both copies in both products have augmented quota vector $\mathbf k+\mathbf e_i+\mathbf e_j$. The actual real-row cap remains $r$ in both colors, so (2) gives $a_v=b_v$ at every real row. At the $j$th dummy the forced bounds $(1,0)$ are unchanged, and at the $i$th dummy they change from $(1,0)$ to $(0,1)$. These bounds satisfy (1), and the fixed-skeleton factors agree. This proves (4), including when its left-hand side is zero.

The products of the binomial denominators on the two sides of (4) are equal. Thus (4) also holds for $p$, and dividing by $p(\mathbf k)p(\mathbf k+\mathbf e_j)>0$ gives the cross-coordinate ratio comparison.

The mixed comparison (4) also holds for weighted counts with forbidden cells and fixed, possibly unequal row intervals. A fixed row interval imposed on both copies still gives $a_v=b_v$. For a multiplicative cell weight, the weight of a pair of arrays is determined by the common and exclusive data, regardless of its coloring. The weight can therefore multiply the same orientation comparison, including a weight of zero for a forbidden cell. Inequality (3) uses row symmetry only when it is converted into the normalized quota comparison.

Along any coordinatewise increasing path with positive terminal probability the intermediate base probabilities are positive, since deleting occupied cells preserves the cap and thus feasibility. Therefore the adjacent comparisons give the stated ratio monotonicity between arbitrary comparable bases. To compare $p_{k+1}/p_k$ with $p_k/p_{k-1}$, concatenate the extensions in the same coordinate order on the two paths from the constant profiles $k$ and $k-1$, provided $p_{k+1}>0$. Each base of the first path is larger by one in every coordinate than the matching base on the second path. Multiplying the comparisons gives $p_{k+1}/p_k\le p_k/p_{k-1}$. All remaining diagonal indices satisfy the weak inequality by the contiguous support $0\le k\le\lfloor nr/d\rfloor$. Indeed, to realize a common quota $k$ with $dk\le nr$, draw $dk$ consecutive labels from the cyclic ordering of $n$ rows and assign successive groups of $k$ labels to the columns. Each group has distinct labels and each row is used at most $\lceil dk/n\rceil$ times.

## Coefficient separation for the original polynomial

At every internal positive-support index, normalized log-concavity gives
$$
\frac{a_k^2}{a_{k-1}a_{k+1}}
\ge \left(\frac{(k+1)(n-k+1)}{k(n-k)}\right)^d
\ge (1+2/n)^{2d}.
$$
The last inequality uses $k(n-k)\le n^2/4$. The strict coefficient-separation criterion applies when this final quantity is greater than $4$. Since $\log(1+2/n)>2/(n+1)$, the stated linear sufficient condition follows. Also $k+1\le nr/d$ for every internal index, giving
$$
\log\frac{a_k^2}{a_{k-1}a_{k+1}}
\ge d\log(1+1/k)>\frac{d}{k+1}\ge\frac{d^2}{nr}.
$$
This proves the second sufficient condition. Constant and linear polynomials have the stated root property directly, including $n=0$. For completeness, for positive coefficients $a_0,\ldots,a_m$ with $a_k^2>4a_{k-1}a_{k+1}$ at every internal index, put $t_k=\sqrt{a_{k-1}/a_{k+1}}$. These values are strictly increasing. At $-t_k$ each of the terms beside the $k$th term has less than half its magnitude. On each side the remaining magnitudes decrease moving outward by log-concavity. Pairing adjacent signed terms from distance two outward leaves a contribution of the same weak sign as the central term. The sign of the polynomial at $-t_k$ is therefore $(-1)^k$. The two limiting signs at zero and negative infinity account for all $m$ negative roots.

For an exact test that uses the full support, put $D=\lfloor nr/d\rfloor$ and, when $D\ge2$, let $m=\min(D-1,\lfloor n/2\rfloor)$. The smallest binomial factor over internal indices is $1+(n+1)/(m(n-m))$, since $k(n-k)$ increases up to the middle of the interval $0\le k\le n$. Its $d$th power can be tested against $4$ using integer arithmetic.

## Saturated-row counts

The same comparison gives an all-size result for the distributions of rows meeting their cap. Let $G_{\mathbf k}(S)$ count arrays with quota vector $\mathbf k$ and with saturated row set exactly $S$, meaning that the rows of $S$ have size exactly $r$ and all other rows have size at most $r-1$. Let
$$
w_{\mathbf k}(s)=\sum_{|S|=s}G_{\mathbf k}(S)=\binom ns G_{\mathbf k}(S_0)
\quad\text{for any }|S_0|=s.
$$

**Saturation theorem.** For each feasible $\mathbf k$, the sequence $w_{\mathbf k}(s)/\binom ns$ is log-concave with contiguous support. Moreover, whenever $\mathbf k^+=\mathbf k+\mathbf e_i$ is feasible,
$$
w_{\mathbf k}(s)w_{\mathbf k^+}(t)\ge w_{\mathbf k}(t)w_{\mathbf k^+}(s)
\qquad(0\le s<t\le n).
\tag{5}
$$
Thus the conditional saturation count increases in monotone likelihood ratio order upon increasing a quota. The real-rootedness of the saturation generating polynomial is a separate question.

At a row where red is saturated and blue is not, let $u=r-c_v$. The intervals in (2) now give
$$
a_v=\max(0,u,H_v-u+1),\qquad b_v=\max(0,H_v-u).
$$
In particular $a_v\ge b_v$. At a row where the two saturation statuses agree, $a_v=b_v$. We can therefore compare $G_{\mathbf k}(S\cup T)G_{\mathbf k}(S\cap T)$ with $G_{\mathbf k}(S)G_{\mathbf k}(T)$, by putting the larger saturation set in red on the first side. Swapping the statuses at the necessary rows preserves the sum of lower bounds. Inequality (1) gives the comparison for each paired skeleton. Taking $S,T$ of the same size with intersection one smaller establishes log-concavity after division by $\binom ns$.

To see contiguity, choose an array with the maximum feasible saturation count. If its count $s$ is above $\max(0,\sum_j k_j-(r-1)n)$, then both a saturated row and a row of load at most $r-2$ exist. Some column is occupied in the former row and absent in the latter because their row loads differ. Move that one entry to the latter row. The column quota is preserved, the cap still holds and the saturation count decreases by one. Iterating reaches the displayed lower bound and shows that every intervening count occurs.

For (5), choose fixed nested sets $S\subset T$ of sizes $s,t$. The product to be bounded is $G_{\mathbf k}(T)G_{\mathbf k^+}(S)$, again with the larger saturation set in red. Add the single dummy cell in column $i$ to red in both products, so the quotas agree in the paired representation and its bounds remain $(1,0)$. Comparing with $G_{\mathbf k}(S)G_{\mathbf k^+}(T)$ swaps the saturation constraints only on $T\setminus S$. Its new bounds satisfy (1) by the same local calculation. The factors $\binom ns\binom nt$ give (5). This cross-product statement requires no divisions at zero masses, including at the ends of support.

## A limit of real stability in two free column variables

A tempting sufficient route to the cross-coordinate inequality would be real stability of the count polynomial with two column quotas free and every other quota fixed. This fails already for $n=2$, $r=3$, and four fixed columns of quota one. Their only feasible row-size types are $(3,1)$ in either order, with $8$ total realizations, and $(2,2)$, with $6$. For two free columns with activity variables $x,y$, the resulting polynomial is
$$
F(x,y)=8(1+x)(1+y)+6(1+x+y)^2.
$$
In the first row type both free columns must avoid the full row. In the second, each row allows either one of the free columns or neither. At $y=-4/5$, the polynomial $25F(x,-4/5)=150x^2+100x+46$ has discriminant $-17600$. A nonzero real specialization of a real-stable polynomial in one variable would have only real roots. This example concerns the sufficient stability property, while (4) proves the actual coefficient comparison.

## A direct cap-three check

For $n=4$, $r=3$ and $\mathbf k=(1,1,2,2,2)$, the following counts were obtained by enumerating each actual column subset. [Direct enumerator](code/verify_orientation_example.py)

| Quota profile | Total valid arrays | Saturation vector in increasing $s$ |
|---|---:|---|
| $\mathbf k$ | 2388 | $(204,1404,780,0,0)$ |
| $\mathbf k+\mathbf e_1$ | 2712 | $(0,936,1632,144,0)$ |
| $\mathbf k+\mathbf e_3$ | 1320 | $(0,480,780,60,0)$ |
| $\mathbf k+\mathbf e_1+\mathbf e_3$ | 1284 | $(0,0,936,348,0)$ |
| $\mathbf k+2\mathbf e_1$ | 1284 | $(0,0,936,348,0)$ |

For the two coordinates, (4) has products $3{,}066{,}192<3{,}579{,}840$. For the first coordinate alone, after multiplying through by the binomial denominators, the normalized comparison has products $110{,}382{,}912<117{,}679{,}104$. The saturation comparison (5) for $s=1,t=2$ under the first-coordinate increment gives $2{,}291{,}328>730{,}080$.
