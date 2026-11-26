# Exact homogeneous marked-row odds with caps up to three

Fix a marked row in an array of $n$ rows and $d$ columns. Each unmarked row $i$ has its own integer size interval $[L_i,U_i]\subseteq[0,d]$, with $U_i\le3$. The marked row may also have a size interval. Each occupied cell contributes an arbitrary nonnegative real weight. For a common column margin $k$, write $f_k(S)$ for the total weight of arrays whose marked set is exactly $S$, and $F_k(j)=\sum_{|S|=j}f_k(S)$.

For integer margins $1\le a<b\le n-1$ and sizes $0\le s<t\le d$, set

$$
\lambda=\frac{b(n-a)}{a(n-b)}.
$$

Then

$$
F_a(s)F_b(t)\ge \lambda^{t-s}F_a(t)F_b(s).
$$

## Positive endpoint fibers

First take all weights strictly positive. The crossed product $F_a(t)F_b(s)$ may be assumed positive. The weak two-margin orientation comparison then gives $F_a(s)F_b(t)\ge F_a(t)F_b(s)>0$. For this comparison, fix the cell monomial of a pair, color the smaller-margin array red, and add $b-a$ exclusive red auxiliary cells in each column on distinct rows. Pair the red and blue exclusive cells within each column. The distinct auxiliaries force their incident edges outward on both sides. Every real unmarked row has the same constraint in both colors, giving symmetric lower bounds on the two degrees, even when row intervals differ across rows. At the marked vertex, the larger red degree requirement and smaller blue degree requirement interchange. Kahn and Neiman's orientation inequality gives the weak comparison on each fixed uncolored pairing, and all colorings have the same refinement multiplicity for that monomial. Common marked cells contribute equally to both row sizes. Any interval imposed on the marked row allows the same two sizes on each side. [Kahn and Neiman, §4, Lemma 8](https://arxiv.org/pdf/1001.0610#page=9)

At each fixed margin the feasible marked sizes form an interval. In the bipartite circulation for the array, fix the marked-row arc to any intermediate integer load and interpolate fractional feasible flows from the two endpoint arrays. Circulation integrality gives a binary array at the prescribed load. Thus both quota levels have positive mass at every size from $s$ to $t$. At a common quota with strictly positive cell weights, permuting columns maps any feasible marked mask to every other mask of its size. All these masks therefore have positive weight at both quota levels.

## The mask likelihood ratio

Let $N=n-1$, let $Z(v)$ be the residual fiber weight on the unmarked rows at column vector $v$, and write

$$
B(v)=\frac{Z(v)}{\prod_j\binom N{v_j}}.
$$

The [global normalized ratio theorem](proof.md) applies to the residual problem with its original row-specific intervals. For neighboring masks $S\subset T=S\cup\lbrace i\rbrace$ in the sizes under consideration, take $v_k=k\mathbf 1-\mathbf 1_S$. The residual profiles for $S$ and $T$ are respectively $v_k$ and $v_k-e_i$. The bases $v_a-e_i\le v_b-e_i$ and their increments are positive by the endpoint argument. The rectangular cuts in the global theorem give positivity on the interval needed for its ratio comparison. Taking reciprocals of the positive extension ratios gives

$$
\frac{B(v_b-e_i)}{B(v_b)}\ge\frac{B(v_a-e_i)}{B(v_a)}.
$$

The extra marked cell contributes its weight $w_{\star i}$, and $(v_k)_i=k$ because $i\notin S$. Therefore

$$
\frac{f_k(T)}{f_k(S)}
=w_{\star i}\frac{Z(v_k-e_i)}{Z(v_k)}
=w_{\star i}\frac{k}{N-k+1}\frac{B(v_k-e_i)}{B(v_k)}.
$$

The base binomial ratio is $k/(n-k)$. Dividing the odds at $b$ by those at $a$ produces a factor at least $\lambda$. Hence $g(S)=f_b(S)/(\lambda^{|S|}f_a(S))$ is increasing across neighboring masks in these slices.

## From masks to sizes

At fixed margin $a$, use the [adjacent marked-slice inclusion coupling](https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/marked-row-likelihood/coupling.md). Its hypothesis concerns each unmarked row's upper bound separately, so the upper bounds need only be at most three. The two marginals on sizes $j$ and $j+1$ weight the marked masks proportionally to $f_a$. The coupled masks are nested, so the mean of $g$ in size $j$ is at most its mean in size $j+1$. Since every mask of either size has positive $f_a$ weight, the slice mean is exactly $F_b(j)/(\lambda^jF_a(j))$. Iterating from $s$ to $t$ and cross multiplying proves the stated inequality. A zero source product is immediate from nonnegativity.

For zero cell weights, replace all zeros by $\varepsilon>0$. Both sides of the asserted inequality are polynomials in the cell weights. The inequality therefore persists as $\varepsilon$ tends to zero, including at endpoints where a whole slice loses its mass.

## Scope

The normalized residual ratio theorem permits arbitrary row intervals. The upper bound of three is used in the inclusion coupling. At cap four, its direct graph reduction leaves the degree-six interval of outdegrees two through four untreated. Forming two disjoint opposite-direction pairs and leaving two incidences free gives multiplicities $12,18,12$ across those outdegrees, so one fixed denominator does not recover the required orientation counts. This is a limitation of that reduction. The weighted marked-row tilt for general caps and the unrestricted balanced-arrays real-rootedness conjecture remain outside the result. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)
