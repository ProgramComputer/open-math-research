# Coefficientwise nonnegative row and quota minors at rank two

Let $A(n,\mathbf k)$ count labeled binary arrays of $n$ rows with column
quotas $\mathbf k$ and row cap two. A row with ones in columns $a,b$
has weight $w_{ab}$, while singleton and empty rows have weight one.
The weight of an array is the product of its row weights.

**Theorem.** For every $n\le m$ and every pair of componentwise ordered
quota vectors $\mathbf k\le\boldsymbol\ell$ on the same columns, every
coefficient of the following polynomial in the independent $w_{ab}$ is
nonnegative.
$$
 A(n,\mathbf k)A(m,\boldsymbol\ell)-A(n,\boldsymbol\ell)A(m,\mathbf k).
$$
In particular the matrix of counts by row number and common quota is
totally nonnegative of order two in every dimension. At positive
specializations this gives a monotone likelihood ratio wherever the
two rows have common positive support.

### Nested matching polynomials

Give each edge of a finite simple graph $H$ a separate variable $x_e$.
For an induced subgraph $G$ define
$$
b(G,j)=\sum_{M:\,|M|=|V(G)|-j}\ \prod_{e\in M}x_e .
$$
This counts ways to partition the vertices into $j$ blocks using singletons
and matched pairs. Values outside the support are zero. For $G\subseteq H$
induced and $i<j$ we claim
$$
 b(G,i)b(H,j)-b(G,j)b(H,i)\ \text{has nonnegative coefficients}.       \tag{1}
$$
We use the alternating-component method of Krattenthaler’s proof of
weighted matching log-concavity. Here the two graphs and the two shifts
from matching size to occupied blocks may differ. [Krattenthaler, 1996](https://doi.org/10.1006/jcta.1996.0058)

Fix an edge monomial and view its multiset of edges as the union of a red
matching on $G$ and a blue matching on $H$. Only monomials admitting at
least one such coloring need consideration. The alternating components are
paths, even cycles, or isolated doubled edges. At every vertex outside $G$
there can be at most one edge and that edge must be blue. Any path meeting
such a vertex has its coloring prescribed. A prescribed odd path has
one more blue edge than red edges, and a prescribed even path has equal
numbers. If two prescribed endpoint colors conflict, neither product
counts that multiset.

Write $s=|V(H)|-|V(G)|$, $h=j-i$, and let $e$ be the number of prescribed
odd paths. Their disjointness implies $0\le e\le s$. Let $t$ be the
number of free odd paths. Each can give blue excess $+1$ or $-1$. The
other components contribute an orientation factor independent of the
required excess. Thus the number of colorings of blue excess $d$ is that
factor times
$$
 \binom{t}{(t+d-e)/2},
$$
with value zero for indices outside $[0,t]$ or of the wrong parity.
In the positive product in (1), the blue excess is $s-h$. In the
subtracted product it is $s+h$. Since $|s-h-e|\le |s+h-e|$ and the
two indices have the same parity, symmetry and unimodality of the
binomial coefficients prove (1) for this monomial.

### From token matchings to labeled rows

Take $k_a$ distinguishable tokens for each column $a$, and join every
two tokens of different columns. Assign the common variable $w_{ab}$ to
each edge between columns $a,b$. A matching and its unused singleton
tokens form $j$ blocks. There are $(n)_{\underline j}$ injections of
these blocks into the rows. Every resulting array has $\prod_a k_a!$
token labelings. Thus for the token graph $G_{\mathbf k}$,
$$
  A(n,\mathbf k)=
  \frac{1}{\prod_a k_a!}\sum_{j\ge0}(n)_{\underline j}\,b(G_{\mathbf k},j).
$$
Choosing nested token sets makes $G_{\mathbf k}$ an induced subgraph of
$G_{\boldsymbol\ell}$. For $n\le m$ and $i<j$,
$$
(n)_{\underline i}(m)_{\underline j}-
(n)_{\underline j}(m)_{\underline i}\ge0.
$$
If the subtracted product is positive, cancel the common factors and
compare $(m-i)_{\underline{j-i}}$ with $(n-i)_{\underline{j-i}}$.
Otherwise the inequality follows directly. Expanding the two-by-two
determinant of $A$ by Cauchy–Binet combines these nonnegative numbers
with (1). Identifying edge variables of the same column types and
dividing by the two positive token-labeling factors preserves coefficient
signs. This proves the theorem, including zero quotas and empty graphs.
The unweighted matching interpretation for balanced arrays is recorded
in the original discussion. [Alexandersson’s tracker](https://github.com/PerAlexandersson/RealRooted/issues/2005)

### Consequence for consecutive interlacing

Write $P_n(x)=\sum_i a_i x^i$ and $P_m(x)=\sum_i b_i x^i$ for the common
quota specialization, $n\le m$. The coefficient of $x^i y^j$ in
$$
  \frac{P_n(x)P_m(y)-P_n(y)P_m(x)}{y-x}
$$
is $\sum_{k=0}^{\min(i,j)}(a_k b_{i+j+1-k}-b_k a_{i+j+1-k})$.
Consequently each entry of the Bézout matrix has nonnegative coefficients
in the row-pair weights. This includes the deformation in which only rows
$1100$ and $0011$ receive weight $u$. Proving definiteness of the
appropriate Bézout matrices would control interlacing. Their higher
principal minors remain open for the uniform four-column model.

**Scope and sources.** The original all-row zero problem remains open. Krattenthaler gives coefficientwise
inequalities for sizes of matchings in one graph. Gasharov treats
independent sets in claw-free graphs, and Li gives an equivariant
matching analogue. The proof above adapts the alternating path argument
to two nested induced graphs and then to arrays. A November 25, 2026
search of indexed literature, GitHub and indexed X pages covered “balanced
arrays”, “total positivity”, “nested graphs”, “matching numbers”,
“vertex deletion”, Alexandersson and weighted log-concavity.
We found no prior statement of this exact array minor in those searches.
Index coverage is incomplete. [Gasharov, 1999](https://doi.org/10.1016/S0012-365X(99)00106-5) · [Li, 2023](https://doi.org/10.5802/alco.284) · [Original array conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**⬜ None.** The proof is combinatorial. The accompanying exact checker
enumerates labeled arrays and their coefficients independently of the
matching argument. [Reproduction code](code/verify_rank_two_row_minors.py)

The direct enumeration covers dimension three through four rows and dimension
four through three rows. It checks 1,151 minors with a nonzero subtracted
product and records all 402 nonzero quota polynomials in the two ranges.
Run the following from the repository root with standard Python.
[Coefficient archive](results/rank-two-row-minors.jsonl.gz) · [Independent review, alternative argument, and limits at higher order](review-rank-two-row-minors.md)

~~~sh
python3 -I -B topics/balanced-arrays/code/verify_rank_two_row_minors.py --archive /tmp/rank-two-rows.jsonl
gzip -dc topics/balanced-arrays/results/rank-two-row-minors.jsonl.gz | cmp - /tmp/rank-two-rows.jsonl
python3 -I -B topics/balanced-arrays/code/check_lai_minor.py
~~~
