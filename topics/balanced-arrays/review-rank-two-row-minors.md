# Rank-two array counts and coefficientwise TP2

The agent-assisted review checks two proofs of the order-two claim. The direct alternating-path count establishes the stronger coefficientwise assertion for arbitrary induced graph inclusions. Applying the falling-factorial kernel gives the stated rank-two array inequality and coefficientwise nonnegative entries for the paired-deformation Bézoutian. These conclusions give no real-rootedness theorem.

## The weighted graph claim

Let $G=H[V(G)]$ be an induced subgraph, let $N=|V(G)|$ and $s=|V(H)\setminus V(G)|$, and let $m_p(J)$ be the weighted $p$-matching number, with a distinct variable for each edge of $H$ and zero outside the possible sizes. Set $F_J(z)=\sum_p m_p(J)z^{|V(J)|-p}$. Then for all integers $0\le i<j$ the polynomial
$$
\Delta_{ij}
=[z^i]F_G[z^j]F_H-[z^j]F_G[z^i]F_H
$$
has nonnegative coefficients in the edge variables. Here and below the two coefficient extractions in a product act on their respective polynomials.

Fix an edge multiset of the total size $2N+s-i-j$ contributing to either term, and color the embedded $G$ matching red and the $H$ matching blue. Every doubled edge is an isolated component with one copy in each color. Any remaining components are alternating paths and even cycles. A new vertex can only be isolated or an endpoint with a blue edge. An even path with both endpoints new cannot occur in any valid coloring, so its multiset contributes zero to both sides. An odd path with a new endpoint is forced blue at both ends and contributes $1$ to the excess of the blue size over the red size. Let $e$ be the number of these forced odd paths. They are disjoint and each uses a new endpoint, so $0\le e\le s$.

Let $t$ be the number of free odd paths, all of whose vertices are old. The doubled edges, even cycles and even paths contribute no excess. Their numbers of colorings multiply both terms by the same factor. The free odd paths independently contribute $+1$ or $-1$. The count for excess $d$ is therefore that common factor times $\binom{t}{(t+d-e)/2}$, interpreted as zero for an unavailable index. The positive term needs $d=s-(j-i)$, while the negative term needs $d=s+(j-i)$. The two required indices have the same integrality condition. Their distances from $t/2$ satisfy
$$
|s-(j-i)-e|\le |s+(j-i)-e|.
$$
This also puts the positive index in range whenever the negative one is in range. Symmetry and unimodality of the binomial coefficients give the claim separately for each edge multiset.

The induced-subgraph hypothesis matters. If $G$ is edgeless on two vertices and $H$ adds an edge of weight $w$ on the same vertices, then $[z^1]F_G[z^2]F_H-[z^2]F_G[z^1]F_H=-w$.

## Independent numerical-weight proof

For a one-vertex inclusion $G=H-v$, the weighted matching-polynomial interlacing theorem provides a partial fraction expansion of $\mu_G(w)/\mu_H(w)$ with nonnegative residues and simple poles after cancellation. The quotient is odd, so opposite poles have equal residues. The identity
$$
\frac{F_G(-w^2)}{F_H(-w^2)}=-\frac{\mu_G(w)}{w\mu_H(w)}
$$
then pairs each pair of nonzero poles into a term $2\gamma/(z+\lambda)$ for $\lambda>0$. A pole at zero gives $\gamma_0/z$. Every $F_H/(z+\lambda)$ appearing in this expansion is real-rooted with nonnegative coefficients.

Write $q_i=[z^i]F_H/(z+\lambda)$ and $f_i=[z^i]F_H$. For $i<j$ one has
$$
q_if_j-q_jf_i=q_iq_{j-1}-q_jq_{i-1}\ge0
$$
by log-concavity and interval support. If the term on the right being subtracted is positive, all intervening ratios are defined and nonincreasing. Summing over the residues proves the one-vertex inequality. Under further vertex additions the endpoints of the support $[|V(J)|-\nu(J),|V(J)|]$ can only increase, using the matching number in the graph of positive-weight edges. If the reverse product for an initial and terminal pair of coefficient sequences is positive, every intermediate sequence is positive at both indices, so the adjacent ratio inequalities multiply. Otherwise the endpoint inequality follows from nonnegativity. [Heilmann and Lieb, Theorem 4.2](https://doi.org/10.1007/BF01877590)

## Transfer to arrays and the Bézoutian

Use $k_i$ labeled tokens of color $i$ and the fixed edge variable or weight for each two-color row type. A matching specifies the rows containing pairs, while unmatched tokens specify singleton rows. Inject the resulting occupied rows into the $n$ row labels and divide by the number $\prod_i k_i!$ of token labelings of a given array. Thus
$$
A(n,\mathbf{k})=\frac{\sum_i (n)_i[z^i]F_{G(\mathbf{k})}(z)}{\prod_j k_j!}.
$$
Token graphs for componentwise ordered quotas are induced inclusions with a common set of edge labels. Identifying variables of the same color pair preserves coefficientwise nonnegativity. For $n\le m$ and $i<j$, the minor $(n)_i(m)_j-(n)_j(m)_i$ is nonnegative. When the subtracted product is nonzero, cancel $(n)_i(m)_i$ and use monotonicity of $(m-i)_{j-i}$ in $m$. The order-two Cauchy–Binet formula now gives coefficientwise nonnegativity of $A(n,\mathbf k)A(m,\boldsymbol\ell)-A(n,\boldsymbol\ell)A(m,\mathbf k)$ for $\mathbf k\le\boldsymbol\ell$. The two column factorial denominators are common to both terms.

In the paired $U(2,4)$ deformation, put weight $u$ on pair types $12$ and $34$ and $1$ on the four cross-pairs, and take $\mathbf k=(k,k,k,k)$. Write $P_n(q,u)=\sum_i a_i(u)q^i$ and $P_m(q,u)=\sum_j b_j(u)q^j$ with $n\le m$. The chosen Bézoutian orientation is
$$
\frac{P_m(x,u)P_n(y,u)-P_n(x,u)P_m(y,u)}{x-y}
=\sum_{i<j}(a_i b_j-a_j b_i)x^iy^i
\sum_{r=0}^{j-i-1}x^{j-i-1-r}y^r .
$$
Its entries are polynomials with nonnegative coefficients in $u$, so they are nonnegative at every $u\ge0$. Positive semidefiniteness is a separate condition. For instance, the same entrywise argument holds for the unrelated pair $1+q$, $1+2q+2q^2$, whose Bézoutian matrix is $\left(\begin{smallmatrix}1&2\\2&2\end{smallmatrix}\right)$ with determinant $-2$.

## Prior work and the boundary at higher orders

Alexandersson's original issue already gives the unweighted diagonal matching formula and explicitly leaves the balanced extraction open. It suggests total positivity as a possible route. [Original issue and exact statement](https://github.com/PerAlexandersson/RealRooted/issues/2005)

Krattenthaler's Theorem 2 proves strong coefficientwise log-concavity for matching numbers **in one graph** and its proof uses alternating red/blue components. The nested argument uses the same switching structure and adds the control of forced blue components. Gasharov extends the same-graph statement to the order-two minors of the graph-elementary-symmetric matrix for claw-free graphs. Shiyue Li proves a same-graph equivariant extension and explicitly credits Krattenthaler's switching construction. Neither statement above compares two distinct induced subgraphs with matching size shifted by their respective vertex counts. [Krattenthaler, JCTA 74, 351–354 and author copy](https://doi.org/10.1006/jcta.1996.0058) · [Author's PostScript](https://mat.univie.ac.at/~kratt/artikel/matching.html) · [Gasharov, Discrete Mathematics 205, 229–234](https://doi.org/10.1016/S0012-365X(99)00106-5) · [Li, §2.1](https://doi.org/10.5802/alco.284)

For unit edge weights, the occupied-row coefficients are graphical Stirling numbers of the complement whenever that complement has no independent set of size three. The general weighted graph argument only counts partitions into singletons and pairs, even when larger independent sets exist. Galvin and Thanh's graphical Stirling work concerns log-concavity and consecutive interlacing for forests and cycles. [Galvin and Thanh](https://arxiv.org/abs/1206.3591)

Lai's Problem 31 asks about coefficientwise nonnegativity of **all** Toeplitz minors of the same-graph weighted matching sequence. The line-graph counterexamples posted by Matherne and Morales to claw-free Schur positivity give an obstruction. In their Example 2.1, let $J=H_1$ be the original 12-edge graph. The all-edge squarefree coefficient of the order-four minor
$$
\det\bigl(m_{3-i+j}(J)\bigr)_{0\le i,j\le3}
$$
is $-64$. Equivalently this is $[s_{(3,3,3,3)}]X_{L(J)}$ by dual Jacobi–Trudi and the Hall involution. The weight of a product of matchings on the all-edge monomial counts proper edge colorings with those prescribed color-class sizes. The independent exact checker expands the displayed determinant and counts the ordered matchings directly. The only nonzero grouped contributions are $128-3\cdot320+768=-64$. Run `python3 -I -O check_lai_minor.py` from this directory. The same determinant is obtained by taking the nested induced chain $H_s=J\sqcup sK_1$ for $s=0,1,2,3$ and occupied-row exponents $|V(J)|-3,\ldots,|V(J)|$, since $F_{H_s}=z^sF_J$. Thus even the nested coefficient matrix does not have coefficientwise positivity at every order. The calculation is for that coefficient matrix before applying the falling-factorial kernel. [Lai, Problem 31](https://arxiv.org/pdf/2109.01466) · [Matherne and Morales, Example 2.1](https://arxiv.org/html/2607.21508v1#S2)

The 2026-11-25 search included “matching numbers” with “coefficientwise”, “strongly x-log-concave”, “vertex deletion”, “induced subgraph”, “alternating paths”, “likelihood ratio” and “total positivity”, as well as “graphical Stirling numbers” with “nested” and “total positivity”. Indexed searches on GitHub and X used “Krattenthaler”, “matching numbers”, “graphical Stirling numbers”, “balanced arrays” and “total positivity”. GitHub contains the original matching formula. These searches found no exact predecessor for the nested induced coefficient minor or the weighted array consequence. Indexed X search is incomplete. This is a scoped provenance finding.
