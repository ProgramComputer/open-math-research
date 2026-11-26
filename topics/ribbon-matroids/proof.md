# The ribbon matroid conjecture

**Theorem.** For every connected ribbon lattice path matroid of rank $r$,

$$
 Z_M(t)=N_{r+1}(t)=\sum_{i=0}^r\frac{1}{r+1}\binom{r+1}{i}\binom{r+1}{i+1}t^i .
$$

Its $r$ roots are simple and negative. For $r\ge2$, the same formula holds for the cycle matroid of a convex $(r+1)$-gon together with any collection of noncrossing diagonals. [Alexandersson's ribbon conjecture, item 4](https://github.com/PerAlexandersson/RealRooted/issues/2650) · [SymCat statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs)

**Deletion lemma.** Suppose a simple graph $G=H_1\cup H_2$ is a parallel connection along an edge $e=uv$. Thus the two sides meet only in $u,v,e$. Suppose both graphs $H_i-e$ are connected. Then $Z_{M(G)}=Z_{M(G-e)}$.

Write $M=M(G)$. This matroid is simple, and a path joining $u$ to $v$ in either $H_i-e$ puts $e$ on a cycle, so $e$ is a noncoloop. Braden and Vysogorets, Theorem 2.8, equation (6), express the difference as a sum over flats $F$ with $e\notin F$ and $F+e$ also a flat. Every term contains the factor $\tau(M/(F+e))$, the top allowed Kazhdan–Lusztig coefficient for odd rank, set to zero in even rank. Their proof of Theorem 3.2 establishes the vanishing of each of these factors. Put $F_i=F\cap E(H_i)$. After contracting $F+e$, the two contracted graphs meet at just the image of $u,v$. Their cycle matroids therefore form a direct sum. Each summand has positive rank. Indeed $F_i$ cannot contain every edge of $H_i-e$, as those edges connect $u$ to $v$, contrary to the flatness of $F$ and $e\notin F$. A missing edge remains a nonloop after contraction because $F+e$ is flat. Lemma 2.7 of the same paper makes $\tau$ vanish on a direct sum of two positive-rank matroids. The equivariant deletion paper of Ferroni, Matherne and Vecchi also records the corresponding vanishing. [Braden–Vysogorets, §2.4 and §3.1](https://doi.org/10.37236/9026) · [Ferroni–Matherne–Vecchi, Theorem 1.1 and §4.1.2](https://doi.org/10.1137/24M1673796)

**Polygon reduction.** Choose any diagonal. The two subpolygons meet along that edge. Their boundary arcs ensure that both sides remain connected upon its deletion. No edge crosses it. Iterating the deletion lemma leaves the boundary cycle, with the vertex set and rank fixed. The matroid of that cycle is $U_{r,r+1}$. Proudfoot, Xu and Young computed its $Z$-polynomial as $N_{r+1}$ and record the negative real interlacing roots of this family. The Jacobi expansion also gives the identity below.

$$
 N_{r+1}(t)=\frac{(1-t)^r}{r+1}P_r^{(1,1)}\left(\frac{1+t}{1-t}\right).
$$

The Jacobi polynomial has $r$ simple roots in $(-1,1)$, whose images under $x\mapsto(x-1)/(x+1)$ are strictly negative. [Proudfoot–Xu–Young, Proposition 4.9 and Example 5.3](https://doi.org/10.37236/7105) · [Jacobi expansion](https://dlmf.nist.gov/18.5.E8)

**Ribbon reduction.** For a connected lattice path matroid with at least two ground elements, the two bounding paths have no intermediate common vertex. At such a vertex the bases would split as a direct sum on the nonempty sets of step positions before and after that vertex. In the region between the paths, a lattice point is interior exactly when the four unit squares incident to it are present. A ribbon therefore has no interior lattice point and satisfies the snake hypotheses of Knauer, Martínez-Sandoval and Ramírez Alfonsín, Theorem 3.2. [Snake definition and multi-fan correspondence](https://doi.org/10.1016/j.aam.2016.11.008)

Theorem 3.2 identifies the matroid with the cycle matroid of a multi-fan. A path through $r$ vertices has a hub joined by one or more edges to selected path vertices, including both ends. In terms of the interval presentation of the ribbon, an element shared by consecutive intervals is a path edge. An element belonging to just one interval is a spoke. Parallel copies have the same incidence with every flat. Simplification therefore preserves the ranked lattice of flats, which determines $Z$. For $r\ge2$ the path, endpoint spokes and hub form a cycle through all $r+1$ vertices. All remaining spokes are noncrossing diagonals, so the preceding reduction applies.

In rank one the lattice of flats is a two-element chain and $Z=1+t=N_2$. If rank-zero degenerate ribbons are admitted, their lattice of flats has one element and $Z=1=N_1$. This includes the empty matroid and the singleton loop whenever the corresponding diagram is allowed.
