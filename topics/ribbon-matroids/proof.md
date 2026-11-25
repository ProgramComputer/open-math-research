# The ribbon matroid conjecture

**Theorem.** For every connected ribbon lattice path matroid of rank $r$,
$$
 Z_M(t)=N_{r+1}(t)=\sum_{i=0}^r\frac{1}{r+1}\binom{r+1}{i}\binom{r+1}{i+1}t^i .
$$
The same formula holds for the cycle matroid of a convex $(r+1)$-gon together with any collection of noncrossing diagonals. Its $r$ roots are simple and negative.

**Deletion lemma.** Suppose a simple graph $G=H_1\cup H_2$ is a parallel connection along an edge $e=uv$. Thus the two sides meet only in $u,v,e$. Suppose both $H_i-e$ are connected. Then $Z_{M(G)}=Z_{M(G-e)}$.

Write $M=M(G)$. The edge is a noncoloop. Braden and Vysogorets, Theorem 2.8, equation (6), express the difference as a sum over flats $F$ with $e\notin F$ and $F+e$ also a flat. Every term contains the factor $\tau(M/(F+e))$, the top allowed Kazhdan–Lusztig coefficient for odd rank, set to zero in even rank. Their proof of Theorem 3.2 establishes the vanishing of each of these factors. Here is the argument for this application. Put $F_i=F\cap E(H_i)$. After contracting $F+e$, the two contracted graphs meet at just the image of $u,v$. Their cycle matroids therefore form a direct sum. Each summand has positive rank. Indeed $F_i$ cannot contain every edge of $H_i-e$, as those edges connect $u$ to $v$, contrary to the flatness of $F$ and $e\notin F$. A missing edge remains a nonloop after contraction because $F+e$ is flat. Lemma 2.7 of the same paper makes $\tau$ vanish on a direct sum of two positive-rank matroids. This proves the deletion lemma. The equivariant deletion paper of Ferroni, Matherne and Vecchi also records the corresponding vanishing. [Braden–Vysogorets, §2.4 and §3.1](https://arxiv.org/pdf/1909.09888) · [Ferroni–Matherne–Vecchi, Theorem 1.1 and §4.1.2](https://arxiv.org/pdf/2406.19962)

**Polygon reduction.** Choose any diagonal. The two subpolygons meet along that edge. Their boundary arcs ensure that both sides remain connected upon its deletion. No edge crosses it. Iterating the deletion lemma leaves the boundary cycle, with the vertex set and rank fixed. The matroid of that cycle is $U_{r,r+1}$. Proudfoot, Xu and Young computed its $Z$-polynomial as $N_{r+1}$. They also record the negative real interlacing roots of this family. Alternatively
$$
 N_{r+1}(t)=\frac{(1-t)^r}{r+1}P_r^{(1,1)}\!\left(\frac{1+t}{1-t}\right).
$$
The Jacobi polynomial has $r$ simple roots in $(-1,1)$, whose images under $x\mapsto(x-1)/(x+1)$ are strictly negative. [Proudfoot–Xu–Young, Proposition 4.9 and Example 5.3](https://arxiv.org/pdf/1706.05575) · [Jacobi expansion](https://dlmf.nist.gov/18.5.E8)

**Ribbon reduction.** The connected ribbon lattice path matroids are the snake matroids. Knauer, Martínez-Sandoval and Ramírez Alfonsín, Theorem 3.2, identify them with cycle matroids of multi-fans. In this presentation there is a path through $r$ vertices, and a hub joined by one or more edges to selected path vertices, including both ends. In terms of the interval presentation of the ribbon, an element shared by consecutive intervals is a path edge. An element belonging to just one interval is a spoke. Parallel copies have the same incidence with every flat. Simplification therefore preserves the ranked lattice of flats, which determines $Z$. For $r\ge2$ the simple path, its two endpoint spokes and the hub form a cycle through all $r+1$ vertices. All remaining spokes are noncrossing diagonals of this polygon. The preceding reduction applies. In rank one the lattice of flats is a two-element chain and $Z=1+t=N_2$. This proves the stated conjecture. [Knauer–Martínez-Sandoval–Ramírez Alfonsín, Theorem 3.2](https://arxiv.org/pdf/1510.00600) · [SymCat statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs)
