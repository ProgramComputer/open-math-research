# A five-thirds row bound for balanced arrays

**Partial theorem.** There is an absolute constant $C>0$ such that, for every $d\ge2$, every $1\le r\le d$, and every $n\ge Cd^{5/3}$, the balanced-array polynomial has exactly $\lfloor nr/d\rfloor$ simple, strictly negative zeros. Its coefficient of $q^k$ counts labeled binary $n\times d$ arrays with common column sum $k$ and every row sum at most $r$.

**Corollary.** There are absolute constants $c>0$ and $N$ such that for every $n\ge N$, every $d\ge2$, and every admissible cap with $\min(r,d-r)\le c n^{1/5}$, the same conclusion holds. The constants are existential. For $d=1$ the polynomial is $(1+q)^n$. The all-parameter conjecture remains open. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**Independent review.** An agent-assisted blind review accepted both claims. [Referee report and editorial follow-up](review.md)

**Formal verification.** ⬜ None. There is no Lean or Rocq proof of these claims.

## Proof and supporting estimates

- [Main proof](proof.md)

- [Fifth-order saddle remainder and integrated estimates](subquadratic-interior-saddle.md)
- [Angular signs at internal phase levels](subquadratic-angular-nodes.md)
- [Upper quota signs when corank is on the subquadratic scale](subquadratic-scaling-corank-upper.md)
- [Lower quota comparison](fifth-thirds-lower-quota.md)
- [Transfer at small corank](small-corank-subquadratic.md)
- [Geometric signs when degree divided by dimension is bounded](small-cap-bounded-degree-ratio.md)
- [Prior results and literature screen](literature.md)
- [Manuscript PDF](paper.pdf) and [LaTeX source](paper.tex)

The [critical quadratic-aspect theorem](https://github.com/ProgramComputer/open-math-research/tree/605cc467a5be93a8408519da331e46f1008df96e/topics/balanced-arrays/critical-aspect) remains available separately.

Build the manuscript from this directory with `tectonic paper.tex`.
