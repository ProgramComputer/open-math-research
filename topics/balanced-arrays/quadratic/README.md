# A quadratic row bound for balanced arrays

**Partial theorem.** There is an absolute constant $C>0$ such that for every $d\ge2$, every $1\le r\le d$, and every $n\ge Cd^2$, the balanced-array polynomial has exactly $\lfloor nr/d\rfloor$ simple, strictly negative zeros. The coefficient of $q^k$ counts labeled binary arrays with $n$ rows, $d$ columns of sum $k$, and every row sum at most $r$. The cutoff constant is existential. At $d=1$, the polynomial is $(1+q)^n$, with a zero of multiplicity $n$ for $n\ge1$. Per Alexandersson's conjecture asks for real-rootedness throughout the parameter range. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**Corollary.** There are existential absolute constants $c>0$ and $N$ such that for all $n\ge N$, these simple negative zeros occur in every dimension $d\ge2$ for every $1\le r\le\min(d,c\log n)$. This combines the quadratic bound with the previously proved rank-dependent dimension bound. [Rank-dependent theorem](https://github.com/ProgramComputer/open-math-research/tree/ba7ddfd7efb37cac33769f4fdfed749e1b5bf58a/topics/balanced-arrays/dense-regime/rank-dependent)

**Independent review.** An agent-assisted blind review accepted the theorem and corollary. [Referee report and editorial follow-up](review.md)

**Formal verification.** ⬜ None.

## Proof and supporting estimates

- [Main proof](proof.md)

- [Lower quota coefficient estimates](quadratic-lower-quota.md)
- [Interior angular integrals at the quadratic row scale](very-tall-quadratic-interior-saddle.md)
- [Angular signs near saturation](near-full-all-angular-signs.md)
- [Related results and literature screen](literature.md)
- [Manuscript PDF](paper.pdf) and [LaTeX source](paper.tex)

The earlier [quartic-log row bound](https://github.com/ProgramComputer/open-math-research/tree/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall) and [dimension-uniform bound for fixed cap](https://github.com/ProgramComputer/open-math-research/tree/f7e10f84dd21fec44ca58c60bae0879d12ebd89b/topics/balanced-arrays/fixed-cap) remain separately available.

Build the manuscript from this directory with `tectonic paper.tex`.
