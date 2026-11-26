# Simple negative zeros for very tall balanced arrays

**Partial theorem.** There is an absolute constant $C>0$ such that, for every $d\ge2$, every $1\le r\le d$, and every $n\ge Cd^4\log(d+1)$, the polynomial counting labeled binary arrays of size $n$ by $d$ with row cap $r$ by their common column sum has exactly $\lfloor nr/d\rfloor$ simple, strictly negative zeros. The constant is existential. Any counterexample to real-rootedness must lie below this cutoff. The original conjecture remains open. Per Alexandersson's conjecture asks for real-rootedness for all row counts, caps, and dimensions. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**Independent review.** An agent-assisted blind review accepted the proof. [Referee report and editorial follow-up](review.md)

**Formal verification.** ⬜ None.

## Proof and supporting estimates

- [Main proof](proof.md)

- [Nearly empty rows and lower-quota coefficients](very-tall-nearly-empty.md)
- [Upper-quota coefficient comparison and saturation](very-tall-upper-quota.md)
- [Interior saddle analysis with appreciable distance from saturation](very-tall-interior-saddle.md)
- [Two-saddle approximation near saturation](growing-cap-upper-saddle.md)
- [Related results and literature screen](literature.md)
- [Manuscript PDF](paper.pdf) and [LaTeX source](paper.tex)

Build the manuscript from this directory with `tectonic paper.tex`.
