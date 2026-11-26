# Simple negative zeros at every fixed quadratic aspect

**Partial theorem.** For each $\alpha>0$ there is an $N_\alpha$ such that every $n\ge N_\alpha$ and $d\ge2$ with $n\ge\alpha d^2$ gives exactly $\lfloor nr/d\rfloor$ simple, strictly negative zeros for every row cap $1\le r\le d$. The polynomial counts labeled binary $n\times d$ arrays by their common column sum with all row sums at most $r$. For $d=1$ the polynomial is $(1+q)^n$.

**Corollary.** For each fixed $M>0$ there is an $N_M$ such that at every $n\ge N_M$ the same root conclusion holds in every dimension $d\ge2$ for $1\le r\le\min(d,M\log n)$. The thresholds are existential. In any infinite sequence of distinct counterexamples to the original real-rootedness conjecture, $d/\sqrt n$ and $r/\log n$ must both tend to infinity. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**Independent review.** An agent-assisted blind review accepted the theorem and corollary. [Referee report and editorial follow-up](review.md)

**Formal verification.** ⬜ None. There is no Lean or Rocq proof of these claims.

## Proof and supporting estimates

- [Main proof](proof.md)

- [Angular signs for diverging transverse row mass](critical-aspect-angular-nodes.md)
- [Fourth transverse cumulant](fourth-transverse-cumulant.md)
- [Upper signs at fixed corank](fixed-corank-critical-upper.md)
- [Prior results and literature screen](literature.md)
- [Manuscript PDF](paper.pdf) and [LaTeX source](paper.tex)

The [quadratic theorem at an absolute aspect constant](https://github.com/ProgramComputer/open-math-research/tree/4fb624ba937a8eecc1361a6066185cd81ab7b172/topics/balanced-arrays/quadratic) remains available separately.

Build the manuscript from this directory with `tectonic paper.tex`.
