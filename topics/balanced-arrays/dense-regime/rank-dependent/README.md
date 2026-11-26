# Simple negative zeros at a rank-dependent dimension bound

Each coefficient of the balanced-array polynomial counts labeled binary $n\times d$ matrices with every column sum equal to the exponent and every row sum at most $r$. This result addresses a growing-dimension range of Per Alexandersson’s balanced-array conjecture. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Source and literature record](literature.md)

**Theorem.** Fix $0<\varepsilon<1/5$. There are constants $C_\varepsilon>0$ and $N_\varepsilon\ge3$ such that, for $n\ge N_\varepsilon$ and $1\le r\le d$, the polynomial has exactly $D=\lfloor nr/d\rfloor$ simple negative zeros if

$$
d\ge C_\varepsilon\sqrt{\frac{nr}{\log n}}
\quad\text{and}\quad
\left(r\le n^{1/5-\varepsilon}\ \text{or}\ d\ge n^{3/4+\varepsilon}\right).
$$

In particular, for a fixed cap the theorem covers all sufficiently large $n$ and $d\ge C_r\sqrt{n/\log n}$. The constants are existential. Consecutive interlacing is a separate question.

- [Proof](proof.md) reduces the alternating sign test to the local curvature of a capped-binomial saddle.
- [Small-rank margins](small-rank-margins.md) apply Greenhill, McKay and Wang. [Large-dimension margins](large-dimension-margins.md) apply Liebenau and Wormald.
- [Small-variance lattice estimate](small-variance.md) complements the [large-variance estimate](../uniform-lattice-lemma.md).
- [Manuscript](paper.pdf) · [LaTeX source](paper.tex). Build here with `tectonic paper.tex`.

**⬜ None.** No Lean or Rocq proof is recorded. An [independent blind review](review.md) checked the argument against the original conjecture and found no substantive gap.
