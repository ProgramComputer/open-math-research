# Simple negative zeros for balanced arrays with a logarithmic dimension bound

**Theorem.** There are absolute constants $C>0$ and $N$ such that, for every integer $n\ge N$, every $d\ge Cn/\log n$, and every cap $1\le r\le d$, the balanced-array polynomial has exactly $\lfloor nr/d\rfloor$ simple negative zeros. The constants are unspecified.

The coefficient of $q^k$ counts labeled binary $n\times d$ matrices with every column sum $k$ and every row sum at most $r$. This extends the earlier theorem for $d\ge\epsilon n$ with fixed $\epsilon>0$. The general all-row conjecture and consecutive interlacing are outside the theorem's scope. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Prior literature record](literature.md) · [Literature check for the logarithmic range](sublinear-literature.md)

## Proof and verification

- [Logarithmic-dimension proof](logarithmic-window.md) gives the quantitative sign argument.
- [Summation over row margins](quantitative-margins.md), [fixed-margin enumeration](sparse-enumeration.md), and the [uniform lattice local limit estimate](uniform-lattice-lemma.md) provide the quantitative estimates.
- [Earlier linear-dimension proof](proof.md), [central estimate](central.md), [saturated endpoint](saturated.md), and its [independent blind review](review.md) record the preceding theorem and its verification.
- [Independent blind review of the logarithmic bound](logarithmic-review.md) records the agent-assisted check and the corrections to the source attribution and full-cap corollary.
- [Manuscript](paper.pdf) · [LaTeX source](paper.tex). Build from this folder with `tectonic paper.tex`.

**⬜ None.** The theorem has no checked Lean or Rocq proof.
