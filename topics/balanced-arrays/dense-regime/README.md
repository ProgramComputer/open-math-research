# Simple negative zeros for balanced arrays in growing dimensions

## Logarithmic dimension bound

At three to four rows per column and every $`n\ge10^6`$, explicit disk counts isolate all but at most $`\lceil n\sqrt{\log(100n)/(2d)}\rceil+4`$ roots as simple and negative for every row cap. [Finite theorem and independent verification](below-cap/finite-aspect/README.md)

**Theorem.** There are absolute constants $C>0$ and $N$ such that, for every integer $n\ge N$, every $d\ge Cn/\log n$, and every cap $1\le r\le d$, the balanced-array polynomial has exactly $\lfloor nr/d\rfloor$ simple negative zeros. The constants are unspecified.

The coefficient of $q^k$ counts labeled binary $n\times d$ matrices with every column sum $k$ and every row sum at most $r$. This extends the earlier theorem for $d\ge\epsilon n$ with fixed $\epsilon>0$. The general all-row conjecture and consecutive interlacing are outside the theorem's scope. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Prior literature record](literature.md) · [Literature check for the logarithmic range](sublinear-literature.md)

## Proof and verification

- [Logarithmic-dimension proof](logarithmic-window.md) gives the quantitative sign argument.
- [Summation over row margins](quantitative-margins.md), [fixed-margin enumeration](sparse-enumeration.md), and the [uniform lattice local limit estimate](uniform-lattice-lemma.md) provide the quantitative estimates.
- [Earlier linear-dimension proof](proof.md), [central estimate](central.md), [saturated endpoint](saturated.md), and its [independent blind review](review.md) record the preceding theorem and its verification.
- [Independent blind review of the logarithmic bound](logarithmic-review.md) records the agent-assisted check and the corrections to the source attribution and full-cap corollary.
- [Manuscript](paper.pdf) · [LaTeX source](paper.tex). Build from this folder with `tectonic paper.tex`.

**⬜ None.** The theorem has no checked Lean or Rocq proof.

## Roots below the row cap

A uniform bound leaves at most $CD\sqrt{n\log(n+1)}/d$ zeros uncertified as simple and negative for $2\le d\le n$ and every cap, with $D=\lfloor nr/d\rfloor$ and an unspecified absolute constant $C$. Thus the certified fraction tends to one when $d\gg\sqrt{n\log(n+1)}$. The comparison isolates individual roots using disks about the unrestricted binomial-power roots. **⬜ None** for Lean or Rocq. [Below-cap theorem, proof and verification](below-cap/README.md)

## Rank-dependent dimension bound

A reviewed all-root theorem applies when $d\ge C_\varepsilon\sqrt{nr/\log n}$ and either $r\le n^{1/5-\varepsilon}$ or $d\ge n^{3/4+\varepsilon}$, for each fixed $0<\varepsilon<1/5$ and all sufficiently large $n$. It gives all simple negative zeros down to order $\sqrt{n/\log n}$ for fixed caps. **⬜ None** for Lean or Rocq. [Rank-dependent theorem, proof and verification](rank-dependent/README.md)
