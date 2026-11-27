# A single eventual size for all ordered-block thresholds

**Reviewed partial theorem.** Let $`O_{n,j}(t)`$ weight every ordered partition of $`[n]`$ by $`t`$ for each block of size at least $`j`$. There is one old-size cutoff $`N`$ such that for every $`n\ge N`$ and $`j\ge2`$, both consecutive rows have simple negative zeros and strictly alternate. In increasing modulus the next row supplies the first root. When the degree stays fixed the old row supplies the last root, and at a carry the next row supplies it. The cutoff is existential. Formal verification is ⬜ None. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Research issue #1](https://github.com/ProgramComputer/open-math-research/issues/1)

The [uniform assembly](assembly.md) exhausts all possible sequences of failing ranks. The new [sparse two-term proof](sparse.md) preserves the signed coefficient difference even when the matching zeros are closer than the individual root errors. The new [bounded-radius dense proof](dense.md) matches the two contours by their actual physical residues, which fixes the integer ranks through the overlap. The earlier [theta and moving-pole proofs](../growing-outer-ranks/README.md) supply the other growing-rank cases. [Sparse-arm review](review-sparse.md) · [Dense-arm and assembly review](review-dense.md)

The [explicit growing-degree theorem](../effective-degree/README.md) gives a numerical threshold in terms of the old degree.

[Source and scope comparison](literature.md)

[Fresh-context independent review of the complete assembly](review-assembly.md)

[Manuscript source](paper.tex) · [Compiled manuscript](paper.pdf)

From this directory, build with Tectonic 0.17.0.

~~~sh
SOURCE_DATE_EPOCH=1795651200 tectonic paper.tex
~~~
