# Ordinary descents of permutations with long cycles

For permutations of size $n\ge25$ whose cycles all have lengths at least $k$, with $52\log n\le k\le n$, the ordinary descent polynomial has degree $n-2$ and simple nonpositive zeros. The same statement holds for any nonzero nonnegative mixture of the allowed cycle types. Here a descent compares consecutive positions in one-line notation. The logarithm is natural.

For a single cycle the descent polynomial is real-rooted in every size. Its only repeated root occurs at size five, where the polynomial is $6t(t+1)^2$. The argument uses the Gessel–Reutenauer necklace enumeration, a disk bound for its polynomial input, and a differential operator that preserves simple roots after factoring out a cubic. The general conjecture for fixed minimum lengths of at least three remains open. [Complete paper](paper.pdf) · [LaTeX source](paper.tex) · [Original question](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsPermutations)

**Verification.** The long-cycle-length bound is analytic. The proof for single cycles uses exact checks in sizes 1 through 79. A second implementation computes the coefficients from the primitive-word period recursion and counts sign changes using only Python integers. It handles the double root at size five separately. Run from this folder.

~~~sh
python3 -I -O verify_single_cycles.py --check-archive results/cycle_research_single.jsonl
~~~

The proof and the exceptional case were independently reviewed within the project with GPT-6.2 Sol assistance. The literature comparison in the manuscript credits the existing weighted Euler transform results. External peer review and a Lean or Rocq proof of these theorems are outstanding. [Standalone verification source](verify_single_cycles.py) · [All 79 rows and Sturm reports](results/cycle_research_single.jsonl)
