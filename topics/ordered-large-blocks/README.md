# Interlacing for ordered partitions counted by nonsingleton blocks

Give each ordered partition of $[n]$ weight $t^k$ when exactly $k$ of its blocks have at least two elements. Let $O_n(t)$ be the sum of the weights.

**Theorem.** Every zero of $O_n(t)$ is simple and negative, and the zeros of $O_n$ and $O_{n+1}$ strictly interlace for every $n$. This proves the threshold-two case of Alexandersson’s ordered large-block conjecture. The full conjecture allows any threshold $j\ge2$. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Proof](threshold-two.md) · [Manuscript](paper.pdf) · [LaTeX source](paper.tex)

The moduli of the zeros have an explicit limiting distribution. The smallest approach a positive limit on the $n^{-2}$ scale. The largest grow on the $n^2$ scale, with different constants in odd and even rows. [Distribution and edge formulas](root-law.md)

**🟨 Partial · Lean 4.** Lean derives the complete negative root multiset and strict order from alternating signs at the previous row’s zeros, for both possible degree changes. Lean also reduces the upper complex pole equation to a real phase equation, proves at most one pole in each permitted band, and verifies the sign shift from two residue error bounds. The contour integral, existence of the poles, and uniform error bound have independently reviewed written proofs. [Root theorem](lean/OrderedThresholdTwoSigns.lean) · [Pole and sign theorems](lean/OrderedThresholdTwoPhase.lean) · [Kernel report](verification.json)

Two coefficient recurrences agree for $0\le n\le104$. Exact Sturm counts verify all 105 rows and exact signed remainders verify all 104 consecutive pairs. A further 24 certified interval comparisons test the principal-residue estimate. [Coefficient vectors and root counts](results/threshold-two.json.gz) · [Verifier](code/threshold_two_check.py)

From the repository root, with Python 3.10 or later, run

~~~sh
python -m pip install python-flint==0.9.0
python -I -O topics/ordered-large-blocks/code/threshold_two_check.py
~~~

In the [shared Lean project](../../shared/lean/README.md), run `lake build OrderedThresholdTwoSigns OrderedThresholdTwoPhase`.
