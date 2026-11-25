# Zeros of ordered partitions counted by large blocks

Give an ordered set partition of $[n]$ weight $t^k$ when exactly $k$ blocks have size at least $j$. Write $O_{n,j}(t)$ for the sum.

**Theorem.** For $j=2$ and $j=3$, every zero is simple and negative in every size and consecutive rows strictly interlace. At threshold three, a linear combination of consecutive rows cancels a competing real pole. The full conjecture allows arbitrary $j\ge2$. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

| Threshold | Proof and verification |
|---|---|
| Two | [Proof](threshold-two.md) · [Manuscript](paper.pdf) · [Source](paper.tex) |
| Three | [Proof and finite prefix](threshold-three.md) · [Manuscript](threshold-three.pdf) · [Source](threshold-three.tex) |
| Every fixed $j\ge2$ | [Sharp zero-free interval for every row](lower-spectral-edge.md) · [Strict interlacing for an initial positive fraction in sufficiently large rows](fixed-threshold-inner-zeros.md) · [Outermost complex zeros and their scales](fixed-threshold-outer-zeros.md) |

For every threshold, rescaling about the sharp lower edge gives a sinc limit. Its derivatives identify the first real zeros of every fixed derivative through Bessel zeros. These general edge results have independently reviewed written arguments. [Sharp-edge manuscript](sharp-edge.pdf) · [Source](sharp-edge.tex)

At threshold two, the moduli of the zeros have an explicit limiting distribution. The smallest approach a positive limit on the $n^{-2}$ scale. The largest grow on the $n^2$ scale, with different constants in odd and even rows. [Threshold-two distribution](root-law.md) · [Threshold-three distribution and lower edge](threshold-three-root-law.md)

**🟨 Partial · Lean 4.** Lean derives the complete negative root multiset and strict order from alternating signs at the previous row’s zeros, for both possible degree changes. Lean also reduces the upper complex pole equation to a real phase equation, proves at most one pole in each permitted band, and verifies the sign shift from two residue error bounds. For threshold three, Lean verifies the quantitative pole separation, cancellation of the real residue, transfer of signs, and the floor-degree root count under their stated hypotheses. The analytic residue estimates and the connection to the counting generating function have written proofs. [Root theorem](lean/OrderedThresholdTwoSigns.lean) · [Pole and sign theorems](lean/OrderedThresholdTwoPhase.lean) · [Three-pole theorems](lean/OrderedThresholdThreeSigns.lean) · [Kernel report](verification.json)

Two coefficient recurrences agree for $0\le n\le104$. Exact Sturm counts verify all 105 rows and exact signed remainders verify all 104 consecutive pairs. A further 24 certified interval comparisons test the principal-residue estimate. [Coefficient vectors and root counts](results/threshold-two.json.gz) · [Verifier](code/threshold_two_check.py)

At threshold three, a standard-library verifier independently reconstructs 97 complete coefficient vectors, root counts, and 96 consecutive signed remainder chains. These overlap the analytic proof from row 94. Two exact methods also compare the outermost three coefficients for 105 rows at thresholds two through eight. [Three-block finite archive](results/threshold-three.json.gz) · [Outer coefficient ratios](results/outer-coefficients.json)

From the repository root, with Python 3.10 or later, run

~~~sh
python -m pip install python-flint==0.9.0
python -I -O topics/ordered-large-blocks/code/threshold_two_check.py
python -I -O topics/ordered-large-blocks/code/threshold_three_check.py
python -I -O topics/ordered-large-blocks/code/threshold_three_replay.py
python -I -O topics/ordered-large-blocks/code/verify_lower_spectral_edge.py
python -I -O topics/ordered-large-blocks/code/outer_coefficient_check.py
~~~

In the [shared Lean project](../../shared/lean/README.md), run `lake build OrderedThresholdTwoSigns OrderedThresholdTwoPhase OrderedThresholdThreeSigns`.
