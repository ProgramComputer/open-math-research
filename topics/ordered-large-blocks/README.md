# Zeros of ordered partitions counted by large blocks

Give an ordered set partition of $[n]$ weight $t^k$ when exactly $k$ blocks have size at least $j$. Write $O_{n,j}(t)$ for the sum.

**Theorem.** For each fixed $`j\ge2`$, every sufficiently large row has only simple negative zeros and strictly interlaces its successor. The distribution of the zero moduli has an explicit limit with uniform error $`O_j(1/n)`$. For $`j=2,3,4`$, strict interlacing holds in every size. The fixed-threshold proof has an undetermined cutoff that may depend on $`j`$. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

**Reviewed partial theorem.** One eventual old-size cutoff suffices for simple negative zeros and strict consecutive interlacing at all thresholds and ranks. The cutoff is existential. Formal verification is ⬜ None. A fresh-context mathematical review checked the complete assembly. [Uniform eventual proof package](uniform-eventual/README.md)

| Threshold | Proof and verification |
|---|---|
| Two | [Proof](threshold-two.md) · [Manuscript](paper.pdf) · [Source](paper.tex) |
| Three | [Proof and finite prefix](threshold-three.md) · [Manuscript](threshold-three.pdf) · [Source](threshold-three.tex) |
| Four | [All-size proof](threshold-four-effective.md) · [Pole classification](threshold-four-eventual.md) · [Manuscript](threshold-four.pdf) · [Source](threshold-four.tex) |
| Every fixed $j\ge2$ | [Eventual strict interlacing and distribution](all-fixed-thresholds.md) · [Proof of the outer root count](fixed-threshold-outer-interface.md) · [Manuscript](all-fixed-thresholds.pdf) · [Source](all-fixed-thresholds.tex) |
| Threshold and degree both growing | [Proposed partial theorem for the smallest-modulus zeros](joint-inner-zeros.md) · [Bounded proportional window](proportional-window.md) |
| Edges at every threshold | [Sharp zero-free interval for every row](lower-spectral-edge.md) · [Strict interlacing for an initial positive fraction in sufficiently large rows](fixed-threshold-inner-zeros.md) · [Outermost complex zeros and their scales](fixed-threshold-outer-zeros.md) |

For each fixed number of outer ranks, a single old-size cutoff works for every threshold. Beyond it, those available roots are simple and negative, and the old and new outer ranks alternate strictly in the order determined by the degree step. Formal verification of this result is ⬜ None. [Uniform outer ranks, proof and independent checks](outer-ranks/README.md)

Two further joint-growth regimes give strict interlacing at growing outer ranks. The theta limit gives an explicit ratio of neighboring moduli, and the pole comparison covers larger defects when both $h/\sqrt m$ and $hj/m$ tend to infinity. Formal verification is ⬜ None. [Growing outer ranks, proofs and reviews](growing-outer-ranks/README.md)

The proposed joint-growth argument gives an interval containing a positive fraction of the smallest-modulus zeros, all simple and negative, with strict consecutive interlacing when both $j$ and $n/j$ are sufficiently large. It also gives the sharp first-zero scale. For each fixed $K$, the first $K$ ranks by modulus, or all available ranks if the degree is smaller, have this property outside a finite set of pairs $(j,n)$. The upper comparison is omitted at the last available rank if the next row has the same degree. The original all-size conjecture remains open in general. This is a proposed partial theorem under review. [Joint-growth argument](joint-inner-zeros.md) · [Research issue #1](https://github.com/ProgramComputer/open-math-research/issues/1)

**⬜ None.** The joint-growth argument and its bounded proportional-window companion have written proofs. Their new claims have no Lean or Rocq verification. The formal coverage below applies to the previously published components.

The written proof for arbitrary fixed thresholds uses a dominant conjugate pole pair. Two independent exact calculations verify all 27 polynomial inequalities needed for thresholds four through twelve. The smallest rational lower bound is $29/150$. [Bernstein certificate](results/angular-modulus.json) · [Independent verifier](code/check_angular_separation_independent.py)

For every threshold, rescaling about the sharp lower edge gives a sinc limit. Its derivatives identify the first real zeros of every fixed derivative through Bessel zeros. These general edge results have independently reviewed written arguments. [Sharp-edge manuscript](sharp-edge.pdf) · [Source](sharp-edge.tex)

At threshold two, the moduli of the zeros have an explicit limiting distribution. The smallest approach a positive limit on the $n^{-2}$ scale. The largest grow on the $n^2$ scale, with different constants in odd and even rows. [Threshold-two distribution](root-law.md) · [Threshold-three distribution and lower edge](threshold-three-root-law.md)

**🟨 Partial · Lean 4.** Lean derives the complete negative root multiset and strict order from alternating signs at the previous row’s zeros, for both possible degree changes. Lean also reduces the upper complex pole equation to a real phase equation, proves at most one pole in each permitted band, and verifies the sign shift from two residue error bounds. For threshold three, Lean verifies the quantitative pole separation, cancellation of the real residue, transfer of signs, and the floor-degree root count under their stated hypotheses. At arbitrary thresholds $j\ge4$, Lean checks the sine-weight inequality on the sector boundary, its implication for the complex numerator, and an angular derivative sign under explicit coefficient bounds. For threshold four, Lean proves the four-pole determinant identity, the margin after perturbation, and the transfer of signs under the analytic error bounds. The analytic residue estimates and the connection to the counting generating function have written proofs. [Root theorem](lean/OrderedThresholdTwoSigns.lean) · [Pole and sign theorems](lean/OrderedThresholdTwoPhase.lean) · [Three-pole theorems](lean/OrderedThresholdThreeSigns.lean) · [Angular inequalities](lean/OrderedGlobalAngular.lean) · [Four-pole sign transfer](lean/OrderedThresholdFourSigns.lean) · [Kernel report](verification.json)

[Stable Lean recheck and per-theorem axiom reports](verification.json) · [Reproduce the audit](../../shared/lean/publication/README.md)

Two coefficient recurrences agree for $0\le n\le104$. Exact Sturm counts verify all 105 rows and exact signed remainders verify all 104 consecutive pairs. A further 24 certified interval comparisons test the principal-residue estimate. [Coefficient vectors and root counts](results/threshold-two.json.gz) · [Verifier](code/threshold_two_check.py)

At threshold three, a standard-library verifier independently reconstructs 97 complete coefficient vectors, root counts, and 96 consecutive signed remainder chains. These overlap the analytic proof from row 94. Two exact methods also compare the outermost three coefficients for 105 rows at thresholds two through eight. [Three-block finite archive](results/threshold-three.json.gz) · [Outer coefficient ratios](results/outer-coefficients.json)

At threshold four, the analytic real-rootedness argument applies for $n\ge119$, and the consecutive interlacing argument applies for $n\ge199$. Three counting methods agree on all 5,151 coefficients through row 200. Independent Sturm and Sturm–Tarski calculations cover 201 rows and 200 consecutive pairs. Two certified interval computations exclude crossings of a pole boundary. [Complete exact archive](results/threshold-four-independent.jsonl.gz) · [Primary verifier](code/threshold_four_effective.py) · [Independent verifier](code/threshold_four_independent.py)

From the repository root, with Python 3.10 or later, run

~~~sh
python -m pip install python-flint==0.9.0
python -I -O topics/ordered-large-blocks/code/threshold_two_check.py
python -I -O topics/ordered-large-blocks/code/threshold_three_check.py
python -I -O topics/ordered-large-blocks/code/threshold_three_replay.py
python -I -O topics/ordered-large-blocks/code/verify_lower_spectral_edge.py
python -I -O topics/ordered-large-blocks/code/outer_coefficient_check.py
python -I -O topics/ordered-large-blocks/code/verify_angular_modulus.py
python -I -O topics/ordered-large-blocks/code/check_angular_separation_independent.py
python -I -O topics/ordered-large-blocks/code/threshold_four_effective.py
python -I -O topics/ordered-large-blocks/code/threshold_four_independent.py topics/ordered-large-blocks/results/threshold-four-independent.jsonl.gz --verify
~~~

In the [shared Lean project](../../shared/lean/README.md), run `lake build OrderedThresholdTwoSigns OrderedThresholdTwoPhase OrderedThresholdThreeSigns OrderedGlobalAngular OrderedThresholdFourSigns`.

[Production matrices and Toeplitz kernels](production-obstructions.md) records exact obstructions to a fixed transition, its canonical Riordan lift, and component-kernel total positivity.

Giving every block the same positive weight can destroy real-rootedness already in degree two. The first critical weight at size $2j$ is asymptotic to $\sqrt{\pi j}(4/9)^j/4$. [Proof and integer certificates for the weighted obstruction](block-weight/README.md)

[Finite-alphabet renewal states](finite-alphabet-states/README.md) gives a conditional interlacing update for the normalized long states and exact obstructions to extending it by a split compatibility argument.
