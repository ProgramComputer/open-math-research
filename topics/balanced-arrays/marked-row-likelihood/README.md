# How a column-quota increase changes one row

**Proposed theorem.** Take any weighted binary array model with fixed labeled column sums and interval constraints on all unmarked rows. Raising every column sum by one increases the relative likelihood of larger marked-row sizes by an explicit factor. If $`F_{\boldsymbol q}(j)`$ is the weight of arrays with marked size $`j`$, then for $`s<t`$,

$$
F_{\boldsymbol q}(s)F_{\boldsymbol q+\mathbf1}(t)
\ge (1+1/K)^{t-s}F_{\boldsymbol q}(t)F_{\boldsymbol q+\mathbf1}(s),
$$

where $`K`$ is any positive integer at least $`\max_j\min(q_j,n-q_j-1)`$ and $`q_j<n`$. The comparison holds coefficientwise in all cell weights. For every positive $`K`$ and every exponent, a cell monomial attains the factor exactly. The proof weights the possible partners of each auxiliary cell in a pair of arrays. [Manuscript](paper.pdf) · [LaTeX source](paper.tex) · [Mathematical argument](likelihood.md)

With exchangeable unmarked rows, a second pairing gives the exact unrestricted binomial odds as a likelihood-ratio lower bound for any two comparable margin vectors. With unrestricted rows and equal column margins, the bound is attained. [Exact-odds theorem and proof](binomial-odds.md)

For balanced arrays with any $`2\le r<d`$, every root is simple and negative whenever

$$
\left(1+\frac{d}{n(r-1)+d}\right)^d>4.
$$

For each fixed cap this crosses the factor-four threshold on an infinite range where the unrestricted binomial comparison alone falls short. At $`n=10000`$ the test applies to $`(r,d)=(2,130),(3,190),(4,220),(12,395)`$. [Proof of the criterion](curvature.md) · [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

At $`n=1000000`$, $`d=250000`$ and $`r=127000`$, the comparison also yields a second proposed proof that all 508,000 roots are simple and negative. It combines a concentration bound for the overlap in each column with the previously reviewed one-dimensional phase estimates. [Finite proof](finite.md) · [Concentration replay](finite-output.txt) · [Exact-odds replay](exact-odds-output.txt) · [First proposed proof, PR #184](https://github.com/ProgramComputer/open-math-research/pull/184)

A separate result couples the entire marked row by inclusion conditional on adjacent sizes when the other row caps are at most three. [Reduction to Chan’s orientation lemma](coupling.md)

**Formal verification**　🟨 Partial · Lean 4 for the pairing and overlap calculations. Ten theorems passed the axiom audit. The graph-orientation reduction and the root conclusions remain outside the formal proof. [Lean declarations, pins, commands and coverage](lean/README.md) The million-row sign certificate awaits independent mathematical review. The two finite arguments share the previously reviewed inner and outer signs. [Source record and scope](literature.md)

Run the following from this directory using Python 3.10 or later and its standard library. The [recorded small-instance run](small-output.txt) checks 22,665 coefficientwise-tilt evaluations, 153,012 exact binomial-odds comparisons, 1,260 individual cell monomials, 10,586 couplings and 231 independently counted coefficient vectors. The first checker enumerates weighted fibers, tests the likelihood comparisons, constructs exact couplings for the small-cap cases and cross-checks balanced coefficients using the row and column counters. Its [compressed JSON record](checks.json.gz) gives the weight vectors indexed by marked bit mask for each feasible margin vector and the full balanced coefficient vectors. The second checker replays the million-row calculation from [rational tilt witnesses](finite-tilts.json). The optional flag `--make-tilts` regenerates those witnesses by proposing trial values and checking them with rational arithmetic.

~~~sh
python3 -IB verify.py
python3 -IB verify-finite.py
python3 -IB verify-finite.py --exact-odds
~~~
