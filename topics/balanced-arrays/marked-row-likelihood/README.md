# How a column-quota increase changes one row

**Marked-row likelihood theorem.** Take any weighted binary array model with fixed labeled column sums and interval constraints on all unmarked rows. Raising every column sum by one increases the relative likelihood of larger marked-row sizes by an explicit factor. If $`F_{\boldsymbol q}(j)`$ is the weight of arrays with marked size $`j`$, then for $`s<t`$,

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

At $`n=1000000`$, $`d=250000`$ and $`r=127000`$, the comparison also gives a proof that all 508,000 roots are simple and negative. It combines a concentration bound for the overlap in each column with the previously reviewed one-dimensional phase estimates. [Finite proof](finite.md) · [Concentration replay](finite-output.txt) · [Exact-odds replay](exact-odds-output.txt) · [Earlier reviewed proof](../dense-regime/below-cap/finite-aspect/marked-row/complete-instance/README.md)

A separate result couples the entire marked row by inclusion conditional on adjacent sizes when the other row caps are at most three. [Reduction to Chan’s orientation lemma](coupling.md)

**Formal verification**　🟨 Partial · Lean 4 checks the array–orientation bijection for a fixed pairing, its row degrees and column margins, the number of refinements of an array pair, and the local pairing and overlap calculations. The full root claim has no checked Lean or Rocq proof. [Formal declarations and verification record](lean/README.md)

Two independent agent-assisted reviews cover the likelihood theorems and the million-row sign argument. The finite review replayed both sets of 1,435 sign checks. Both finite arguments use the same inner and outer endpoint signs. [Mathematical review](review.md) · [Finite certificate review](finite-review.md) · [Source record and scope](literature.md)

Run the following from this directory using Python 3.10 or later and its standard library. The [recorded small-instance run](small-output.txt) checks 22,665 coefficientwise-tilt evaluations, 153,012 exact binomial-odds comparisons, 1,260 individual cell monomials, 10,586 couplings and 231 independently counted coefficient vectors. The first checker enumerates weighted fibers, tests the likelihood comparisons, constructs exact couplings for the small-cap cases and cross-checks balanced coefficients using the row and column counters. Its [compressed JSON record](checks.json.gz) gives the weight vectors indexed by marked bit mask for each feasible margin vector and the full balanced coefficient vectors. The second checker replays the million-row calculation from [rational tilt witnesses](finite-tilts.json). The optional flag `--make-tilts` regenerates those witnesses by proposing trial values and checking them with rational arithmetic.

~~~sh
python3 -IB verify.py
python3 -IB verify-finite.py
python3 -IB verify-finite.py --exact-odds
~~~
