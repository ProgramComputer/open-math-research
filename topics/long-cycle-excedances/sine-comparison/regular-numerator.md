# The regular numerator error

Fix an interval $\ell\le n/k\le X$ from the nine-slab comparison, with $n\ge10000$, $S=\sin\theta>0$, and $nS^2\ge6/5$. The numerator difference at degree $s=n+1-t$ multiplies the coefficient of degree $t$ in the occupied product. Write $b_s$ for that difference in the original permutation probabilities. This estimate sums the scaled absolute error from every $s>k$ and every signed pole, including both principal poles. [Finite adjacent identity](../lean/paired-profile/FiniteAdjacentResidues.lean) · [Original-enumerator theorem](../lean/paired-profile/RepositoryRegularCost.lean)

Let $b$ be the sum of the quarter-cutoff bins of the factors in a term of degree $t$. On the support, $4t\le kb\le5t$. Put $j=\max(0,\ell-\lceil b/4\rceil)$. Then $jk\le n-t<s$. In particular, when $\ell-b/4$ is an integer, $s$ is strictly above that block boundary. Use $\kappa_b=1/(2j!)$ for $j\ge2$ and $\kappa_b=1$ for $j<2$. The factorial difference bound and the first-block bound give $k^2|b_s|\le\kappa_b$.

The earlier bound used the preceding block at a positive integral boundary. The strict shift improves the estimate in precisely those bins. Also $s>k$ gives $t+k\le n$, so $b+5\le5X$. [Block endpoints and factorial estimate](../lean/paired-profile/RegularNumeratorBin.lean) · [Single-pole bound](../lean/paired-profile/RegularValueCost.lean)

Set $c_b=\max(1/X,1-b/(4\ell))/160$, $A_0=\lfloor4\sqrt{12000}/X\rfloor/4$, and $W_c(p)=(1+c(p^2-1))^{-96}$. The modulus of the pole factor at odd index $p$ is bounded by $W_{c_b}(p)$, and $kS\ge A_0$. The finite cost for every set of poles is at most

$$
\frac{1}{A_0}\sum_{b=0}^{5(X-1)}\kappa_b \frac{q_b}{2^{56}}
\left(2\sum_{i=0}^{31}W_{c_b}(2i+1)
+\frac{1}{190c_b\cdot63 (1+c_b(63^2-1))^{95}}\right).
$$

Here $q_b$ satisfies the rounded integer product recurrence. The parenthesized expression bounds the zeroth moment of both signs of every odd pole. The tail estimate starts beyond absolute index 63. The bound applies to the whole degree sum at each finite window, so a bin is charged once per pole. [Signed mass tail](../lean/sine-comparison/SignedStarEnvelope.lean) · [Weighted degree and bin sum](../lean/paired-profile/FiniteWeightedBinCost.lean)

Two exact evaluations, one using the Lean evaluator's product coefficients, yielded the same ceilings. In millionths, the upper bounds for the first three intervals improve from 14,284, 4,248 and 263 to 6,068, 2,565 and 198 respectively. The other six ceilings agree at this precision. This refinement leaves the uniform nine-interval minimum of the previously reviewed determinant comparison at the same reported precision. [Exact rational replay](check-regular.py) · [All nine comparisons](regular-output.txt) · [Earlier determinant comparison](uniform-carrier.md)

Local Lean 4.19 checked the analytic reduction for every sequence satisfying the original probability recurrence, with the standard axiom set. The production wrapper specializes the reduction to the permutation enumerator. The numerical ceilings were evaluated in exact Python. The isolated numerator at $s=k$ requires a separate estimate. [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)
