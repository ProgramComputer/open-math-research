# Independent review of the 36-row coverage

An independent agent-derived check accepted the coverage and exact vectors. It obtained the same 28 residual keys by using only the weakest binomial-curvature index, namely the internal quota closest to 18. It checked the 15 earlier vectors against the original working checkpoint and reconciled the column-extension and defect archives with the new coverage ledger.

For quota one, the audit allocates the $d$ distinctly labeled column entries among labeled rows subject to the cap. For quota two, give each column two distinct labels and use inclusion–exclusion over events that the two labels of a column occupy the same row. At a marked column its two labels must travel as a single weighted group of size two. Every other label travels separately. A row assignment DP for these labeled groups yields the count, and division by $2^d$ removes the labels within each column. This checks 56 coefficients independently.

For each of the 28 polynomials $P$, the audit forms the coefficient matrix of the Bézout kernel
$$
\frac{P(x)P'(y)-P'(x)P(y)}{x-y}.
$$
All 617 leading principal determinants are strictly positive, so each real symmetric matrix is positive definite. A multiple root makes its evaluation vector vanish in the quadratic form. A nonreal root does so by pairing evaluation at the root with its conjugate. Positive definiteness rules out both. Positive coefficients exclude nonnegative roots. This provides a third exact root certificate independent of Sturm chains and negative-axis evaluations. The audit does not rely on a numerical root calculation.

The [independent replay](independent-audit.py) runs with Python and python-flint from the repository root. The optional source checkpoint argument was used in the independent review.

~~~sh
python3 -B topics/balanced-arrays/finite-36/independent-audit.py
~~~
