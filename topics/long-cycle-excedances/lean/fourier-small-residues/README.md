# Enclosed nonprincipal residues for cutoffs eight through ninety-nine

For $8\le k\le99$, $n\ge10000$ and $s\ge0$, let $p_j=s+(2j+1)\pi i$, $r=|p_0|$ and $S=\pi/r$. Assume $nS^2\ge1$ and $R^2\le r^2(1+2/k)$. Let $T$ be the original truncated numerator for permutations with minimum cycle length $k$, evaluated at the polynomial argument $-\exp(-s)$. For any finite set of indices $j\ge1$ with $|p_j|\le R$, define

$$
f_j=\left(\frac{r}{|p_j|}\right)^n\left|\frac{T(p_j)}{T(p_0)}\right|.
$$

The bound $f_j\le e^{-3j}$ gives $\sum_j (2j+1)f_j\le1/5$ and $\sum_j f_j\le1/15$. The two complex residue sums for the original row and its signed successor contrast then have absolute values at most $1/12$ and $S/4$, respectively. These are the two estimates required by the sign argument. [Original numerator and mass bounds](RepositorySmallCutoffResidues.lean) · [Complex sums](RepositorySmallMinorSums.lean)

Enclosing any nonprincipal pole forces $s\ge17$ and $(R/s)^{k-1}\le31/10$. For $s\le200$, the size assumption gives $nS^2\ge12/5$. For $s\ge200$, the decreasing Poisson tail gives a stronger bound on the change of the log numerator. In both ranges the radial factor absorbs this change. The estimates are uniform up to the central endpoint $s=0$, where the nonprincipal sum is empty.

## Verification

Lean 4.33.1 verified the bounds for the original permutation numerator on the research pin, including the endpoint at zero. [Proof replay and build command](verification.md) · [Independent review](review.md)
