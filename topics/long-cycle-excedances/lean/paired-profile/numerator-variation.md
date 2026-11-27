# Cutoff numerator coefficient bounds

For a cutoff $k\ge2$, let $d_s$ be the probability that a permutation of size $s$ has all cycles of length at least $k$. Let $\widetilde d_s=d_s$ for $s\ge k$ and zero for $s\lt k$. The existing formal cycle factor has coefficients $d_s$, including $d_0=1$. Its numerator $(D_k-1)(1-u)$ has coefficient $b_s=\widetilde d_s-\widetilde d_{s-1}$, with natural subtraction in degree zero. [Literal coefficient identification](RepositoryNumeratorVariation.lean)

The formal Euler derivative of the existing cutoff exponential gives the same recurrence as the anchored permutation probabilities. Strong induction identifies the coefficients, and multiplication by $1-u$ gives the stated difference formula. [Formal recurrence and uniqueness](CutoffCycleSeriesRecurrence.lean) · [Original probability specification](../probability-bands/RepositoryProbabilityBands.lean)

The atom is $b_k=1/k$. In the open first block $k\lt s\lt 2k$, the signed value is $-1/(s(s-1))$, so the variation sums to $1/k-1/(2k-1)$. At the endpoint,

$$
b_{2k}=\frac{1/k-1/(2k-1)}{2k},\qquad 0<b_{2k}<\frac{1}{4k^2}.
$$

For every integer $j\ge2$ and $jk\lt s\le(j+1)k$,

$$
|b_s|\le\frac{1}{2j!k^2}.
$$

In the second block the adjacent probability recurrence bounds $s|b_s|$ by the width of the reciprocal probability interval. Beyond that, the recurrence gives a telescoping sum of $k-1$ previous differences. Each lag belongs to the preceding block or to the current block at a smaller degree. Strong induction controls both groups with the preceding block bound. Dividing by $s\gt jk$ supplies the factor $j$. [Lean bounds](CycleNumeratorVariation.lean) · [Written degree-block proof](../../degree-blocks/README.md)

The [paired-profile driver](check.py) reuses the pinned probability and reciprocal-bound sources and checks the three modules above. These results provide the numerator input to the occupied-degree estimates.
