# The nonprincipal value error in the adjacent determinant

Fix an aspect interval $\ell\le n/k\le X$ from the nine-slab comparison, with $n\ge10000$, $S=\sin\theta>0$ and $nS^2\ge6/5$. In the finite occupied-pole expansion of the two original rows, take the absolute values of all value terms at poles other than the two principal ones. Multiply their sum by $k/S$. This entire error is bounded by a finite sum with at most 236 bin coefficients. The bound holds uniformly in the finite set of poles. [Original-enumerator theorem](../lean/paired-profile/RepositoryNonprincipalCost.lean) · [Adjacent coefficient identity](../lean/paired-profile/FiniteAdjacentResidues.lean)

**The value multiplier.** Write $a=2q+1$ for the odd pole index and $w_a=\cos\theta+iaS$. For every real $v$,

$$
w_a\sin(v+\theta)-\sin v=S\bigl(\cos(v+\theta)+ia\sin(v+\theta)\bigr).
$$

The modulus is at most $S|a|$. Let $t$ be the degree of the occupied factors and $b$ the sum of their individual quarter-cutoff bins. These satisfy $4t\le kb\le5t$. A nonzero probability weight requires $n-t\ge k$, so $b+5\le5X$. At the largest upper aspect $X=48$, this gives $b\le235$. Define $y_b=\max(1/X,1-b/(4\ell))$ and $c_b=y_b/160$. On the joint support, $(n+1-t)/n\ge y_b$, and the angle bound gives

$$
|w_a^{-1}|^{n+1-t}\le (1+c_b(a^2-1))^{-96}.
$$

The scaled cutoff probability is bounded by $v_b=4/7$ when $b+8\le4\ell$, and by $v_b=1$ otherwise. Since the bound is applied at each joint degree and bin before summation, each rounded coefficient $q_b/G$ is charged only once per pole. [Angular factors](../lean/paired-profile/NonprincipalPoleValue.lean) · [Weighted bin argument](../lean/paired-profile/FiniteWeightedBinCost.lean) · [Single-pole theorem](../lean/paired-profile/NonprincipalValueCost.lean)

**The finite sum.** For $c=c_b$, each of the two signed tails after the positive and negative odd index 63 contributes at most $(1+c(63^2-1))^{-95}/(380c)$ to the first absolute moment. The discrete tail inequality applies because $c\ge1/7680$ implies $3c(63)^2\ge1$. The nonprincipal moment is therefore at most

$$
M(c)=2\sum_{i=1}^{31}\frac{2i+1}{(1+c((2i+1)^2-1))^{96}}+\frac{1}{190c(1+c(63^2-1))^{95}}.
$$

The full error is at most $\sum_{b=0}^{5(X-1)}v_b M(c_b) q_b/G$. Both signs are included and the two principal poles are omitted. [Signed lattice proof](../lean/paired-profile/NonprincipalMoment.lean)

**Numerical verification.** Rounding the first-moment weights upward at $2^{64}$ reproduced all nine previously reviewed upper bounds to the nearest upward millionth. They range from 63,943 in the interval $10\le n/k\le16$ to 164,099 in the interval $44\le n/k\le48$. The rational replay recomputes the product table from the existing integer recurrence and checks the written result in every interval. [Exact calculation](check-nonprincipal.py) · [All nine results](nonprincipal-output.txt) · [Earlier determinant comparison](uniform-carrier.md)

Local Lean 4.19 checked the analytic reduction with the standard axiom set. The production port checks the wrapper for the original permutation probabilities. The fixed numerical ceilings have been replayed in exact Python. The regular numerator error and the isolated cutoff jump have their own cost terms. [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)
