# Adjacent rows on symmetric finite pole sets

The determinant estimate for consecutive long-cycle excedance rows can be checked on the finite sets $A_M=[-M-1,M]\cap\mathbb Z$. These sets contain both principal poles, are closed under $q\mapsto-q-1$, and eventually contain every finite set of indices. The two original normalized coefficients converge along these sets by the previously checked coefficientwise limit. The principal contribution converges along the same sets. Consequently a uniform upper bound for the difference between the finite principal contribution and the finite determinant passes to their limits. [Symmetric windows](SymmetricPoleComparison.lean) · [Principal contribution](WindowPrincipalLimit.lean) · [Original permutation rows](RepositoryAdjacentWindows.lean)

**Exact finite identity.** Let $D$ be the single-pole cycle series with its constant removed, $d_s=[u^s]D$, and $b_s=d_s-d_{s-1}$, taking $d_{-1}=0$. For each distinguished pole $a$ in a finite set $A$, write $w_a$ for its angular denominator and $Q_a$ for the product of its occupied factors over the other poles in $A$. In the combination of rows with weights $x,-y$, the term indexed by $a,t$ is

$$
[u^t]Q_a\cdot w_a^{-s}\bigl(d_{s-1}(w_a x-y)-b_s y\bigr),\qquad s=n+1-t,\quad 0\le t\le n+1.
$$

Summing gives the exact difference of the two finite coefficients. At $t=n+1$ the original distinguished series has zero constant. This makes the older coefficient and the padded boundary term agree. Centering the convolution at the limiting probability preserves the exact first difference between adjacent sizes. [Finite coefficient identity](FiniteAdjacentResidues.lean) · [Centered convolution](PrincipalAdjacentError.lean)

**Probability error.** Let $p_N$ be the probability that every cycle of a uniform permutation on $N$ letters has length at least $k$. Omit the empty permutation by setting its weight to zero in the centered convolution. Evaluating the entire numerator at one and telescoping the coefficients gives $p_N\to c_k=\exp(-H_{k-1})$. For $j\ge2$ and $N\ge jk$ the centered error satisfies

$$
k|p_N-c_k|\le\frac{j+1}{2j(j!)}.
$$

To prove this, start the walk at $N$ by evaluating the probability at $\max(s,N)$. On the block $jk<s\le(j+1)k$ the scaled variation is at most $1/(2j!)$. The bound $B_j=(j+1)/(2j(j!))$ satisfies $1/(2j!)+B_{j+1}\le B_j$. Induction gives a bound independent of the terminal block. Passing to the probability limit gives the assertion, including starting points in the interior of a block. For $k\ge100$, combining this estimate with the previously proved probability bands gives the exact piecewise upper bound used by the rational determinant checker. [Limit and tail identity](ExactCycleProbabilityLimit.lean) · [Factorial bound](FactorialProbabilityTail.lean) · [Piecewise error bound](ProbabilityErrorBands.lean)

For the actual finite product of occupied factors at the principal pole, a summable majorant for its centered degree masses now bounds the error of the full original convolution, including the terms past the row degree. Instantiating that majorant with the binned bounds gives the first of the four determinant costs. [Centered cost theorem](FinitePrincipalCost.lean)

**Verification scope.** Lean 4.33.1 checked the finite coefficient identities, cofinality, convergence of the principal contribution and the factorial probability bounds, including the adapter to the literal permutation enumerators. The replay covered 55 modules and 104 named axiom reports. [Verification record](adjacent-verification.md) The four complete determinant error costs and the final root-list assembly are still being formalized. [Shared checker](check.py) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

The [principal bin estimate](principal-bin-cost.md) reduces the untruncated centered convolution to 241 rounded coefficients and a uniform tail.
