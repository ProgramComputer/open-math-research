# The isolated numerator jump at the cycle cutoff

The difference of the original cutoff probabilities has an atom $b_k=1/k$. In the adjacent sine determinant, its remaining degree is exactly $T=n+1-k$. Let $S=\sin\theta>0$, $U=6/5$, $nS^2\ge U$ and $n\ge10000$. Use an interval $\ell\le n/k\le X$ from the nine-interval comparison. Write $A_0$ for its rational lower bound on $kS$. The argument works at every angle satisfying these conditions. [Original-enumerator theorem](../lean/paired-profile/RepositoryCutoffJump.lean) · [Uniform determinant comparison](uniform-carrier.md)

At each pole, the coefficient at degree $T$ splits into the sum of its one-primitive terms and a residual supported on products with at least two primitives. The empty product contributes zero because $T>0$. Subtracting the one-primitive part before taking the norm lets the two estimates use different information. [Coefficient decomposition](../lean/paired-profile/MarkedCoefficientComparison.lean)

**One primitive.** The single primitive has degree $T>(\ell-1)k$. The factorial estimate gives $k^2|b_T|\le1/(2(\ell-1)!)$. The outer pole carries exponent $k$ and the inner pole carries exponent $T-1$. Applying their angular bounds separately yields a product of a signed mass and a signed sum weighted by reciprocal pole distance. Each includes a finite head and an explicit tail. The single-primitive error, in upward millionths, is at most 596 in the first interval, 107 in the second and one in each of the other seven. [Exact-degree argument](../lean/paired-profile/CutoffSinglePrimitive.lean) · [Nine interval bounds](../lean/paired-profile/CutoffSingleSlabs.lean)

**Two or more primitives.** Put $u=A_0/(kS)\le1$. Write $L_b/G$ and $q_b/G$ for the rounded linear and product bounds, where $G=2^{56}$. Retaining the actual angle in the linear estimate bounds each linear coefficient by $uL_b/G$. Differentiating the multiple part of the finite product lets us retain this factor in its positive-degree coefficients. The resulting bound in bin $b>0$ is $u(q_b-L_b)/G$. This subtraction is justified even when the rounded linear bound exceeds the actual linear coefficient. [Scaled linear estimate](../lean/sine-comparison/LinearSlabs.lean) · [Derivative comparison](../lean/paired-profile/ScaledMultipleBudget.lean)

For a nonzero contribution, $4T\le kb\le5T$. The identity $T+k=n+1$ and integrality give $4(\ell-1)<b\le5(X-1)$. Also $u/S\le A_0X/U$. Put $c_b=\max(1/X,1-b/(4\ell))/160$ and let $M_0(c_b)$ denote the finite upper bound for the zeroth moment of the signed poles. The multiple-primitive contribution is at most

$$
\frac{A_0 X}{U}
\sum_{4(\ell-1)<b\le5(X-1)}
\frac{q_b-L_b}{G} M_0(c_b).
$$

This holds uniformly in the finite pole set and bounds the coefficient of the actual residual. It accounts for every bin that can contain degree $T$. [Bin support and angular scaling](../lean/paired-profile/CutoffAtomGeometry.lean) · [Single-pole theorem](../lean/paired-profile/AtomWindowAggregate.lean) · [Sum over all poles](../lean/paired-profile/RepositoryMultipleAtom.lean)

**Verification.** The pinned Linux build compiled the original-enumerator wrapper. The exact rational replay and a second evaluation using the Lean-generated product coefficients agree with the previously reviewed combined ceilings in all nine intervals. Rounding each summand separately can give a larger integer than rounding their exact sum. [Lean build and axiom record](cutoff-jump-verification.md) · [Rational checker](check-cutoff-jump.py) · [All nine results](cutoff-jump-output.txt) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)
