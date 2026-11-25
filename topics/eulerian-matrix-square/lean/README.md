# Lean verification of Eulerian cluster polynomials

`EulerianRootSpacing.spacingStep_roots` starts with positive roots $x_i$ satisfying $v x_i<x_j$ for $i<j$, where $v>1$. For $a>0$, the update $G(t)-atG(t/v)$, with $G(t)=\prod_i(x_i-t)$, has one simple root in each gap $(0,x_0), (v x_0,x_1),\ldots,(v x_{m-1},\infty)$. The theorem also covers the empty input, with a single gap $(0,\infty)$. It gives the exact real roots multiset, multiplicative spacing of the new roots, and factorization with a positive scalar. `EulerianRootSpacing.spacingStep_C_mul` gives the update for an arbitrary scalar multiple of $G$.

This checks the inductive step for the limiting polynomials in [matrix-powers.md](../matrix-powers.md). The coefficient estimates and asymptotic zero theorems are written proofs.

After preparing the [shared Lean project](../../../shared/lean/README.md), run `lake build EulerianRootSpacing` from `shared/lean`. Lean 4.19.0 checked both declarations using only `propext`, `Classical.choice`, and `Quot.sound`.

The [cluster module](EulerianCluster.lean) connects this step to the polynomial in the manuscript. For a list of positive weights, `coeff_cluster` proves that coefficient $k$ of the output in the modulus variable is coefficient $k$ of $\prod_i(1-\alpha_i x)$ times $v^{-\binom k2}$. The theorem `matrixPowerCluster` instantiates the weights for every integer matrix power $p$ and every cluster $h\ge1$. It gives a complete real linear factorization whose roots are positive and strictly separated by the factor $(h+1)/h$. This verifies the finite limiting polynomial itself. Asymptotic convergence of the matrix rows to that polynomial is a written theorem.

~~~sh
lake build EulerianCluster
~~~
