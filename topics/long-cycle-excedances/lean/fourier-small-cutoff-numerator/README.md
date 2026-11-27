# Actual small-cutoff Fourier numerator

The production endpoints in [RepositorySmallCutoffNumerator.lean](RepositorySmallCutoffNumerator.lean) bound the sum of the two original cutoff-log displacements by $32$ for $50\le k<100$ and by $60$ for $10\le k<50$. They allow all heights $s\ge0$ and every outer point with $r\le |w|\le(1+1/k)r$, where $r=|s+\pi i|$. Each comparison uses the same principal contraction radius $(1-1/k)r$ and the repository's principal analytic logarithm. The cutoff polynomial uses the original tilt coefficients.

For the low heights $s\le4\sqrt{k}$ and $s\le8\sqrt{k}$ respectively, reuse the actual odd-pole logarithm envelope and the existing all-degree disk identity. The radial slope $5/2$ works uniformly for $k\ge10$. With $\rho=1-1/k$, the exact geometric-tail scalar is $\rho^k/(k(1-\rho))=\rho^k\le e^{-1}<3/8$. Bounds on $U=1/(S\sqrt{k})$ of $13/10$ and $13/5$ yield $32$ and $60$.

Above those heights, the checked frequency method extends with rational lower-tail splits $7/5$ and $2$ and exponential decay rates $9/200$ and $1/8$. The key prefix bound uses $u\le\exp(\ell)$ and $uk\le x$. It gives an exponential factor $\exp(((1+\ell)/u)x)$. The numerical choices $\ell=337/1000$ and $\ell=3/4$ suffice. The contracted positive-frequency tail uses $(k/(2t))e^{-k/6}+2/(1-d)$, where $t=(1-1/k)r$ and $r-s\le ds/k$. Finite cutoff upper endpoints control the first term by $1/10$ and $1$, so these arguments need no separate harmonic or Stirling estimate.

## Checks

Run `python3 -I -B check.py /path/to/new/project` on Linux with Lean 4.33.1. The optional `--retained-imports` argument reuses authenticated common-pin import objects. The checker rebuilds the all-degree logarithm and the original numerator inputs, then compiles and replays the eleven new modules. In a prepared authenticated project, call `compile_small_cutoff_numerator(project)` after staging the same original dependencies. [Checker](check.py) · [Production pin](../common-pin/README.md)

The local Lean 4.19.0 check covers the generic analytic estimates, both scalar budgets, and the combination at the actual contour points with the imported analytic identities supplied explicitly. The production run checks the unconditional wrapper against the genuine imported coefficient and analytic-log sources.

This work gives only the numerator contraction. The small-cutoff contour choice and bound for the denominator, Cauchy error and residues belong to separate steps.

[Independent scope and arithmetic review](independent-review.md) · [Hosted verification record](verification.md)
