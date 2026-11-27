# Cauchy bounds for cutoffs eight through ninety-nine

Let $8\le k\le99$, $n\ge10000$, $s\ge0$, $p=s+\pi i$, $r=|p|$, and $S=\pi/r$. Suppose $nS^2\ge1$. The theorem chooses one radius $R$ that separates the contour from every odd pole. If $F_j$ denotes the normalized Fourier coefficient of the original generating function on that circle and $T$ is its numerator, set $W=r(r/R)^n/(2|T(p)|)$. Then

$$
W|F_n|<1/25,\qquad W\left|(r/R)F_{n+1}-(s/r)F_n\right|<S/25.
$$

The squared-radius gap gives distance at least $r/n$ from every pole. The original numerator estimates bound the logarithmic contraction by $32$, $60$, and $65$ on the three successive cutoff ranges $50$–$99$, $10$–$49$, and $8$–$9$. The normalized amplitude is at most $2n^2e^M$ with the corresponding bound $M$. Also $(r/R)^n\le\exp(-4n/(5k))$. These bounds permit direct integration of the absolute value of the trace at both frequencies. [Original theorem](RepositorySmallBoundary.lean) · [Circle and decay](SmallCutoffCircle.lean) · [Two-coefficient estimate](SmallCutoffCauchyPair.lean)

## Verification

Lean 4.33.1 checked both Fourier errors from the original permutation generating function, including all three numerator bounds, for every cutoff from eight through ninety-nine. [Verification record and build command](verification.md) · [Independent mathematical review](review.md)
