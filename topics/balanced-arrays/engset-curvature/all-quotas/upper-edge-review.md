# Independent audit of upper mesoscopic extension concavity

**Verdict.** I found no substantive gap for fixed $`2\le r<d`$, with $`e=nr-dk\to\infty`$ and $`e/n\to0`$. Both leading constants are negative. Correct the displayed definition $`H(h)=x,y(h)`$ to $`H(h)=x\thinspace y(h)`$. The argument concerns actual balanced-array counts in the stated regime.

## Torus and analytic expansion

For each $`j<d`$, choose an $`(r-1)`$-set avoiding $`j,d`$, and adjoin $`j`$ or $`d`$. This is possible since $`r-1\le d-2`$. Its exchange vector $`e_j-e_d`$ is realized by two atoms of probability $`\Omega(1)`$. Separately take a size-$`r`$ set containing $`d`$ and delete $`d`$, giving vector $`e_d`$ with pair probability $`\Omega(h)`$. Each lower bound follows from the nonnegative independent-pair expression for $`1-|K_h|^2`$. Averaging the $`d`$ individual lower bounds verifies the simultaneous inequality even if selected summands overlap. Together the differences generate the whole lattice. For $`h>0`$, equality in the modulus bound is possible only at the origin modulo $`2\pi`$. At $`h=0`$ there is a full common-angle circle, and the deletion bound gives its required $`e=nh`$ scale for positive $`h`$.

The torus map $`\theta\mapsto((\theta_j-\theta_d)_{j<d},\theta_d)`$ is unimodular. A point off a fixed neighborhood of the origin has at least one image coordinate separated from zero in torus distance. Splitting the exponent into two halves isolates suppression at least $`\exp(-c e)`$, and integrating the other half retains the factor $`n^{-(d-1)/2}e^{-1/2}`$. This addresses slowly growing $`e`$, where an unweighted torus-volume estimate would be insufficient. Locally, the difference coordinates control the sum-zero projection $`w`$. The radial coordinate $`v`$ differs from $`-\theta_d`$ by a linear form in $`w`$, and $`e\le n`$ makes the resulting scaled quadratic comparison uniform. Hence the remainder outside the scaled box also retains both volume factors.

I checked the power bookkeeping after writing $`n=e/h`$. For a term $`v^a w^{b'}`$ involving a radial factor, the cumulant's factor $`h`$ leaves $`e^{1-(a+b')/2}h^{b'/2}`$. Purely transverse terms with $`b'\ge2`$ instead contribute $`e^{1-b'/2}h^{b'/2-1}`$. The two quadratic blocks are positive definite after scaling, with zero cross term for every $`h`$ by symmetry. The radius of the joint analytic logarithm can be fixed uniformly near $`h=0`$. Subtracting its restriction $`v=0`$ before estimating the degree-twelve Taylor remainder keeps the factor $`h`$ on radial terms. Exponential expansion through $`e^{-9/2}`$ leaves a polynomial-Gaussian integrable $`O(e^{-5})`$ error on the growing cutoff. Simultaneous reflection removes odd half-orders in $`e`$. Separate transverse reflection removes half-integer powers of $`h`$, so the retained Gaussian coefficients are analytic at zero. The leading Gaussian mass is strictly positive. The original tilted integral is therefore positive uniformly for large $`e`$, as is also evident at admissible quotas from the nonempty counting model.

## Constants and finite differences

At $`h=0`$ only purely radial nonquadratic cumulants survive, and the scaled cumulants tend to the Poisson values one. The radial Gaussian has variance one at zero. Its order-$`e^{-1}`$ integral contribution is $`3/24-15/72=-1/12`$. Equivalently the contributing terms are the quartic and half the square of the cubic, with the minus sign from $`i^6`$. The log retains this first correction and Stirling cancels it, giving $`F_1(0)=0`$.

The adjacent-ratio prefactor $`u_k/e`$ at $`h=0`$, through order $`\epsilon^2=e^{-2}`$, is $`(\rho/b)\prod_{j=0}^{d-1}(1-j\epsilon)^{1/d}`$. For the geometric mean, the second coefficient equals $`-\frac12`$ of the variance of the uniform law on $`0,\ldots,d-1`$, namely $`-(d^2-1)/24`$. Analytic differences of $`F_j`$ contribute no order-$`\epsilon^2`$ correction there because $`F_1(0)=0`$. This verifies $`C(0)=-(d^2-1)\rho/(24b)`$. Separately $`H=x\thinspace y(h)`$ and inversion of $`h=b y+(2b_2-b^2)y^2+O(y^3)`$ give

$$
H''(0)=2\big((r-1)b^2-2r b_2\big)/(db^3)
=-2(r-1)(d-r)(d-r+1)/(dr(d-r+2)).
$$

The two adjacent-ratio errors in the log need no derivative bounds. They remain $`O(e^{-5})`$ before multiplying by $`e`$, so their pointwise contribution to $`u_k`$ is $`O(e^{-4})`$. Taking a second difference of these bounded neighboring errors still costs only $`O(e^{-4})`$. The smooth retained terms yield the stated $`d^2H''(0)/n`$ and $`2d^2C(0)/e^3`$, with all other second differences $`o(n^{-1}+e^{-3})`$. This reasoning covers the crossover without assuming either contribution dominates.

**Signed** — four_literature, independent agent-assisted mathematical review.
