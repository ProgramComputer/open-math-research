# Eventual extension concavity at every quota in fixed dimension

For nonnegative integer $`n`$, integers $`d\ge2`$ and $`1\le r\le d`$, let $`a_k`$ count
labeled binary $`n`$ by $`d`$ arrays with every column sum $`k`$ and every row
sum at most $`r`$. Write $`D=\lfloor nr/d\rfloor`$ and
$`u_k=(k+1)(a_{k+1}/a_k)^{1/d}`$ for $`0\le k<D`$.
The counts through $`D`$ are positive by distributing the successive columns' ones into consecutive blocks of a cyclic ordering of the rows.

**Theorem.** For each $`d\ge2`$ there exists $`N(d)`$ such that, simultaneously for every $`1\le r<d`$ and every $`n\ge N(d)`$,

$$
u_{k-1}-2u_k+u_{k+1}<0
\qquad (1\le k\le D-2).
$$

Empty index ranges are vacuous. At full cap $`r=d`$ the same second differences are zero, since $`a_k=\binom nk^d`$ and $`u_k=n-k`$. A zero extension at quota $`D`$ is outside the statement. The theorem addresses an extension inequality for the original balanced-array coefficients. [Per Alexandersson’s original real-rootedness question](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

## Rank one and compact interior

If $`r=1`$, the extension count raised to the $`d`$th power is
$`\prod_{j=0}^{d-1}(n-dk-j)`$. On any positive interval containing three genuine extensions, the geometric mean of those affine factors is strictly concave. In fact its second derivative divided by the mean is $`d^2`$ times the negative variance of the $`d`$ reciprocals of the factors under their uniform distribution. The reciprocals are distinct since $`d\ge2`$.

Now fix $`2\le r<d`$ and put $`\rho=r/d`$. The [compact-interior extension argument](../finite-extension.md#fixed-dimensions-compact-interior) proves strictness uniformly on every compact subinterval of $`0<k/n<\rho`$, for all sufficiently large $`n`$. The tilted entropy there gives $`u_k=n f(k/n)+f_1(k/n)+n^{-1} f_2(k/n)+O(n^{-2})`$, with smooth retained terms and $`f''<0`$. The two neighborhoods with distance to the nearest quota boundary tending to infinity are handled by the [lower mesoscopic proof](sparse-edge.md) and the [upper mesoscopic proof](upper-edge-mesoscopic.md).

## Fixed lower quota

Put $`p_k=a_k/\binom nk^d`$. Independently select a uniform $`k`$-subset of rows in each column. At fixed $`k`$, a specified row violates the cap with probability $`\binom d{r+1}(k/n)^{r+1}+O(n^{-r-2})`$. For two specified rows the joint probability is $`O(n^{-2(r+1)})`$. To see this, prescribe $`r+1`$ occupied columns for each row in finitely many ways. In each column, requiring one or both specified labels has probability $`O(n^{-1})`$ or $`O(n^{-2})`$ respectively. First and second Bonferroni bounds and the logarithm give

$$
\log p_k=-\binom d{r+1} k^{r+1}n^{-r}+O(n^{-r-1}).
$$

Since $`u_k=(n-k)(p_{k+1}/p_k)^{1/d}`$, the second difference at fixed $`k\ge1`$ equals

$$
-\frac1d\binom d{r+1} n^{1-r}
\left.\Delta^3 t^{r+1}\right|_{t=k-1}+O(n^{-r}),
$$

where $`\Delta f(t)=f(t+1)-f(t)`$. The third difference is positive, since it is the integral of the strictly positive third derivative at positive arguments over a unit cube.

## Fixed upper deficit

Put $`e=nr-dk`$, $`b=\binom d{r-1}/\binom dr`$, and
$`\lambda=r(d-r)/(d(d-1))`$. At any fixed feasible $`e\ge0`$ the main arrays before balancing use $`e`$ rows of size $`r-1`$ and all other rows of size $`r`$. The weights of all profiles with fewer deficient rows contribute an $`O(1/n)`$ relative factor after the balancing estimates below. Condition on the occupied sets of the deficient rows. For the remaining rows choose independent uniform size-$`r`$ subsets. Their projection to the first $`d-1`$ coordinate counts has covariance $`\lambda(I-\mathbf1\mathbf1^{\mathrm T}/d)`$, of determinant $`\lambda^{d-1}/d`$. Its support differences include every coordinate unit vector by exchanging a label with label $`d`$. Thus its characteristic function has a single modulus-one point on the torus. Near that point the covariance is nonsingular. Fourier inversion and Gaussian scaling give, for every target at bounded displacement from its expectation, probability asymptotic to $`C_{d,r}n^{-(d-1)/2}`$, with $`C_{d,r}=\sqrt d(2\pi\lambda)^{-(d-1)/2}`$. The same argument gives a uniform upper bound of this order, even for the other finitely many deficit profiles. The last column equation follows from the total sum. Therefore

$$
a_k=C_{d,r}\binom{d}{r}^{n} n^{e-(d-1)/2}\frac{b^e}{e!}(1+o(1)).
$$

At each fixed $`D-k\ge2`$, pass if necessary to a fixed residue of $`nr\bmod d`$. Then $`u_k`$ tends to
$`(\rho/b)\bigl(e(e-1)\cdots(e-d+1)\bigr)^{1/d}`$, and the neighboring extensions tend to the same expression at $`e\pm d`$. Those three deficits are at least $`d`$. The limiting function is strictly concave on this interval by the same geometric-mean derivative calculation. There are only finitely many possible residues.

## Moving upper deficit and the crossover

For $`e\to\infty`$ with $`e/n\to0`$, the [upper-edge expansion](upper-edge-mesoscopic.md) gives

$$
u_{k-1}-2u_k+u_{k+1}=
-\frac{2d(r-1)(d-r)(d-r+1)}{r(d-r+2)n}
-\frac{d^2(d^2-1)\rho}{12b e^3}
+o(n^{-1}+e^{-3}).
$$

The first term comes from the curvature of the tilted entropy. The second comes from preserving the exact falling factorial in the adjacent ratio. If $`e/n^{1/3}\to t\in(0,\infty)`$, the coefficient of $`n^{-1}`$ is the sum of the first negative constant and the second negative constant multiplied by $`t^{-3}`$. Below the crossover the factorial term dominates. Above it the entropy term dominates.

## Combining the regimes

If the claimed row threshold failed for a fixed $`d`$, there would be a sequence of failures with $`n\to\infty`$. There are finitely many proper caps, so restrict to a subsequence with fixed $`r`$. Rank one is already handled. The remaining densities $`k/n`$ lie in $`[0,\rho]`$, so along a subsequence they converge. An interior limit lies in one compact interval, contradicting compact-interior strictness. A limit of zero has a further subsequence with constant $`k`$ or with $`k\to\infty`$. These are the fixed lower quota and [lower mesoscopic](sparse-edge.md) cases. For a limit of $`\rho`$, the integer deficit $`nr-dk`$ is constant along a further subsequence or diverges to infinity. The finite residue argument and the moving upper expansion cover those cases. Each possible failure leads to a contradiction.

This proof gives no effective $`N(d)`$ and no uniform cutoff over dimensions. The all-parameter inequality $`2u_k\ge u_{k-1}+u_{k+1}`$ for every finite admissible $`(n,r,d,k)`$ remains open. These arguments also leave the all-cap real-rootedness conjecture open.
