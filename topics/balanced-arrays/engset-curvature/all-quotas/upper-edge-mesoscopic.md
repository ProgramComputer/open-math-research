# Strict extension concavity at the mesoscopic upper edge

Fix integers $`2\le r<d`$. Let $`a_k`$ count the labeled capped arrays, and let
$`u_k=(k+1)(a_{k+1}/a_k)^{1/d}`$. Put $`e=nr-dk`$, $`h=e/n`$, and suppose
$`e\to\infty`$ and $`h\to0`$. Then

$$
u_{k-1}-2u_k+u_{k+1}
=\frac{d^2H''(0)}n-\frac{d^2(d^2-1)\rho}{12b e^3}
+o(n^{-1}+e^{-3}), \qquad
\rho=\frac rd,\quad b=\frac{\binom d{r-1}}{\binom dr},
$$

where $`H''(0)<0`$. Thus the proposed strict concavity holds along every such sequence, including the crossover $`e\asymp n^{1/3}`$. The current argument concerns fixed $`d,r`$.

## The moving tilted row law

Let $`P(y)=\sum_{j=0}^r\binom d{r-j}y^j/\binom dr`$. A row with occupied set $`S`$ has tilted probability $`y^{r-|S|}/(\binom dr P(y))`$. Write $`T=r-|S|`$ for its deficit. Determine $`y=y(h)`$ by $`yP'(y)/P(y)=h`$. The implicit function theorem gives a real analytic $`y`$ near zero with $`y(0)=0`$, $`y'(0)=1/b`$. For positive small $`h`$, the size-$`r`$ subsets have individual probabilities bounded below, and each size-$`(r-1)`$ subset has probability bounded below by a positive constant times $`h`$. Also $`\mathbb P(T=1)=h+O(h^2)`$ and $`\mathbb P(T\ge2)=O(h^2)`$, with analytic probabilities.

Let $`X`$ be the row indicator vector, $`Z`$ its orthogonal projection to the sum-zero subspace in fixed orthonormal coordinates, and $`x=(r-h)/d`$. Then $`\mathbb E X=x\mathbf1`$, $`\mathbb EZ=0`$, and $`\mathrm{Cov}(T,Z)=0`$ by permutation invariance. The covariance of $`Z`$ is analytic in $`h`$ and positive definite at zero: uniform size-$`r`$ subsets have all the exchange differences $`e_i-e_j`$. Moreover $`\mathrm{Var}(T)/h`$ is analytic at zero with value one. For every $`m\ge2`$, the order-$`m`$ cumulant of $`T`$ equals $`h+O(h^2)`$, since $`\log\mathbb E e^{vT}=h(e^v-1)+O(h^2)`$ as a convergent analytic function near $`v=0`$. Every joint cumulant involving at least one copy of $`T`$ vanishes at $`h=0`$. Constants here and below may depend on the fixed $`d,r`$.

## A two-scale expansion with analytic coefficients

Write $`K_h(\theta)=\mathbb E e^{i\theta\cdot X}`$ for the uncentered characteristic function. Its squared modulus satisfies

$$
1-|K_h(\theta)|^2
=\sum_{S,S'}\mathbb P(S)\mathbb P(S')
\bigl(1-\cos(\theta\cdot(\mathbf1_S-\mathbf1_{S'}))\bigr).
$$

For each $`j<d`$ a pair of size-$`r`$ subsets differing by exchange of $`j`$ and $`d`$ gives a fixed positive multiple of $`1-\cos(\theta_j-\theta_d)`$. A size-$`r`$ set containing $`d`$ and the set obtained by deleting $`d`$ give a positive multiple of $`h(1-\cos\theta_d)`$. All terms are nonnegative, so, taking the relevant torus representatives in $`[-\pi,\pi]`$, these inequalities imply

$$
|K_h(\theta)|^n
\le \exp\left(-c n\sum_{j<d}|\theta_j-\theta_d|_{2\pi}^2
-c e|\theta_d|_{2\pi}^2\right)
$$

for some $`c>0`$. The coordinates $`\theta_j-\theta_d`$ and $`\theta_d`$ preserve torus measure. In particular the bound retains the transverse volume factor $`n^{-(d-1)/2}`$ even when $`e`$ grows arbitrarily slowly compared with $`n`$. Near the origin a constant invertible linear change gives the argument $`(v,w)`$ for the random vector $`(T-h,Z)`$, where $`v`$ is minus the arithmetic mean of the angles. The quadratic bound in torus coordinates dominates a positive constant times $`e v^2+n\lVert w\rVert ^2`$ uniformly for $`0<h\le h_0`$. This follows since each transverse angle difference controls the entire sum-zero projection, and the difference of $`v`$ from $`-\theta_d`$ is a fixed linear function of that projection with $`e\le n`$.

Let $`I(n,e)`$ be the tilted probability of column sum $`(k,\ldots,k)`$. Fourier inversion in $`d`$ dimensions is centered exactly at the mean. On the central box substitute $`v=t/\sqrt e`$, $`w=s/\sqrt n`$. The Jacobian is a positive constant times $`e^{-1/2}n^{-(d-1)/2}`$. Outside the box $`|t|+\lVert s\rVert \le e^{1/100}`$, the torus bound above, integrated using the two Gaussian scales, contributes at most that same volume factor times $`O(\exp(-c'e^{1/50}))`$. To justify use of this box globally, first restrict to a fixed neighborhood of the torus origin where the representatives do not wrap. On its complement one angular difference or the common angle is bounded away from zero, so the same product estimate gives the two-scale volume times $`O(e^{-c'' e})`$.

The centered row log-characteristic function is jointly analytic in a fixed complex neighborhood of $`(h,v,w)=0`$, using its branch at zero. A term of degree $`a`$ in $`v`$ and $`b'`$ in $`w`$, of total degree $`\ell=a+b'\ge2`$, has after multiplication by $`n`$ and rescaling the form

$$
e^{1-\ell/2}\begin{cases}
h^{b'/2}\times\text{an analytic coefficient in }h,& a\ge1,\\
h^{b'/2-1}\times\text{an analytic coefficient in }h,&a=0.
\end{cases}
$$

The first case uses the vanishing of each radial cumulant at $`h=0`$. In the second case $`b'\ge2`$. At degree two the scaled Gaussian is block diagonal, with blocks $`\mathrm{Var}(T)/h`$ and $`\mathrm{Cov}(Z)`$, both bounded and positive definite after restricting $`h_0`$. Expand through degree eleven. The Taylor remainder, after multiplication by $`n`$, is $`O(e^{-5}(|t|+\lVert s\rVert )^{12})`$ on the central box. For this bound, separate the log-characteristic function at $`v=0`$ and its difference from that restriction. The former remainder has degree at least twelve in $`w`$, while the latter is divisible by $`h`$ and its remainder is bounded by a constant times $`h(|v|+\lVert w\rVert )^{12}`$. Uniform convergence of the analytic Taylor series gives these bounds.

Now expand the exponential of the nonquadratic terms through order nine in $`e^{-1/2}`$. The omitted terms, after multiplication by the Gaussian, have integrated size $`O(e^{-5})`$: on the box the nonquadratic terms are uniformly $`o(1)`$, and the remainder is bounded by $`e^{-5}`$ times a fixed polynomial in $`|t|+\lVert s\rVert `$ times the Gaussian. Extend each polynomial Gaussian integral to all of $`\mathbb R^d`$ with exponentially small error. Odd powers of $`e^{-1/2}`$ vanish by simultaneous reflection, since their total monomial degree is odd. Terms of odd total transverse degree vanish by transverse reflection alone because the Gaussian is block diagonal. The surviving powers of $`h`$ displayed above are therefore nonnegative integers. The Gaussian integrals, including the leading determinant factor, are analytic in $`h`$, since their covariance matrices are analytic and nonsingular at zero. The leading coefficient is positive on a neighborhood of zero.

Taking the logarithm gives analytic functions $`f_j`$ such that

$$
\log I(n,e)=-\tfrac12\log e-\tfrac{d-1}2\log n
+\sum_{j=0}^4 f_j(h)e^{-j}+O(e^{-5}).
$$

The error is uniform for $`0<h\le h_0`$ and $`e\to\infty`$. At $`h=0`$ all nonquadratic terms with transverse variables vanish. The pure radial normalized cumulants tend to one. In the leading Gaussian law $`t`$ is standard normal, so the relative coefficient of $`e^{-1}`$ is $`\mathbb E[t^4]/24-\mathbb E[t^6]/72=3/24-15/72=-1/12`$. Taking the logarithm preserves that first relative coefficient. Thus $`f_1(0)=-1/12`$.

## Isolating the factorial and taking second differences

Write $`S(h)=\log P(y)-h\log y`$. The exact tilted counting identity is
$`a_k=\binom{d}{r}^{n}\exp(n S(h))I(n,e)`$. Since $`S'(h)=-\log y`$, one has
$`S(h)=h(1+\log(b/h))+\Psi(h)`$ with $`\Psi`$ analytic, $`\Psi(0)=0`$, and
$`\Psi'(h)=-\log(by(h)/h)`$, so $`\Psi'(0)=0`$. Stirling's formula to order four, with error $`O(e^{-5})`$, now gives

$$
\log a_k=n\log\binom dr+e\log(nb)-\log(e!)
-\tfrac{d-1}2\log n+n\Psi(h)
+\sum_{j=0}^4 F_j(h)e^{-j}+O(e^{-5}),
$$

where the $`F_j`$ are analytic and $`F_1(0)=0`$ by cancellation of the $`-1/(12e)`$ term.

Put $`\epsilon=1/e`$. Replacing $`k`$ by $`k+1`$ replaces $`e`$ by $`e-d`$ and $`h`$ by $`h'=h(1-d\epsilon)`$. After taking the adjacent ratio, the factorial contribution to $`u_k/e`$ is $`\prod_{j=0}^{d-1}(1-j\epsilon)^{1/d}`$. The remaining prefactor is $`(x+h\epsilon)/b`$. The contribution in the logarithm from $`n\Psi`$ after taking the $`d`$th root is

$$
\frac{\Psi(h-dh\epsilon)-\Psi(h)}{d h\epsilon}
=-\int_0^1 \Psi'(h-dh\epsilon t)\thinspace dt,
$$

which extends analytically at $`h\epsilon=0`$. The other displayed log terms give the analytic contributions $`\epsilon^j[(1-d\epsilon)^{-j}F_j(h')-F_j(h)]/d`$. Thus $`u_k/e`$ is an analytic function of $`(h,\epsilon)`$ up to $`O(e^{-5})`$. Its expansion in $`\epsilon`$ yields analytic $`B,C,E_2,E_3`$ with

$$
u_k=nH(h)+B(h)+C(h)e^{-1}+E_2(h)e^{-2}+E_3(h)e^{-3}+O(e^{-4}),
\qquad H(h)=xy(h).
$$

Indeed the constant coefficient of $`u_k/e`$ is $`(x/b)e^{-\Psi'(h)}=xy(h)/h`$. At $`h=0`$ the $`\Psi`$ contribution vanishes, and so do the differences for $`j=0,1`$, by $`h'=h=0`$ and $`F_1(0)=0`$. For $`j\ge2`$ the difference starts at order $`\epsilon^{j+1}`$. Therefore $`C(0)`$ is $`\rho/b`$ times the second coefficient in $`\prod_{j=0}^{d-1}(1-j\epsilon)^{1/d}`$. Expanding its logarithm gives

$$
C(0)=-\frac{(d^2-1)\rho}{24b}.
$$

For the other constant, write $`s_{\ast}=d-r`$ and $`b_2=\binom d{r-2}/\binom dr`$. The deficit equation has expansion $`h=b y+(2b_2-b^2)y^2+O(y^3)`$. Inverting gives $`y=h/b-(2b_2-b^2)h^2/b^3+O(h^3)`$. Multiplying by $`x=\rho-h/d`$ gives

$$
H''(0)
=\frac{2((r-1)b^2-2r b_2)}{d b^3}
=-\frac{2(r-1)s_{\ast}(s_{\ast}+1)}{d r(s_{\ast}+2)}<0.
$$

Finally the centered second difference of step $`d`$ in $`e`$ of $`nH(e/n)`$ is $`d^2H''(0)/n+o(n^{-1})`$. For $`B(e/n)`$ it is $`O(n^{-2})`$. For $`C(e/n)/e`$ its second derivative is $`2C(0)/e^3+o(e^{-3})`$ uniformly on $`[e-d,e+d]`$, so its second difference contributes $`2d^2 C(0)/e^3+o(e^{-3})`$. The second derivatives of the next two smooth terms are $`O(e^{-4})`$, using $`h\to0`$. The pointwise uniform remainder also has second difference $`O(e^{-4})`$. This proves the asserted two-scale asymptotic.
