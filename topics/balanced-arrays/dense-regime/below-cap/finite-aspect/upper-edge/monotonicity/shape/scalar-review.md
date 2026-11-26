# Independent review of the deficit excess

Agent-assisted mathematical review by Codex (`edge_referee`), 2026-11-26.

I accept strict increase of the scalar excess up to mean deficit $`\sqrt{r(d-r)/d}`$. I also accept the stronger result that the excess has exactly one critical point on its full mean interval for $`r\ge2`$, and that this is a nondegenerate maximum. The fixed bounded-slack endpoint transfer is valid, uniformly over near-balanced phases. A separate estimate is needed for the original fibers when the slack grows with $`n`$ or dimension varies.

## Scalar identities and monotonicity

Fix $`d\ge2`$ and a proper cap $`1\le r<d`$. Write $`c=d-r`$. At inverse odds $`x>0`$, let $`J`$ have masses $`\pi_j`$ proportional to $`\binom d{r-j}x^j`$ on $`0\le j\le r`$. Put $`p=\pi_0`$, $`t=\mathrm{E}J`$, $`V=\mathrm{Var}(J)`$, $`g=1/(1+t)-p`$, and $`u=(1+t)g`$. Differentiation in $`\log x`$ gives $`\mathrm{d}t/\mathrm{d}\log x=V>0`$ and $`\mathrm{d}p/\mathrm{d}t=-tp/V`$. The attainable means fill $`0<t<r`$.

Compare $`\pi`$ to the geometric law of the same mean. The ratios of its consecutive likelihood ratios are decreasing on the positive support because $`\pi_{j+1}/\pi_j`$ is decreasing. If $`\pi_0`$ were at least the geometric mass at zero, the signed mass difference would be nonnegative through one prefix and nonpositive afterwards, with a strict negative tail. Equal total mass would then give $`\pi`$ strictly smaller mean, a contradiction. Thus $`0<u<1`$.

The recurrence for the normalized weights includes the inverse odds,

$$
(c+j)\pi_j=x(r-j+1)\pi_{j-1}\qquad (1\le j\le r).
$$

Summing it and its $`j`$-weighted form gives

$$
x(r-t)=c(1-p)+t,\qquad
(1+x)V=x(r-t)(1+t)-t(c+t)=t+cu.
$$

In particular $`V=(r-t)(1+t)(t+cu)/(r+dt+cu)`$. Substituting $`p=(1-u)/(1+t)`$ into $`g'=tp/V-1/(1+t)^2`$ shows that $`g'`$ has the sign of

$$
F(t,u)=(d+1)t^2-[rc+(r-2c)t+dt^2]u-ctu^2.
$$

Indeed $`g'=F/[(1+t)^2(r-t)(t+cu)]`$. At any positive zero of $`F`$ along the scalar trajectory, $`u'=u/(1+t)`$. Substituting this and the zero equation gives the exact identity

$$
\frac{1+t}{u}\frac{\mathrm{d}}{\mathrm{d}t}F(t,u(t))
=rc(1+2/t)+(r-2c)-dt^2+c(1-t)u .
$$

Write $`R=rc/d`$. If $`t^2\le R`$ and $`t\le1`$, the right side is at least $`2rc/t+r-2c>0`$, using $`t<r`$. If $`t^2\le R`$ and $`t\ge1`$, it is at least $`r+c(2r/t-1-t)>0`$, using $`u<1`$ and $`t^2<r`$. Near zero, expansion in $`x`$ and inversion of the mean give $`p=1-t+bt^2+O(t^3)`$, with

$$
b=\frac{\binom d{r-2}\binom d r}{\binom d{r-1}^2}
=\frac{(r-1)(c+1)}{r(c+2)}<1,
$$

where the first numerator factor is zero for $`r=1`$. The expansion is analytic since the mean has derivative $`r/(c+1)>0`$ at $`x=0`$. Thus $`g'\sim2(1-b)t>0`$ as $`t\downarrow0`$. A first zero on $`0<t\le\sqrt R`$ would have positive derivative of $`F`$, contradicting positivity on its left. This proves the scale-one assertion including the upper endpoint.

## The unique scalar maximum

Suppose $`r\ge2`$. For each $`t\in(0,r)`$, $`F(t,0)>0`$ and $`F(t,1)=(t-r)(t+c)<0`$. The quadratic in $`u`$ has just one positive root $`h(t)\in(0,1)`$, with $`F_u(t,h)<0`$. At that root,

$$
F_t(t,h)/h=2rc/t+r-2c+ch>0 ,
$$

so $`h'>0`$. The sign of the derivative along the actual trajectory at a zero is the sign of

$$
D(t)=rc(1+2/t)+r-2c-dt^2+c(1-t)h(t).
$$

The argument for scale one applies to $`D`$. It is also positive for $`0<t\le1`$, since $`rc+r-dt^2\ge c(r-1)`$, $`2rc/t-2c\ge0`$, and $`c(1-t)h\ge0`$. For $`t\ge1`$, $`D'=-2rc/t^2-2dt-ch+c(1-t)h'<0`$. The positive root extends to $`h(r)=1`$ and $`D(r)=d(1-r^2)<0`$. Consequently $`D`$ has one simple zero $`T>\max(1,\sqrt R)`$.

An actual zero before $`T`$ is impossible, since the first such zero would have positive derivative. To rule out a zero exactly at $`T`$, write $`u'=u/(1+t)+L(t,u)F(t,u)`$ with positive smooth $`L=1/[(1+t)(r-t)(t+cu)]`$. The derivative along the trajectory is the value of the smooth function $`B=F_t+F_u[u/(1+t)+LF]`$. Along the curve $`u=h(t)`$, $`B(t,h(t))=h(t)D(t)/(1+t)`$. If the actual trajectory reached that curve at $`T`$, $`F'=0`$ would force $`u'(T)=h'(T)`$, by $`F_u\ne0`$. The actual second derivative of $`F`$ would then equal $`(hD/(1+t))'(T)<0`$, contradicting $`F>0`$ immediately to the left. Every zero after $`T`$ is a strict downward crossing, so there is at most one.

For existence, let $`y=1/x\to0`$. Expanding the row-size distribution at $`y=0`$ gives $`r-t=dy+O(y^2)`$, $`V=dy+O(y^2)`$ and $`p=\binom dr y^r(1+O(y))`$. Thus $`tp/V\to0`$ for $`r\ge2`$ and $`g'<0`$ near $`r`$. The unique zero $`t_*>T`$ is simple, and $`g''(t_*)<0`$. For $`r=1`$ the exact formula $`g=t^2/(1+t)`$ is strictly increasing on $`0<t<1`$.

## Fixed bounded slack in the original fibers

Now fix $`d,r`$ and an integer $`s\ge0`$. Consider a near-balanced margin vector of total $`nr-s`$, with column sums differing by at most one. Set

$$
E(s)=\mathrm{E}M-\frac{ns}{n+s-1},
$$

where $`M`$ is the number of positive row deficits. The finite family of row-deficit profiles of total $`s`$ consists of one profile type with $`M=s`$, one with $`M=s-1`$ if $`s,r\ge2`$, and the types with $`M\le s-2`$. Given the positions and sizes of the deficient rows, generate each row as an independent uniform subset of its prescribed size. Conditional on the deficient row vectors, the column constraint for the $`n-M`$ remaining uniform size-$`r`$ rows is a transverse lattice atom with bounded centered displacement, uniformly over phases.

After dropping the last coordinate, differences of size-$`r`$ row vectors generate $`\mathbb Z^{d-1}`$ by exchanging each column with the last one. Thus the transverse covariance is nonsingular and its characteristic function has modulus one only at zero on the torus. The ordinary fixed-dimensional Fourier expansion for a bounded displacement gives the atom $`K(n-M)^{-(d-1)/2}(1+O_{d,r,s}(n^{-1}))`$. For the relative error here, rescale the central integral by $`\sqrt{n-M}`$. Its only term of order $`(n-M)^{-1/2}`$ beyond the Gaussian is odd, arising from the third cumulant and the linear displacement. It integrates to zero on a symmetric box. The next terms are bounded by a fixed polynomial times the Gaussian divided by $`n-M`$. A fixed neighborhood gives the Gaussian tail control, and the rest of the torus is exponentially small. This argument is uniform over the finitely many bounded displacements at fixed $`d,r,s`$.

The ratio of the one-double-deficit profile to the all-single-deficit profile is therefore

$$
\frac{n\binom{n-1}{s-2}}{\binom ns}
\frac{\binom d{r-2}\binom d r}{\binom d{r-1}^2}
(1+O(n^{-1}))
=b\frac{s(s-1)}{n-s+1}(1+O(n^{-1})).
$$

All profiles with $`M\le s-2`$ have total relative mass $`O(n^{-2})`$ from the count of labeled row choices, with the row weight ratios and transverse factor bounded uniformly. Hence $`s-\mathrm{E}M=bs(s-1)/n+O(n^{-2})`$ and

$$
E(s)=(1-b)\frac{s(s-1)}n+O_{d,r,s}(n^{-2}).
$$

For $`s=0,1`$ the excess is exactly zero. For $`r=1`$ all positive deficits are single and the excess is exactly $`s(s-1)/(n+s-1)`$. For any fixed $`s\ge1`$, subtraction gives $`E(s+1)-E(s)=2(1-b)s/n+O(n^{-2})>0`$ for sufficiently large $`n`$, independently of the two near-balanced phases.

## Scope of the finite application

Signed monotonicity for the original fibers, once transferred uniformly for moving slack, removes the loss term $`X`$ from the earlier same-phase consecutive-availability comparison. This extends that switching method past its former $`s=O(\sqrt n)`$ small-slack limit at fixed $`d,r`$. For $`\sqrt n\ll s\ll n`$ the resulting lower bound has order $`d^2/s`$, better than the orientation estimate of order $`d/n`$ and weaker in constant than the separate mesoscopic coefficient asymptotic already in the repository. At $`s/n`$ fixed and positive the switching bound is still of order $`1/n`$ in fixed dimension and cannot by itself reach the factor-four sign cutoff. This is a result about finite availability in the original fibers and its eventual behavior at fixed dimension. It supplies no uniform transition sign result when the dimension grows with height. The scalar unimodality predicts the sign away from its critical mean. A finite assertion at or very close to the critical mean needs control of higher-order corrections.
