# Local transverse Gaussian estimate for fixed row cap

Fix $`r\ge1`$, let $`d\to\infty`$, take $`u>0`$, and put $`v=ue^{i\tau}/d`$. Use the row function
$`R_\tau(y)=\sum_{|S|\le r}v^{|S|}\exp(i\sum_{i\in S}y_i)`$ on the Euclidean hyperplane $`V=\{y\in\mathbb R^d:\sum_i y_i=0\}`$. Put $`H=R_\tau(0)`$ and $`\lambda=\min(u,1)`$. All constants below can depend on fixed $`r`$.

For some fixed $`\eta,\tau_0>0`$, uniformly on $`\max_i|y_i|\le\eta`$, $`|\tau|\le\tau_0`$ and all $`u>0`$, the logarithm through zero satisfies

$$
\log(R_\tau(y)/H)=-\tfrac12 a\sum_i y_i^2-\tfrac i6 c\sum_i y_i^3+E_4(y),\qquad
|E_4(y)|\le C\lambda d^{-1}\sum_i y_i^4.
$$

Here $`a=a_1-a_2`$ and $`c=a_1-3a_2+2a_3`$, where $`a_j`$ is the complex normalized weight of a subset containing any fixed $`j`$-set. In particular $`\mathrm{Re}(a)\asymp\lambda/d`$, $`|\mathrm{Im}(a)|\le C\lambda|\tau|/d`$, $`|c|\le C\lambda/d`$, and $`|\mathrm{Im}(c)|\le C\lambda|\tau|/d`$.

The local integral over the stated cube in $`V`$, with Euclidean measure, obeys

$$
\int_{V,\ \max_i|y_i|\le\eta} R_\tau(y)^n\thinspace dy
=H^n\left(\frac{2\pi}{na}\right)^{(d-1)/2}
\left[1+O\left(\frac{d}{\sqrt{n\lambda}}+\frac{d^2}{n\lambda}\right)\right]
$$

as long as $`n\lambda/d^2\to\infty`$ and $`d\tau^2=O(1)`$. Powers are continued from positive $`a`$. This includes the two principal phases $`\tau=\pm\pi/d`$ when $`u`$ stays in a positive compact and $`n\ge c d^2\log n`$. The assertion concerns this integral only. A global estimate and phase comparison are needed to identify the dominant contributions to the polynomial.

## Expansion

Give each subset $`S`$ the normalized weight $`v^{|S|}/H`$ and write $`L_S=\sum_{i\in S}y_i`$. The positivity of the real radial coefficients and the bounded support of the sizes give $`|H|\ge\tfrac12 H|_{\tau=0}`$ for small enough $`\tau_0`$. Absolute complex weights are at most twice their $`\tau=0`$ counterparts. The real size distribution has $`\mathbb P(|S|\ge1)\asymp\lambda`$, uniformly in $`u>0`$, because the nonempty contribution is a polynomial in $`u`$ of degree $`r`$ with coefficients bounded above and below for large $`d`$. Its moments of positive order up to any fixed order are of size $`\asymp\lambda`$. This also controls derivatives of inclusion weights in $`\tau`$: $`|a_j|+|\partial_\tau a_j|\le C\lambda/d^j`$ for $`1\le j\le3`$. At zero phase $`a_1\asymp\lambda/d`$, $`a_2=O(\lambda/d^2)`$, and $`a,c`$ are real. These facts imply the asserted bounds for small $`\tau_0`$.

Weighted moments of $`L_S`$ are computed by exchangeability. The mean vanishes on $`V`$. The second moment is $`(a_1-a_2)\sum_i y_i^2`$. In the cubic, $`\sum_{i\ne j}y_i^2 y_j=-\sum_i y_i^3`$ and $`\sum_{i,j,k\ {\rm distinct}}y_i y_j y_k=2\sum_i y_i^3`$, giving the cubic coefficient. Weighted absolute fourth moments are at most $`C\lambda d^{-1}\sum_i y_i^4`$ by $`|L_S|^4\le r^3\sum_{i\in S}|y_i|^4`$. Taylor's bound for $`e^{iL_S}`$ gives the expansion through degree three. The logarithm exists in the stated cube because $`|R_\tau/H-1|\le C\lambda d^{-1}\sum_i y_i^2\le C\eta^2`$ using the vanishing first moment. The square of this bound is $`O(\lambda d^{-1}\sum_i y_i^4)`$ by Cauchy–Schwarz and $`\lambda\le1`$. The real part of the cubic term is at most $`C\lambda|\tau|d^{-1}|\sum_i y_i^3|`$.

## Integrated error

Set $`\alpha=\mathrm{Re}(a)`$ and $`\sigma^2=(n\alpha)^{-1}\asymp d/(n\lambda)`$. A centered Gaussian $`Y`$ on $`V`$ of covariance $`\sigma^2 I_V`$ has coordinates $`Y_i=Z_i-\overline Z`$, with $`Z_i`$ independent $`N(0,\sigma^2)`$. Write $`C_\eta`$ for the cube and $`B(y)=-inc\sum_i y_i^3/6+nE_4(y)`$. The real Gaussian normalization divided by the absolute complex Gaussian normalization is $`(|a|/\alpha)^{(d-1)/2}\le\exp(O(d\tau^2))`$. The Gaussian mass outside the cube is at most $`2d\exp(-c_0\eta^2 n\lambda/d)`$, negligible compared with either displayed error scale.

For the unweighted $`L^2`$ norm of the cubic, the coordinate covariances are $`q_{ij}=\sigma^2(\delta_{ij}-1/d)`$. Wick's formula gives $`\mathbb E Y_i^3Y_j^3=9q_{ii}q_{jj}q_{ij}+6q_{ij}^3`$. Since all diagonal entries agree and $`\sum_{ij}q_{ij}=0`$, the linear terms cancel and $`\|\sum_iY_i^3\|_2=O(\sqrt d\,\sigma^3)`$. Also $`\|\sum_iY_i^4\|_2\le C d\sigma^4`$ by the eighth moment and the triangle inequality. Therefore

$$
\Vert B(Y)\mathbf 1_{C_\eta}\Vert _2
=O(d/\sqrt{n\lambda}+d^2/(n\lambda)).
$$

To control the exponential in $`|e^B-1|\le |B| e^{(\mathrm{Re} B)_+}`$, bound $`2(\mathrm{Re} B)_+`$ by $`C(n\lambda/d)(|\tau|\sum_i|y_i|^3+\sum_i y_i^4)`$. The event $`|\overline Z|\le\eta`$ has probability tending to one independently of $`Y`$. On its intersection with $`C_\eta`$, one has $`|Z_i|\le2\eta`$ and $`\sum_i|Y_i|^j\le 2^j\sum_i|Z_i|^j`$ by the triangle inequality for powers and Jensen's inequality. Thus the expectation of the exponential over $`C_\eta`$ is at most a bounded factor times the product of $`d`$ identical one-dimensional truncated expectations. If $`X\sim N(0,\sigma^2)`$ and $`L(x)=C'\sigma^{-2}(|\tau||x|^3+x^4)`$, the single-factor bound is

$$
\mathbb E[\mathbf 1_{|X|\le2\eta}e^{L(X)}]
\le 1+C''(|\tau|\sigma+\sigma^2).
$$

Indeed, after choosing small enough fixed $`\eta`$, $`L(x)\le x^2/(4\sigma^2)`$ on the interval. Use $`e^{L(x)}-1\le L(x)e^{L(x)}`$ there and integrate against the Gaussian, with variance at most doubled. The product is $`\exp(O(|\tau|d^{3/2}/\sqrt{n\lambda}+d^2/(n\lambda)))`$, bounded under the hypotheses. Cauchy–Schwarz now gives the claimed error after integrating the pointwise exponential difference and comparing normalizations.

## Moving radius

The proof holds uniformly for $`u\to0`$ provided $`nu/d^2\to\infty`$, and for arbitrary $`u\to\infty`$ under $`n/d^2\to\infty`$. In the latter case the transverse variance stays of order $`1/d`$, even though the size distribution concentrates at $`r`$ and its radial variance can vanish. Consequently the local dimension estimates persist while a separate global argument in the radial/diagonal phase can lose localization. The proof gives no uniform vanishing-relative-error conclusion in the small-$`u`$ range $`nu=O(d^2)`$.
