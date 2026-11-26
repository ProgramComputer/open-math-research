# Balancing sparse row supports at a column quota of order $`d`$

Let $`d\to\infty`$ and let a finite list of integers $`s_1,\ldots,s_n\in[0,d]`$ have sum $`dk`$, where $`k`$ is an integer with $`k/d\to\beta\in(0,\infty)`$. Assume $`\max_i s_i=o(d)`$. Choose independent uniform $`s_i`$-subsets of $`[d]`$ as the row supports and write $`B`$ for the probability that all columns have sum $`k`$. Set $`\nu=(d-1)/2`$ and

$$
a_s=\frac{s(d-s)}{d(d-1)},\qquad \Lambda=\sum_i a_{s_i}.
$$

Then, uniformly along every such sequence of profiles,

$$
B=\sqrt d\thinspace (2\pi\Lambda)^{-\nu}
\exp\negthinspace \left(-\frac{1}{12\beta}\right)(1+o(1)).
$$

Zero rows have no effect. One may replace $`1/\beta`$ in the exponential by $`d/k`$. No distributional assumption on the row-size list is needed. In particular $`\Lambda/k\to1`$ since $`\max s_i=o(d)`$. We keep the exact $`\Lambda`$ in the power of order $`d`$.

The smaller range $`\max_i s_i=o(d^{1/3})`$ already follows from Corollary 5.2 of Greenhill, McKay and Wang by Stirling expansion of the binomial normalizer. [Version of record](https://doi.org/10.1016/j.jcta.2005.03.005)

## Angular coordinates and localization

For a real angle vector $`y`$ of zero sum let $`Q_j=\sum_i y_i^j`$, $`M_y=\max_i|y_i|`$, and, for a uniform $`s`$-subset $`I`$, $`L_s=\sum_{i\in I}y_i`$. Pinned-coordinate Fourier inversion for the first $`d-1`$ columns gives the integral of $`\prod_i\mathbb E\exp(iL_{s_i})`$ on the quotient by common angular shifts, in zero-sum lifts. The centered integrand is periodic on the projected lattice since the total degree is $`dk`$. Its Euclidean covolume is $`(2\pi)^{d-1}/\sqrt d`$, from the determinant $`1/d`$ of the Gram matrix for the first $`d-1`$ projected standard basis vectors. Thus the Gaussian approximation with precision $`\Lambda`$ has normalized mass $`B_0=\sqrt d(2\pi\Lambda)^{-\nu}`$.

The global localization lemma bounds the absolute contribution outside a common arc of arbitrarily small fixed width and bounded squared norm by $`o(B_0)`$. More explicitly, first choose a sufficiently large fixed dispersion cutoff depending on $`\beta`$. Outside it, the integral is negligible. Inside it, the integral on configurations with two coordinates separated by more than any fixed small angle is again negligible. In the remaining common arc take the unique short lifts with zero mean. The chord-dispersion cutoff bounds $`Q_2`$ by a fixed $`L`$, since chord and angle distances are comparable in this arc. Conversely the local domain contains a cube of small coordinate width intersected with a ball $`Q_2\le L_1`$ for a fixed $`L_1>1/\beta`$, by taking the initial cutoff large enough, since dispersion is at most $`Q_2`$. Let $`\mathcal A`$ denote the actual retained local domain. Its indicator lies between the indicators of the inner and outer regions just described, both of asymptotically full Gaussian mass. In the Gaussian expectation below, the integrand is multiplied by $`\mathbf 1_{\mathcal A}`$. Uniform integrability of the modulus on the outer region makes the omitted Gaussian mass negligible. This comparison uses absolute errors, so applies to the complex integrand. Injectivity in the quotient follows because the difference of pairwise lifted angles between any two such representations has absolute value $`<2\pi`$. [Proof of global localization](sparse-fixed-profile-global-localization.md)

## Uniform logarithmic expansion for one row

For real $`y`$ with zero sum, $`K_s(z)=\log\mathbb E e^{zL_s}`$ has a single-valued analytic branch through $`K_s(0)=0`$ in $`|z|<c/M_y`$, for an absolute $`c>0`$. The case $`M_y=0`$ is immediate. In that disk each $`e^{zy_i}`$ has positive real part. For variables $`u_i`$ in the open right half-plane, $`e_s(u)`$ is nonzero: the roots of $`\prod_i(z+u_i)`$ and of all its derivatives lie in the open left half-plane by Gauss–Lucas, and its derivative of order $`d-s`$ at zero is $`(d-s)!e_s(u)`$. Apply this with $`u_i=e^{zy_i}`$. With $`s=o(d)`$ we can assume $`s\le d/2`$. For $`|z|M_y\le c`$, elementary symmetric mean comparison on the positive reals gives

$$
\log|\mathbb Ee^{z L_s}|\le s\log\left(d^{-1}\sum_j e^{(\mathrm{Re}\thinspace z)y_j}\right)
\le C a_s |z|^2 Q_2 .
$$

The first inequality is the elementary symmetric mean bound $`e_s(u)/\binom ds\le (\sum u_i/d)^s`$, also obtainable by the sampling-without-replacement comparison. The second uses $`\sum y_j=0`$ and $`s/d\le2a_s`$. Borel–Carathéodory applied on two concentric subdisks bounds the absolute logarithm by $`C a_s Q_2/M_y^2`$ on $`|z|\le c' / M_y`$. Cauchy's estimates for the resulting power series show that at $`z=i`$ its remainder after degree four is $`O(a_s Q_2 M_y^3)`$, if $`M_y\le\eta`$ for a sufficiently small absolute $`\eta`$.

For completeness, with $`p_j=(s)_j/(d)_j`$ (falling factorials), the second, third and fourth cumulants of $`L_s`$ are respectively

$$
a_s Q_2,\qquad \gamma_s Q_3,\qquad A_sQ_4+3B_sQ_2^2,
$$

where
$`\gamma_s=a_s(d-2s)/(d-2)`$, $`A_s=p_1-7p_2+12p_3-6p_4`$, and $`B_s=(s)_2(d-s)_2/(d)_4-a_s^2`$. These identities follow by expanding the moments using the inclusion probabilities for distinct indices and $`Q_1=0`$, then subtracting three times the squared second moment. For instance the coefficients of $`Q_4,Q_2^2`$ in the raw fourth moment are $`A_s,3(p_2-2p_3+p_4)`$, and the latter parenthesis equals $`(s)_2(d-s)_2/(d)_4`$ by requiring two prescribed elements inside and two outside a random subset. At positive $`s\le\max s_i=o(d)`$, uniformly,

$$
\gamma_s/a_s=1+o(1),\qquad A_s/a_s=1+o(1),\qquad d B_s/a_s=-1+o(1).
$$

Indeed $`p_j\le (s/d)^j`$ and $`a_s\sim s/d`$ in this range. For the last identity write $`u=s(d-s)`$ and observe that $`B_s/a_s=(u-d+1)/[(d-2)(d-3)]-u/[d(d-1)]`$. The error after multiplying by $`d`$ and adding one is $`O(1/d+s/d)`$. Zero-size rows have zero cumulants.

## Integrating the correction

Let $`Y_i=(Z_i-\overline Z)/\sqrt\Lambda`$ with $`Z_i`$ independent standard normals, giving the real isotropic Gaussian in the zero-sum hyperplane. Write $`\Gamma=\sum\gamma_s`$, $`A=\sum A_s`$ and $`B'=\sum B_s`$, summing over all rows. The logarithmic correction to the Gaussian in the integral on the retained region is

$$
-\frac{i\Gamma}{6}Q_3+\frac A{24}Q_4+\frac{B'}8 Q_2^2
+O(\Lambda Q_2M_y^3).
$$

Under this Gaussian, $`Q_2\to1/\beta`$ in probability, $`\Lambda Q_4\to3/\beta`$ in probability, and $`M_Y=O_{\mathbb P}(\sqrt{\log(d+1)/\Lambda})`$. The first two limits follow by the law of large numbers for the centered independent normal coordinates and $`\Lambda/d\to\beta`$. Hence the quartic part converges to $`3/(24\beta)-1/(8\beta)=0`$. The remainder also converges to zero in probability. For the cubic, the centered sum $`d^{-1/2}\sum_i(Z_i-\overline Z)^3`$ differs from $`d^{-1/2}\sum_i(Z_i^3-3Z_i)`$ by a term tending to zero in probability: expand and use $`\overline Z=O_{\mathbb P}(d^{-1/2})`$ and $`\sum_i(Z_i^2-1)=O_{\mathbb P}(\sqrt d)`$. The iid central limit theorem gives limit $`N(0,6)`$, the variance being the third Hermite polynomial's second Gaussian moment. Since $`\Gamma/\Lambda\to1`$, $`\Gamma Q_3`$ converges to $`N(0,6/\beta)`$.

The exponentials of the corrections on the retained region are uniformly integrable. The cubic is imaginary. For any fixed doubled constants it suffices by Cauchy–Schwarz to bound truncated exponential moments of $`\Lambda Q_4`$ and $`\Lambda L M_Y^3`$ separately, since $`|B'|Q_2^2=O_\beta(L^2)`$. For the first, use independent $`X_i=Z_i/\sqrt\Lambda`$ and $`Y=X-\overline X`$. The event $`|\overline X|\le\eta`$ has probability tending to one independently of $`Y`$. On that event and $`M_Y\le\eta`$, $`|X_i|\le2\eta`$ and $`\sum Y_i^4\le16\sum X_i^4`$. With $`\eta`$ sufficiently small each of the resulting one-dimensional truncated expectations is at most $`1+C/\Lambda`$: use $`e^v-1\le ve^v`$ and absorb $`C\Lambda x^4`$ in a quarter of the quadratic exponent. The product is bounded as $`d/\Lambda=O(1)`$.

For the second term choose $`\eta`$ still smaller, depending on $`L`$, so $`C L x^3\le x^2/8`$ for $`x\le\eta`$. Each $`Y_i`$ has variance at most $`1/\Lambda`$, hence $`\mathbb P(M_Y>x)\le2d e^{-\Lambda x^2/2}`$. Below $`x_0=\sqrt{K\log(d+1)/\Lambda}`$ the exponent $`C\Lambda L x_0^3=o(1)`$. Above $`x_0`$, integrating the tail bound against $`3 C\Lambda L x^2 e^{C\Lambda L x^3}`$ gives $`o(1)`$ for sufficiently large fixed $`K`$, also accounting for the boundary term at $`x_0`$. This proves the asserted bounded exponential moments even after doubling constants.

The retained region has Gaussian probability tending to one. Uniform integrability and convergence in distribution of the displayed correction give the limiting Gaussian expectation of $`\exp(-iZ/6)`$ for $`Z\sim N(0,6/\beta)`$. This is $`\exp(-1/(12\beta))`$. The Haar normalization and the negligible global tail prove the formula. As a check, when all nonzero rows have size one, the exact balance probability is $`(dk)!/(d^{dk}(k!)^d)`$, and Stirling's formula gives the same exponential correction with $`\Lambda=k`$.
