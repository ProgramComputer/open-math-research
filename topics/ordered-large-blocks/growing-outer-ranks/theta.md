# A transition in the exterior roots of ordered partition polynomials

A partial theorem for issue #1. Let $`O_{n,j}`$ count ordered set partitions of $`[n]`$ by the number of blocks of size at least $`j`$. Write $`n=mj+s`$, $`0\le s<j`$. Number the complex roots of the reversed polynomial $`D_n(y)=y^m O_{n,j}(1/y)/n!`$ in increasing order of modulus, counting multiplicity and giving the smallest modulus rank zero.

Consider a sequence with $`m,j,h\to\infty`$, $`h=o(m)`$. At index $`h`$ define the saddle radius $`r`$ and standard deviation $`\sigma`$ below. Suppose $`j/\sigma\to a`$ with $`0<a<\infty`$. Then for each fixed integer $`b`$, the reversed root of rank $`h+b`$ is eventually simple and negative. At equal degrees the old root of rank $`h+b`$ has modulus strictly between the new moduli of ranks $`h+b-1`$ and $`h+b`$. At a degree increase it lies strictly between new ranks $`h+b`$ and $`h+b+1`$. The modulus ratio between successive old roots tends to $`\exp(a^2)`$. The result concerns ranks among all complex zeros.

## Renewal representation and a centered tilt

Use $`S_j(x)=\sum_{i=1}^{j-1}x^i/i!`$, $`S_j(\rho)=1`$, $`T(z)=(1-S_j(\rho z))^{-1}`$, $`U(z)=\sum_{i\ge0}j!(\rho z)^i/(i+j)!`$, $`V=T U`$. Decomposing at the large blocks gives, with $`p_t=m-t`$, $`e_t=s+tj`$, $`F_p=T V^p`$, the exact coefficient

$$
d_t=[y^t]D_n(y)=(j!)^{-p_t}\rho^{-e_t}[z^{e_t}]F_{p_t}(z).
$$

For completeness, an ordered sequence with $`p`$ marked large blocks has $`p+1`$ gaps of small blocks. After the $`p`$ forced groups of $`j`$ labels are removed from the exponential generating function the remaining factors are precisely $`T^{p+1}U^p`$. For a fixed $`R>1`$, both $`T,V`$ have coefficient sequences of the form $`c_j+O(R^{-i})`$ with $`c_j`$ bounded above and below by positive constants (a different $`c_j`$ for each function). Indeed $`(1-z)T`$ and $`U`$ are uniformly analytic on a slightly larger disk, since $`\rho\to\log 2`$ and the removable divided difference $`(1-S_j(\rho z))/(1-z)`$ converges to $`(2-e^{(\log2)z})/(1-z)`$ there without zeros for $`R`$ close to one. Finite-index positive limits give uniform upper and positive lower bounds on *every* coefficient, using the pole estimate at high indices.

At $`0<r<1`$ tilt each coefficient sequence of $`T,V`$ by $`r^i`$ and normalize to get an integer-valued variable. Let $`X_{p,r}`$ be the independent sum of one $`T`$ variable and $`p`$ copies of the $`V`$ variable, and let $`L_{p,r}(x)`$ be its mass at the integer $`x`$, extended by zero off the support. Write $`\mu_V`$ for one tilted $`V`$ mean. Choose $`r`$ to give $`X_{p_h,r}`$ the mean $`e_h`$ and let $`\sigma^2`$ be its variance. The mean increases strictly from zero to infinity because its derivative in $`\log r`$ is the variance. Define

$$
\omega_t(r)=(j!)^{-p_t}(\rho r)^{-e_t}F_{p_t}(r),\qquad K(r)=\omega_{t+1}(r)/\omega_t(r).
$$

$`K(r)`$ is independent of $`t`$ and $`d_t=\omega_t(r)L_{p_t,r}(e_t)`$. A tilted single variable has mass between fixed positive multiples of the geometric law $`(1-r)r^i`$. Its mean is comparable to $`r/(1-r)`$ and its variance to $`\kappa=r/(1-r)^2`$ (use half the mean squared difference of two independent copies for the lower bound). Its third absolute centered moment is $`O(r/(1-r)^3)`$. In particular $`\mu_V/j=O((h+1)/m)=o(1)`$. The variance $`\sigma^2`$ is comparable to $`m\kappa`$ and $`mr\to\infty`$: if $`r\to0`$, $`mr`$ is comparable to $`e_h\to\infty`$.

When $`e_h/m\to\infty`$, the mean bound forces $`r\to1`$. The uniformly analytic and nonzero numerators in $`T`$ and $`V`$ have bounded first and second log-radius derivatives. Each summand therefore has mean $`r/(1-r)+O(1)`$ and variance $`r/(1-r)^2+O(1)`$ from the simple pole part. As $`p_h\sim m`$ and $`e_h\sim jh`$, this gives

$$
\sigma\sim\frac{e_h}{\sqrt m}\sim\frac{jh}{\sqrt m},\qquad\frac{j}{\sigma}\sim\frac{\sqrt m}{h}.
$$

In particular, if $`j/\sqrt m\to\infty`$ and $`h/\sqrt m\to c\in(0,\infty)`$, then $`e_h/m\to\infty`$ and the theorem applies with $`a=1/c`$.

## Two local limit estimates

For $`p/m\to1`$ write $`b_{p,r}=\mathbb E X_{p,r}`$ and $`\sigma_p^2=\mathrm{Var}(X_{p,r})`$. For integer targets with $`(x-b_{p,r})/\sigma_p\to u`$,

$$
\sigma_p L_{p,r}(x)\longrightarrow\phi(u),\qquad
\sigma_p^2\Delta L_{p,r}(x)\longrightarrow-u\phi(u),\qquad
\Delta L(x)=L(x+1)-L(x).
$$

Here $`\phi(u)=e^{-u^2/2}/\sqrt{2\pi}`$. The sum of third absolute centered moments divided by $`\sigma_p^3`$ is $`O((mr)^{-1/2})`$. Thus the centered characteristic function at $`\theta/\sigma_p`$ tends to $`e^{-\theta^2/2}`$. Fourier inversion for the difference inserts $`e^{-i\theta}-1`$, which after scaling tends to $`-i\theta`$ and differentiates the limiting Gaussian density. The required integrable tails follow as follows. If $`G`$ is the geometric law with parameter $`r`$, then for either single variable $`Z`$,

$$
1-|\mathbb E e^{i\theta Z}|^2
\ \ge c(1-|\mathbb E e^{i\theta G}|^2)
=c\frac{4r\sin^2(\theta/2)}{(1-r)^2+4r\sin^2(\theta/2)} .
$$

This follows by comparison in the double expectation of $`1-\cos(\theta(Z-Z'))`$. When $`r`$ is bounded away from one the product of the characteristic functions is bounded by $`\exp(-c(p+1)\kappa\theta^2)`$ throughout $`[-\pi,\pi]`$. For $`r\to1`$ the same estimate holds on $`|\theta|\le M(1-r)`$ for each fixed $`M`$, with $`c`$ depending only on $`M`$. Outside this arc each characteristic function is at most $`C(1-r)/|\theta|`$, by the pole representation and the uniform analytic numerator. Choose $`M>2C`$. For $`p\ge3`$ the integral over this remaining arc against $`|\theta|^b`$, $`b=0,1`$, is $`O((1-r)^{b+1}2^{-p})`$. This comparison supplies dominated tails after rescaling in both inversion integrals.

The same estimates without centering give, uniformly in the integer $`x`$, for $`p\ge3`$,

$$
L_{p,r}(x)\le C((p+1)\kappa)^{-1/2},\qquad
|\Delta L_{p,r}(x)|\le C((p+1)\kappa)^{-1}.
$$

They also hold for $`p=0,1,2`$ when $`r`$ is bounded away from one. For $`r\to1`$ the first inequality still holds for these $`p`$ by the geometric comparison and convolution. For $`p=1,2`$ the $`\ell^1`$ norm of the first difference of a single tilted variable is $`O(1-r)`$, including the edge at zero. This follows by writing its unnormalized coefficients as $`c_j+O(R^{-i})`$ and summing the absolute differences after tilting. Convolution with a second variable of supremum norm $`O(1-r)`$ gives the second bound. At $`p=0`$ its difference at the actual target $`x=e_m`$ is $`O((1-r)^2+(1-r)R^{-e_m})`$. In our application $`1-r\ge c/j`$ when $`r\to1`$, since $`e_h\le mj`$ and the mean is comparable to $`m r/(1-r)`$. Thus $`R^{-e_m}=o(1-r)`$ even when $`j`$ grows faster than every exponential function of $`m`$.

## The limiting series at a balance

Write $`y_h=d_h/d_{h+1}`$ and normalize the polynomial as $`B(z)=D_n(y_hz)/(d_h(y_hz)^h)`$. At the common tilt $`r`$, the coefficient of $`z^\ell`$ is

$$
(y_hK(r))^\ell\frac{L_{p_{h+\ell},r}(e_{h+\ell})}{L_{p_h,r}(e_h)}.
$$

Its standardized target differs from the anchor by $`\ell(j+\mu_V)/\sigma\to a\ell`$ for fixed $`\ell`$. Thus $`y_hK(r)\to e^{a^2/2}`$ and this coefficient tends to $`q^{\ell(\ell-1)/2}`$ for $`q=e^{-a^2}`$.

For the adjacent row write $`I=1`$ when $`s=j-1`$, and $`I=0`$ otherwise. The Laurent coefficients of $`(\rho r)y^{-I}D_{n+1}(y)-D_n(y)`$ in degree $`t`$ are exactly $`\omega_t(r)\Delta L_{p_t,r}(e_t)`$, for $`0\le t\le m`$. At a carry this includes $`t=-1`$ with $`p_{-1}=m+1`$, $`e_{-1}=-1`$. Indeed $`L(-1)=0`$, $`L(0)=1/F_{m+1}(r)`$ for that sum, giving the required extra term $`(\rho r)(j!)^{-(m+1)}y^{-1}`$. Normalize this contrast by $`\sigma/(d_h(y_h z)^h)`$ at $`y=y_hz`$ to obtain $`H(z)`$. The second local limit gives the coefficient limit $`-a\ell q^{\ell(\ell-1)/2}`$.

We justify both Laurent limits on every compact annulus. Fix a signed integer $`b`$. Recenter the tilt at $`h+b`$ by solving for $`r_b`$ as before. Along $`\log r+\lambda/\sigma`$ for bounded $`\lambda`$, the variances of $`X_{p_{h+b}}`$ divided by $`\sigma^2`$ tend uniformly to one. At $`\lambda=0`$ adding or removing $`|b|`$ variables changes the relative variance by $`O_b(1/m)`$. Along the interval, $`r'/r\to1`$ and $`(1-r')/(1-r)\to1`$ (near one use $`(1-r)\sigma\asymp\sqrt m`$). Integrating the third cumulant bound $`O(mr/(1-r)^3)`$ for change of variance gives relative error $`O((mr)^{-1/2})`$. Integration once more and strict monotonicity give $`\sigma\log(r_b/r)\to ab`$, since the target-mean difference at $`r`$ is $`b(j+\mu_V)`$. In particular the variance at the new tilt is asymptotic to $`\sigma^2`$ and $`\sigma|r/r_b-1|=O_b(1)`$. Centering at $`h+b`$ now gives

$$
y_h K(r_b)=\frac{L_{p_h,r_b}(e_h)}{L_{p_{h+1},r_b}(e_{h+1})}\longrightarrow \exp(a^2(1-2b)/2),\qquad
L_{p_h,r_b}(e_h)\asymp_b \sigma^{-1}.
$$

For a given annulus $`0<c_1\le |z|\le c_2`$, choose a large positive $`b`$ so $`|y_hK(r_b)z|<1/2`$ throughout, and a large negative $`b`$ so the same modulus exceeds $`2`$. Use the former on $`\ell\ge0`$, the latter on $`\ell<0`$. For the contrast, changing tilt in its numerator replaces $`\Delta L`$ by $`(r/r_b)\Delta L+(r/r_b-1)L`$ at the new tilt. Since $`\kappa(r_b)\asymp\sigma^2/m`$, the uniform bounds above dominate both series termwise by $`C_b2^{-|\ell|}(1+m/(p_t+1))`$. If $`\ell\le m/2`$, this ratio is bounded for large $`m`$; if $`\ell>m/2`$ it is $`O(1+\ell)`$. The bound at the possible left index $`t=-1`$ uses $`p_t=m+1`$ and holds for every target. We have proved compact uniform convergence in $`\mathbb C^\times`$:

$$
B(z)\longrightarrow \Theta_q(z)=\sum_{\ell\in\mathbb Z}q^{\ell(\ell-1)/2}z^\ell,\qquad
H(z)\longrightarrow -a z\Theta_q'(z).
$$

## Rank and strictness

Jacobi's triple product factors $`\Theta_q`$ as $`\prod_{v\ge1}(1-q^v)(1+q^{v-1}z)(1+q^v/z)`$. On $`|z|=q^{1/2}`$ the winding number is zero; on $`|z|=q^{-1/2}`$ it is one. On the first circle each varying factor traces a circle about $`1`$ of radius less than one. On the second the factor $`1+z`$ is the only one with positive winding. Uniform convergence and the argument principle, restoring the power $`z^h`$, give precisely $`h`$ and $`h+1`$ roots of $`D_n(y_h z)`$ inside the two circles. The intervening root tends to $`-1`$, is simple, and is real by conjugation. Repeating at $`h+b`$ gives the adjacent ranks and $`y_{h+1}/y_h\to q^{-1}`$ from the same coefficient limits. [Jacobi triple product, DLMF 20.5.9](https://dlmf.nist.gov/20.5.E9)

For the new row its corresponding index is $`h+I`$, with the same number of summands as the old anchor and target $`e_h+1`$. Its new saddle has log-radius change $`O(1/\sigma^2)`$ by the variance estimate, so it satisfies the same hypotheses. Its corresponding balance divided by $`y_h`$ tends to one by the first local limit at targets $`e_h+1,e_{h+1}+1`$. At the actual negative old root $`y=y_h z`$ we have $`z\to-1`$ and $`H(z)\to a\Theta_q'(-1)>0`$ by the product. Hence $`D_{n+1}(y)`$ has sign $`(-1)^{h+I}`$. In this annulus the unique new root is simple and negative. To read its side from this sign, the number of new negative real roots before the annulus has parity $`h+I`$ since nonreal roots inside the smaller circle occur in conjugate pairs and positive coefficients exclude positive roots. The new polynomial is positive at zero. Thus its sign at the old root places the old modulus strictly below the new modulus with rank $`h+I`$. The previous new rank is strictly below the old modulus by the limiting factor $`q`$, which finishes the proof.
