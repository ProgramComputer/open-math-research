# Direct cubic-phase lower bound for nearly homogeneous row profiles

The cubic-phase estimate uses its full Gaussian second moment, including the linear component.

**Proposition.** Let $`n\ge10^{30}`$, $`n/4\le d\le n`$, $`x=k/n\in[.3,.7]`$, and let integers $`\ell_1,\dots,\ell_n`$ have sum $`dk`$ and satisfy $`|\ell_i/d-x|\le10^{-6}`$. Select each row independently as a uniform $`\ell_i`$-subset of $`[d]`$. Its probability of equal column margins $`k`$ is at least

$$
\frac{\sqrt d}{200}\thinspace{}[2\pi n x(1-x)]^{-(d-1)/2}.
$$

In particular the assertion covers the homogeneous profiles and profiles with $`|\ell_i/d-x|\le1/d`$. The explicit cutoff is deliberately loose.

## Joint margin integral and covariance

Take independent Bernoulli cells with row parameters $`p_i=\ell_i/d`$, put $`v_i=p_i(1-p_i)`$ and $`A=\sum_i v_i`$. All $`v_i\ge1/5`$. Write $`F`$ for the centered joint row-and-column characteristic product, with cell argument $`\phi_i+\theta_j`$. The centered margins are integral, so the full joint characteristic product is periodic and invariant under shifting the row angles by $`t`$ and column angles by $`-t`$. The probability of all margins is its normalized torus integral, which equals the integral on the section $`\theta_d=0`$.

The quadratic form on that section is $`Q=\sum_{ij}v_i(\phi_i+\theta_j)^2`$. Its matrix has row block $`\mathrm{diag}(dv_i)`$, column block $`AI_{d-1}`$ and cross column $`(v_i)_i`$. The Schur complement is $`A(I-\mathbf1\mathbf1^{\mathsf T}/d)`$, with determinant $`A^{d-1}/d`$. The normalized Gaussian integral is therefore

$$
G=B_0(2\pi A)^{-d/2}\sqrt{2\pi d A},\qquad
B_0=\prod_i (2\pi d v_i)^{-1/2}.
$$

Use the gauge $`\sum_j\theta_j=0`$. Then the row angles are unrestricted and the column angles lie in the centered hyperplane. The change of gauge preserves all cell arguments and the normalized Gaussian law. The quadratic form splits into $`d\sum_i v_i\phi_i^2+A\sum_j\theta_j^2`$. For the cell arguments $`X_{ij}=\phi_i+\theta_j`$, this gives

$$
c_{ij,kl}=\frac{\delta_{ik}}{d v_i}+\frac{\delta_{jl}-1/d}{A}.
$$

Write $`\sigma_i^2=c_{ij,ij}`$. The simple uniform bound $`\sigma_i^2\le30/n`$ will suffice.

## Cubic phase and quartic loss

Put $`b_i=v_i(1-2p_i)`$, $`a_i=v_i(6v_i-1)/24>0`$, and define

$$
\Phi=-\frac16\sum_{ij}b_iX_{ij}^3,\qquad
\Lambda=\sum_{ij}a_iX_{ij}^4.
$$

For jointly centered Gaussian $`X,Y`$, with variances $`\sigma_X^2,\sigma_Y^2`$ and covariance $`c`$, Wick's identity gives

$$
\mathbb E(X^3Y^3)=6c^3+9\sigma_X^2\sigma_Y^2c,\qquad
\mathrm{Cov}(X^4,Y^4)=24c^4+72\sigma_X^2\sigma_Y^2c^2.
$$

The second term in the cubic identity is the contribution from the linear component of the cubic monomial and is essential in this estimate.

In the homogeneous case let $`v=x(1-x)`$. Equivalently, the covariance at homogeneity is $`(\delta_{ik}-1/n)/(dv)+\delta_{jl}/(nv)`$. Then

$$
\sum c_{ij,kl}^3=\frac{n^2+d^2-1}{nd\thinspace{}v^3},
\quad
\sum c_{ij,kl}=\frac{nd}{v},
\quad
\sigma^2=\frac{n+d-1}{ndv}.
$$

For the cube sum, expand across the row and column pieces. The centered row projection $`P_{ik}=\delta_{ik}-1/n`$ has sums $`\sum P_{ik}=0`$, $`\sum P_{ik}^2=n-1`$ and $`\sum P_{ik}^3=(n-1)(n-2)/n`$. Thus

$$
\mathbb E\Phi^2=
\frac{(1-2x)^2}{36v}\frac{6(n^2+d^2-1)+9(n+d-1)^2}{nd}
\le \frac{109}{63}<\frac74 .
$$

Indeed $`n/d+d/n\le17/4`$ and $`(1-2x)^2/v\le16/21`$. Also $`\mathbb E\Lambda=(6v-1)(n+d-1)^2/(8vnd)\le25/16`$.

The following explicit comparison controls heterogeneity. Put $`\eta=\max_i|p_i-x|`$, use subscript $`0`$ for the homogeneous values, and let

$$
H_{ij,kl}=\delta_{ik}/d+\delta_{jl}/n+1/(nd).
$$

The covariance formula and $`|v_i-v|\le\eta`$ imply $`|c|,|c_0|\le5H`$, $`|c-c_0|\le25\eta H`$. Also $`|b_i-b_0|\le\eta`$ and $`|b_i|,|b_0|\le1/4`$. Direct summation yields $`\sum H=3nd`$, $`\sum H^2\le9n`$, and $`\sum H^3\le54`$, using $`(s_1+s_2+s_3)^j\le3^{j-1}\sum_i s_i^j`$. Consequently the change in the $`c^3`$ contribution to $`\mathbb E\Phi^2`$ is at most $`1620\eta`$. For the linear contribution, write $`B_i=b_i\sigma_i^2`$. One has $`|B_i|\le7.5/n`$ and $`|B_i-B_0|\le70\eta/n`$, so that change is at most $`5025\eta`$ using $`\sum H=3nd`$. Thus changing the profile alters the full cubic moment by at most $`10^4\eta`$. For $`\eta\le10^{-6}`$ the result remains $`\mathbb E\Phi^2<7/4`$.

Similarly $`\mathbb E\Lambda=\sum_{ij}v_i(6v_i-1)\sigma_i^4/8`$ differs from its homogeneous value by at most $`400\eta`$. Use $`|(v_i(6v_i-1))-(v(6v-1))|\le2\eta`$ and $`|\sigma_i^2-\sigma_0^2|\le150\eta/n`$. Hence $`\mathbb E\Lambda<2`$. The quartic Wick identity, $`a_i\le1/192`$, $`\sigma_i^2\le30/n`$ and $`\sum c^2\le225n`$ give $`\mathrm{Var}(\Lambda)\le1000/n`$. As $`e^{-t}`$ is 1-Lipschitz on $`t\ge0`$ and $`1-\cos \Phi\le\Phi^2/2`$, it follows that

$$
\mathbb E[e^{-\Lambda}\cos\Phi]
\ge e^{-\mathbb E\Lambda}\left(1-\frac12\mathbb E\Phi^2\right)
 -\sqrt{\mathrm{Var}(\Lambda)}
\ge\frac1{72}-\sqrt{1000/n}.
$$

## An explicit torus tail bound

Set $`\epsilon=n^{-2/5}`$. Let the central angular set consist of column angles of circular diameter at most $`\epsilon`$, and row angles within circular distance $`\epsilon`$ of $`-\arg\sum_j e^{i\theta_j}`$. On $`\theta_d=0`$, this set is in the real chart with $`|\theta_j|\le\epsilon`$, $`|\phi_i|\le2\epsilon`$, and $`|X_{ij}|\le3\epsilon`$. It contains the real cube $`|\theta_j|,|\phi_i|\le\epsilon/4`$.

The modulus at one cell is bounded by $`\exp[-v_i(1-\cos(\phi_i+\theta_j))]`$. Put $`R=|\sum_j e^{i\theta_j}|`$. Integrating this majorant in each row angle gives $`\prod_i e^{-dv_i} I_0(v_iR)`$. For ease of checking, the elementary Bessel inequalities used below are

$$
J(z)=e^{-z}I_0(z)\ge (6\sqrt{1+z})^{-1},\qquad
J(z)\le \frac{e^{1/(2z)}}{\sqrt{2\pi z}}\quad(z\ge10).
$$

The lower bound integrates $`e^{-z(1-\cos t)}/\pi`$ on $`0\le t\le(1+z)^{-1/2}`$. The sharp upper bound uses $`u=2\sin(t/2)`$, with $`(1-u^2/4)^{-1/2}\le 1+3u^2/8`$ for $`u^2\le2`$, and bounds the remaining interval by $`e^{-z}`$. The large-$`z`$ remainder in Gaussian units is at most $`1/(8z)`$ for $`z\ge10`$. [Detailed one-dimensional Bessel estimate](https://github.com/ProgramComputer/open-math-research/blob/7b585bad34491cf9e733a316e1b62f6c3529880f/topics/balanced-arrays/bessel-margins/upper.md)

For $`R<d/2`$, the row-integrated bound is at most $`e^{-Ad/2}\le e^{-nd/10}`$ since $`I_0(z)\le e^z`$. Relative to $`G`$ this is at most $`e^{-n^2/80}`$, using $`G\ge(2\pi n)^{-n}`$ and $`d\ge n/4`$.

For $`R\ge d/2`$, $`v_iR\ge d/10`$ and the sharp Bessel upper bound gives a total exponential correction at most $`e^{20}`$. Also $`(d/R)^{n/2}\le e^{(n/d)(d-R)}`$. Hence the row-integrated majorant is at most

$$
e^{20}B_0 e^{-A'(d-R)},\qquad A'=A-n/d\ge n/6 .
$$

The lower Bessel bound implies $`e^{A'R}\le6\sqrt{1+A'd}\,I_0(A'R)`$. The exact integral identity

$$
I_0(A'R)=\int_{-\pi}^{\pi}\prod_j e^{A'\cos(\theta_j-t)}\thinspace{}\frac{dt}{2\pi}
$$

allows one to use a product law on the column angles at each common angle $`t`$. Integrating all columns and applying the sharp Bessel upper bound at $`A'`$ gives a total aligned-region bound at most $`6e^{26}G`$. Indeed the column Bessel correction is at most $`e^{d/(2A')}\le e^3`$, replacing $`A'`$ by $`A`$ costs at most another $`e^3`$ by $`\log(A/A')\le(A-A')/A'`$, and $`\sqrt{1+A'd}\le\sqrt{nd}\le\sqrt{2\pi Ad}`$.

If the column diameter exceeds $`\epsilon`$, for every $`t`$ there is a column angle at circular distance greater than $`\epsilon/2`$ from $`t`$. The product von Mises tail at that threshold is bounded by $`6d\sqrt n\,e^{-n\epsilon^2/120}`$ by the lower Bessel bound and $`1-\cos u\ge2u^2/\pi^2`$. In the aligned region the conditional row majorants are themselves independent von Mises laws of parameters $`v_iR\ge n/40`$, centered at $`-\arg\sum_j e^{i\theta_j}`$. The probability of a row-angle violation is at most $`6n\sqrt n\,e^{-n\epsilon^2/200}`$ by the same estimate. Combining these estimates, the absolute contribution outside the central set is at most

$$
G\left(e^{-n^2/80}+10^{15}n^{3/2}e^{-n^{1/5}/200}\right).
$$

These torus estimates can be obtained before fixing $`\theta_d=0`$, since the events and the integrand's modulus are gauge invariant.

## Central remainder and normalization

On the central chart the per-cell logarithm is

$$
\log(1+p_i(e^{iu}-1))-ip_i u
=-v_i u^2/2-i b_i u^3/6-a_i u^4+R_i(u).
$$

On the complex disk $`|u|\le1/4`$, the left side has modulus at most $`3/4`$: use $`|p_i(e^{iu}-1)|\le e^{1/4}-1<1/3`$. Cauchy's coefficient bound and parity give, for real $`|u|\le1/8`$,

$$
|R_i(u)|\le1536|u|^5,\qquad |\Re R_i(u)|\le6144|u|^6 .
$$

On the central set the sum of real remainders has magnitude at most $`6144nd(3\epsilon)^6<1`$. The normalized Gaussian expectation of $`\sum_{ij}|R_i(X_{ij})|`$ on that set is at most $`1536\cdot nd\cdot8(30/n)^{5/2}`$. Since $`\Lambda\ge0`$, replacing its exponential with the version including the full remainder costs at most $`2\cdot10^8/\sqrt n`$ in Gaussian units, using $`|e^{R}-1|\le e^{|\Re R|}|R|`$.

The Gaussian loss from restricting to the central set is at most $`4n e^{-n^{1/5}/3840}`$. To see this, work in the section $`\theta_d=0`$ and note that $`\phi_i=X_{id}`$ and $`\theta_j=X_{1j}-X_{1d}`$ have variances at most $`120/n`$. The Gaussian tail bound on the cube of radius $`\epsilon/4`$, which is contained in the central set, gives the asserted loss. The integrand $`e^{-\Lambda}\cos\Phi`$ has absolute value at most one. For $`n\ge10^{30}`$ each of $`\sqrt{1000/n}`$, the Taylor error, the Gaussian chart loss, and the full torus tail loss is less than $`10^{-4}`$, directly from the displayed bounds. The joint probability, which is the real part of the integral, is therefore larger than $`G/100`$.

Conditioning on the prescribed row sums divides by the product of the row binomial mean atoms. Stirling's bounds put that product at most $`B_0e^{n/(12d)}<2B_0`$. Thus the balance probability is at least $`\sqrt d(2\pi A)^{-(d-1)/2}/200`$. Finally $`A=\sum_i p_i(1-p_i)\le nx(1-x)`$ because the average of the $`p_i`$ is $`x`$. This proves the proposition.
