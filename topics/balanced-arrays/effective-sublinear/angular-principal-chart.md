# Quantitative transverse error on the near angular charts

For a tilted capped-binomial row size $`S`$, let $`a_s=s(d-s)/(d(d-1))`$, $`\gamma_s=a_s(d-2s)/(d-2)`$, $`a=\mathbb Ea_S`$, $`V=\mathrm{Var}(S)`$, $`\phi(t)=\mathbb E e^{itS}`$, and $`f(t)=\mathbb E[f_S e^{itS}]/\phi(t)`$ for $`f=a,\gamma`$. Below $`u=\log n\ge10^{60}`$, $`n^{.99}\le d\le n`$, $`na/d\ge u/400`$, $`nV/d^2\ge u/400`$. In particular $`V\ge n^{.98}u/400`$. The standard variance bound for the tilted row is $`V\le d a`$. On the determinant-minus-one torus let $`t=m\pi/d`$ be an odd common angle, with circular representative in $`[-\pi,\pi]`$. A local chart uses $`t\mathbf1+y`$, $`\sum y_j=0`$ and $`Q_2=\sum_j y_j^2\le b^2`$ with $`b=10^{-3}`$. Write $`R(t,y)=\mathbb E\exp(itS+i\sum_{j\in I_S}y_j)`$ for the tilted row characteristic. The normalized Haar chart integral of $`R^n`$ is $`I_t`$. Let $`\nu=(d-1)/2`$, $`I_0=(2\pi n a)^{-\nu}/\sqrt d`$, and $`G_t=I_0\phi(t)^n(a/a(t))^\nu`$ (continuation from $`t=0`$).

For $`|t|\sqrt V\le 1/10`$, we prove
$`|I_t|\le 4 I_0|\phi(t)|^n\exp(20d|t|)`$.
At $`|t|=\pi/d`$ we also have $`|I_t-G_t|<|G_t|/10`$.
The same bounds hold for $`10^{-4}\le b\le10^{-3}`$ with this value of $`u`$.

For the stated near angles $`|\phi(t)|\ge1-Vt^2/2\ge.995`$, by centering at the mean. For a Lipschitz real function $`g`$ of $`S`$, covariance with $`e^{itS}`$ costs at most $`\mathrm{Lip}(g)|t|V`$ by the independent-copy covariance identity. The functions $`a_s,\gamma_s`$ on the full real interval $`[0,d]`$ have Lipschitz constants at most $`2/d,5/d`$. Consequently
$`|a(t)-a|\le3a|t|`$ and $`|\gamma(t)-\mathbb E\gamma_S|\le6a|t|`$. In particular $`A=n\Re a(t)\in[.99na,1.01na]`$ and $`|\gamma(t)|\le2a`$. The complex quadratic Gaussian has modulus normalized by $`I_0(a/\Re a(t))^\nu`$. This real normalization is at most $`I_0\exp(4d|t|)`$. At $`|t|=\pi/d`$ its ratio to $`I_0|(a/a(t))^\nu|`$ is at most $`\exp(10d t^2)<2`$, by squaring $`|a(t)|/\Re a(t)`$. Covolume on each angular chart is $`1/[\sqrt d(2\pi)^{d-1}]`$ in Euclidean measure: pinning the first $`d-1`$ angles and lifting the last by minus their sum has Gram determinant $`d`$.

## Averaging the subset expansion

Put $`M=\max_j|y_j|`$, $`Q_j=\sum y_i^j`$. On $`Q_2\le b^2`$, use the exact fixed-row expansion
$`K_s=-a_s Q_2/2-i\gamma_s Q_3/6+E_s`$ with
$`|E_s|\le a_s(Q_4+8Q_2 M^3)`$, by the [row cumulant bounds](direct-row-expansion.md). Put
$`D_s=-(a_s-a(t))Q_2/2-i(\gamma_s-\gamma(t))Q_3/6`$.
Then $`\mathbb E_tD_S=0`$, $`|D_s|+|E_s|<.01`$, and $`\mathrm{Var}(a_S)\le4V/d^2`$, $`\mathrm{Var}(\gamma_S)\le25V/d^2`$. The complex shifts cost at most $`2\sqrt{\mathrm{Var}(g_S)}`$ by Cauchy–Schwarz, so
$`\mathbb E|g_S-g(t)|^2\le5\mathrm{Var}(g_S)`$.
Using $`|Q_3|\le M Q_2`$, one gets $`\mathbb E|D_S|^2\le40a Q_2^2/d`$.
The estimates $`|e^{D+E}-1-D|\le2(|D|^2+|E|)`$ and $`|\log(1+z)|\le2|z|`$ for $`|z|<1/2`$ now give

$$
\log(R(t,y)/\phi(t))=-a(t)Q_2/2-i\gamma(t)Q_3/6+E,\qquad
|E|\le 300a(Q_4+Q_2 M^3).
$$

Here $`|\mathbb E_t f|\le2\mathbb E|f|`$ and $`Q_2^2/d\le Q_4`$ were used; using the sharper $`1/.995`$ for the former makes the displayed 300 valid even from the crude variance estimates ($`2\cdot2\cdot(40+1)/.995<170`$).

## Real Gaussian bounds

Take $`Y_j=(Z_j-\bar Z)/\sqrt A`$ with independent standard normals, so $`A Q_2\sim\chi^2_{d-1}`$. Under the real Gaussian, set $`H=-in\gamma(t)Q_3/6+n E`$. On the chart,

$$
(\Re H)_+\le1000 A(Q_4+t^2 Q_2+Q_2M^3)
$$

by $`|\Im\gamma(t)|\le6a|t|`$ and $`|t|\sum|Y_j|^3\le(Q_4+t^2 Q_2)/2`$. We record the exponential moments for each term separately, at multiplier 6000; Hölder with exponents three then bounds $`\mathbb E[\mathbf1_{\mathcal C}e^{2(\Re H)_+}]`$.

For $`Q_4`$, insert $`|\bar Z|\le1`$ at cost at most two. On the chart $`|Z_j|\le1+b\sqrt A\le2b\sqrt A`$. Since $`\sum(Z_j-\bar Z)^4\le8(\sum Z_j^4+d)`$ there, the single-site exponential has parameter $`48000/A`$ on $`|Z_j|\le2b\sqrt A`$. Its exponent is at most $`.192Z_j^2< Z_j^2/4`$. The fourth-power normal expectation bound gives

$$
\mathbb E[\mathbf1_{\mathcal C}\exp(6000 A Q_4)]\le 2\exp(1008000d/A)<3.
$$

For $`Q_2`$, the chi-square moment generating function gives
$`\mathbb E\exp(6000At^2Q_2)\le \exp(12000d t^2)`$, since $`12000t^2<1/2`$.

For $`M\le n^{-2/5}`$ the last exponent is at most $`6000 n b^2 n^{-6/5}<n^{-1/6}`$ since $`A\le n`$. On the remainder of the chart,
$`6000 A Q_2 M^3\le6000 b^3 A M^2\le A M^2/100`$.
The Gaussian tail $`\Pr(M>x)\le2d e^{-Ax^2/2}`$ and integration by parts give
$`\mathbb E[\mathbf1_{M>\epsilon}\exp(A M^2/100)]\le3d e^{-.49A\epsilon^2}`$, where $`\epsilon=n^{-2/5}`$. This is below $`n^{-10}`$ by $`A\ge d u/401`$, $`d\ge n^{.99}`$. Thus this chart exponential moment is less than 2. Combining the three factors gives

$$
\mathbb E[\mathbf1_{\mathcal C}e^{2(\Re H)_+}]\le2\exp(4000 d t^2).
$$

This proves the near-chart modulus bound, since $`2000 d t^2\le d|t|`$ for all these near angles (their $`V`$ is large). The prefactors leave the claimed room.

At $`|t|=\pi/d`$, the last expectation is below 3. In comparing to $`G_t`$ split off $`M>\epsilon`$: Cauchy–Schwarz and the Gaussian tail bound give loss less than $`n^{-9}`$ in real Gaussian units. The real Gaussian probability of $`Q_2>b^2`$ is also below $`n^{-9}`$, by the exponential Markov inequality at $`A/4`$ and $`A b^2/d\ge10^{-8}u/401`$. On $`M\le\epsilon`$ the $`L^2`$ norm of $`H`$ is bounded by

$$
2\sqrt{d/A}+4000 d/A+400d\epsilon^3.
$$

Indeed $`\|Q_3\|_2\le\sqrt{6d}/A^{3/2}`$ by the zero-sum Wick identity, $`\|Q_4\|_2\le\sqrt{105}d/A^2`$ by triangle and the eighth normal moment, and $`\|AQ_2\|_2\le d`$. The right hand side is below $`10^{-4}`$ since $`d/A\le401/u`$. Use $`|e^H-1|\le |H|e^{(\Re H)_+}`$ on the inner region, combining the norm bound with the chart exponential moment. Accounting for both tails gives an absolute error less than $`.001`$ in real Gaussian units. Those units are at most twice the magnitude of the complex Gaussian at the principal angles, proving the asserted relative error.
