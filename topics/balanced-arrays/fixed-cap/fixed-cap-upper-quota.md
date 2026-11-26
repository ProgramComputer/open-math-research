# Coefficients at the upper end for a fixed row cap

Fix a positive integer $`r`$, let $`d\to\infty`$, and put $`b=d^2/n\to0`$, $`T=nr/d`$ and $`D=\lfloor T\rfloor`$. Write $`a_i`$ for the number of labeled binary arrays with common column sum $`i`$ and row sums at most $`r`$. The functions $`H(w)=\sum_{s=0}^r\binom ds w^s`$ and $`A_i=[w^{di}]H(w)^n`$ count rows and arrays with only the total prescribed. At real quota $`0<x<T`$ choose $`w_x`$ by $`\mu_x=\mathbb E S=dx/n`$ for the size law with weights $`\binom ds w_x^s`$. Its variance $`V_x>0`$ is the derivative of its mean with respect to $`\log w_x`$, so the tilt exists uniquely. Put $`h_x=r-\mu_x`$.

For internal integers $`k`$ set $`\Gamma_k=a_k^2/(a_{k-1}a_{k+1})`$ and $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$. If $`(D-k)/d\to c\in(0,\infty)`$, then, for every fixed integer $`j`$,

$$
\log\Gamma_{k+j}\to1/c,\qquad \log t_k=d\log w_k+o(1).
$$

If $`(D-k)/d\to0`$, then $`\Gamma_k\to\infty`$.

## The column-balance probability

For $`0\le D-i=O(d)`$, set $`M=di`$, $`e=nr-M=d(T-i)`$, and $`m=d-1`$. Thus $`e=O(d^2)`$ and $`M\sim nr`$. Condition on any row-size profile $`s_1,\ldots,s_n`$ of that total, with $`0\le s_j\le r`$. The uniform fixed-profile local limit gives probability $`\sqrt d\,(2\pi\Lambda)^{-m/2}(1+o(1))`$ of column balance for independent uniform supports of these sizes, uniformly even at $`e=0`$. [Fixed-profile estimate](fixed-profile-balance-llclt.md)

Here $`\Lambda=\sum_j s_j(d-s_j)/(d(d-1))`$ and

$$
0\le\Lambda-\Lambda_{\ast}(i)=
\frac{\sum_j s_j(r-s_j)}{d(d-1)}\le\frac{re}{d(d-1)},
\qquad \Lambda_{\ast}(i)=\frac{i(d-r)}{d-1}.
$$

Since $`d\log(\Lambda/\Lambda_*)=O(e/M)=o(1)`$, averaging over profiles gives $`a_i=A_i F_i(1+o(1))`$ for $`F_i=\sqrt d\,(2\pi\Lambda_*(i))^{-m/2}`$. The adjacent differences of $`\log F_i`$ are $`O(d/i)=O(b)=o(1)`$, since $`i\sim nr/d`$. This proves that the required local logarithmic differences may be taken on $`A_i`$, including when one neighbor is the last coefficient.

## Bounded positive distance on the scale of $`d`$

If $`(D-k)/d\to c>0`$ is finite, then $`h_x\sim cb`$ uniformly for $`|x-k|\le L`$ at any fixed $`L`$. For $`u=dw_x`$, the size weights are proportional to $`c_s u^s`$ with $`c_s=\binom ds/d^s`$ bounded above and bounded away from zero for $`0\le s\le r`$ and $`d\ge2r`$. Expanding the law of the deficit $`J=r-S`$ in $`1/u`$ gives $`V_x=h_x+O(h_x^2)`$, $`\mathbb P(J=0)=1-O(h_x)`$ and $`\mathbb P(J=1)\sim h_x`$. The third absolute centered moment is $`O(h_x)`$ by bounded support, and $`|dV_x/d\mu_x|\le C_r`$ by the centered third-moment identity.

Write $`E(x)=n\log H(w_x)-dx\log w_x`$. Then $`E'(x)=-d\log w_x`$, $`E''(x)=-b/V_x\to-1/c`$ uniformly on these windows and $`|E'''(x)|=O(1/d)`$. At each integer $`i`$ there, $`A_i=e^{E(i)}(2\pi nV_i)^{-1/2}(1+o(1))`$. Indeed the adjacent masses at $`J=0,1`$ give $`|\mathbb E e^{itJ}|\le e^{-c_r h_i t^2}`$ throughout $`[-\pi,\pi]`$. After rescaling $`t`$ by $`1/\sqrt{nV_i}`$, the third-moment Taylor bound and $`nh_i\asymp d^2\to\infty`$ give pointwise Gaussian convergence in Fourier inversion at the integer mean. The preceding Gaussian bound justifies integrating the limit. Ratios of neighboring variances tend to one. The central second difference of $`E`$ is the triangular average of $`-E''`$, and its signed central first difference $`(E(k-1)-E(k+1))/2`$ is $`-E'(k)+O(1/d)`$. This proves both limits.

## Quotas within $`o(d)`$ of the last coefficient

Here $`d\le e=d(T-k)=o(d^2)`$ at an internal quota. The scalar deficit counts $`U_e=[z^e](\sum_{j=0}^r\binom d{r-j}z^j)^n`$ satisfy log-concavity relative to $`\binom{n+e-1}e`$. For completeness, denote the positive row weights by $`B_j`$ and the $`(n-1)`$-row totals by $`C_m`$. The $`C_m`$ have interval support and are log-concave by convolution of log-concave sequences. The law on $`j`$ proportional to $`(j+1)B_j C_{e-j}`$ shifts upwards in likelihood ratio order when $`e`$ increases, by log-concavity of $`C`$. This holds at the support boundaries by extending $`C_m`$ by zero. Under that law the expectation of $`B_{j+1}/B_j`$ (zero at $`j=r`$) is $`(e+1)U_{e+1}/((n+e)U_e)`$, by differentiating the row polynomial power for the numerator and by symmetry of the $`n`$ summands for the denominator. The ratio $`B_{j+1}/B_j`$ decreases, hence this normalized forward ratio decreases. [Original scalar derivation](https://github.com/ProgramComputer/open-math-research/blob/8bf2220688ce5fb1e4ac745daa655bb3c3813fbf/topics/balanced-arrays/deficit-curvature/scalar.md)

Comparing the binomial normalizers at $`e-d,e,e+d`$, and integrating the one-step differences of the logarithms, gives

$$
\log\frac{A_k^2}{A_{k-1}A_{k+1}}
\ge\sum_{j=1}^d\int_0^d\frac{n-1}{(e-d+j+t)(n+e-d+j-1+t)}\thinspace dt
\ge\frac{d^2(n-1)}{(e+d)(n+e+d)}.
$$

Since $`e=o(d^2)`$ and $`d^2=o(n)`$, the right side tends to infinity. The column-balance comparison transfers this divergence to $`\log\Gamma_k`$.
