# Lower-edge coefficient comparison at fixed row cap

Fix an integer $`r\ge1`$. Let $`n,d\to\infty`$ with $`b=d^2/n\to0`$
and take integer quotas $`k`$ with $`k/d\to c\in(0,\infty)`$. Let $`a_i`$
count labeled binary $`n\times d`$ arrays with common column sum $`i`$
and row cap $`r`$. Define

$$
\Gamma_i=\frac{a_i^2}{a_{i-1}a_{i+1}},\qquad
t_i=\sqrt{\frac{a_{i-1}}{a_{i+1}}},\qquad
H(w)=\sum_{s=0}^r\binom ds w^s .
$$

For real $`u`$ in a fixed bounded window about $`k`$, let $`w_u>0`$ be
the scalar capped-binomial tilt whose mean is $`du/n`$. Then for
every fixed integer $`j`$,

$$
\log\Gamma_{k+j}\longrightarrow\frac1c,\qquad
\log t_k=d\log w_k+\frac{d}{2k}+o(1).
\tag{1}
$$

All integer quotas involved are interior for large $`n`$, since
$`\lfloor nr/d\rfloor/d\to\infty`$.

## The row law at vanishing mean

Write $`\delta=d/n`$, $`\mu_u=\delta u`$, and let $`S`$ have mass
$`\binom ds w_u^s/H(w_u)`$ for $`0\le s\le r`$. The tilt is unique
since the mean increases from zero to $`r`$ and its derivative
in $`\log w`$ is the positive variance. In the stated window,
$`\mu_u\asymp b\to0`$, whereas $`n\mu_u\asymp d^2\to\infty`$.
Writing $`\lambda=dw_u`$, the ratio of the masses at 1 and 0
is $`\lambda`$. Markov's inequality gives
$`\mathbb P(S=0)\ge1-\mu_u`$ and $`\mathbb P(S=1)\le\mu_u`$,
so $`\lambda=O(\mu_u)`$. The bound $`\binom ds/d^s\le1/s!`$ gives

$$
H(w_u)=1+\lambda+O(\lambda^2),\qquad
\mu_u=\lambda+O(\lambda^2),\qquad
\mathbb E[S(S-1)]=O(\mu_u^2).
$$

In particular $`\mathbb P(S=0)=1+O(\mu_u)`$ and
$`\mathbb P(S=1)\sim\mu_u`$. With $`V_u=\mathrm{Var}(S)`$ we have

$$
V_u=\mu_u+O(\mu_u^2),\qquad
\mathbb E|S-\mu_u|^3=O(\mu_u),\qquad
\left|\frac{dV_u}{d\mu_u}\right|=O(1).
\tag{2}
$$

The last bound follows from the exponential-family identity
$`dV/d\mu=\mathbb E(S-\mu)^3/V`$. All constants are uniform on
the window.

At an integer quota $`i`$, let $`T_m`$ be the sum of $`m`$ independent
copies of the law at $`w_i`$, and put $`M=di=n\mu_i`$. Write $`L_i`$ for
$`\mathbb P(T_n=M)`$. Then

$$
L_i=(2\pi nV_i)^{-1/2}(1+o(1)),\qquad
\sup_{v\in\mathbb Z}\mathbb P(T_{n-1}=v)=O((n\mu_i)^{-1/2}).
\tag{3}
$$

Indeed for $`\phi(t)=\mathbb E e^{it(S-\mu_i)}`$ the masses at 0
and 1 in the cosine expansion of $`1-|\phi|^2`$ give
$`|\phi(t)|\le e^{-c_0\mu_i t^2}`$ on $`[-\pi,\pi]`$. Inversion and
absolute values yield the second estimate. At the exact mean
inversion uses $`\phi(t)^n`$ without an additional phase. With
$`t=v/\sqrt{nV_i}`$, the third-moment bound in (2) gives
$`\phi(t)^n\to e^{-v^2/2}`$ uniformly for $`v`$ in bounded sets,
and the Fourier envelope yields Gaussian domination after
rescaling. This proves (3) uniformly for bounded shifts of $`k`$.

## Summing the fixed-margin correction

For integer $`i`$ in the window put

$$
A_i=[w^{di}]H(w)^n,\qquad K_i=\frac{\binom ni^d}{\binom{nd}{di}},
\qquad p_i=i/n.
$$

For a row profile $`\mathbf s`$ with sum $`M=di`$ and $`s_j\le r`$,
the maximum row and column degrees are at most $`r`$ and $`i`$.
The Greenhill–McKay–Wang hypothesis
$`ri/M^{2/3}=O(d^{-1/3})`$ holds, and $`M\to\infty`$.
The normalized row variance is
$`R/[n\mu_i(1-p_i)]`$ for $`R=\sum_j(s_j-\mu_i)^2`$.
It is uniformly bounded since $`\sum_j s_j^2\le rM`$ and $`p_i\to0`$.
The normalized column variance is zero. Thus Corollary 5.2,
under Theorem 1.3, gives uniformly for every feasible row
profile the count

$$
K_i\prod_j\binom d{s_j}
\exp\left(-\frac12+\frac{R}{2n\mu_i(1-p_i)}
+O(d^{-1/3})\right).
\tag{4}
$$

Every profile of total $`di`$ under the cap is feasible. Assign successive blocks of lengths $`s_j`$ in the cyclic list of column labels to the rows. Since $`s_j\le d`$, the labels within each row are distinct, and each label is used exactly $`i`$ times across all $`di`$ positions.

No near-regularity or aspect ratio assumption is needed. [Greenhill–McKay–Wang, Theorem 1.3 and Corollary 5.2](https://doi.org/10.1016/j.jcta.2005.03.005) · [Authors' text, Corollary 5.2](https://web.maths.unsw.edu.au/~csg/papers/irregular-final.pdf#page=33)

The weights $`\prod_j\binom d{s_j}/A_i`$ at total $`M`$ are the
law of the $`n`$ tilted sizes conditioned on $`T_n=M`$.
With $`U=\sum_j S_j(S_j-1)`$, the exact identity on this event is

$$
R=M(1-\mu_i)+U,\qquad 0\le U\le(r-1)M.
$$

Here the seemingly constant exponent $`-1/2`$ in (4) cancels
the linear contribution of the squares. To control $`U`$ after
conditioning, use (3):

$$
\begin{aligned}
\frac{\mathbb E[U\mid T_n=M]}M
&=\frac nM\sum_{s=0}^r s(s-1)\mathbb P(S=s)
\frac{\mathbb P(T_{n-1}=M-s)}{\mathbb P(T_n=M)}\\
&=O(\mu_i).
\end{aligned}
$$

The ratio of probabilities is uniformly bounded, even if the
number of rows grows arbitrarily fast relative to $`d`$. Now the
correction exponent without the $`O(d^{-1/3})`$ part equals

$$
\frac{p_i-\mu_i}{2(1-p_i)}+\frac{U/M}{2(1-p_i)}.
$$

The first term is $`O(\mu_i+p_i)`$ and the second is bounded.
Since $`|e^x-1|\le C|x|`$ on a fixed bounded interval, its
conditional exponential average is $`1+O(\mu_i+p_i)`$. Combining
with the uniform error in (4) gives

$$
a_i=K_i A_i\bigl(1+O(\mu_i+p_i+d^{-1/3})\bigr).
\tag{5}
$$

For $`r=1`$ the term $`U`$ is identically zero, so the same
calculation applies without any comparison of second factorial moments.

## Exact differences of the binomial normalization

Set $`\Delta_i=\log K_i-\log K_{i-1}`$. The adjacent binomial
ratio and the product formula for the ratio at a distance $`d`$
give

$$
\Delta_i=\sum_{h=1}^d
\left[
\log\frac{n-i+1}{n-i+h/d}
+\log\frac{i-1+h/d}{i}
\right].
$$

Writing $`s_h=1-h/d`$, the first logarithm is
$`-\log(1-s_h/(n-i+1))`$ and the second is
$`\log(1-s_h/i)`$. Since $`\sum_h s_h=(d-1)/2`$, Taylor expansion
with a uniform quadratic error gives

$$
\Delta_i=-\frac{d-1}{2i}
+O\left(\frac{d}{n-i+1}+\frac{d}{i^2}\right).
$$

Thus $`(\log K_{k-1}-\log K_{k+1})/2=d/(2k)+o(1)`$.
Also differences of the same logarithms with $`i`$ incremented
by one are $`O((n-i)^{-2}+i^{-2})`$ termwise. Consequently
$`2\log K_i-\log K_{i-1}-\log K_{i+1}=O(d/i^2+d/(n-i)^2)=o(1)`$.
These estimates use exact products, so no Stirling remainder
is needed.

## Entropy differences and the answer

At real quota $`u`$ write $`E(u)=n\log H(w_u)-du\log w_u`$.
At integers the exact tilted coefficient is $`A_i=e^{E(i)}L_i`$.
Differentiation gives

$$
E'(u)=-d\log w_u,\qquad E''(u)=-b/V_u,\qquad
E'''(u)=\frac{b\delta}{V_u^2}\frac{dV_u}{d\mu_u}=O(d^{-1}).
$$

The last estimate uses (2), $`\mu_u\asymp b`$, and $`\delta=b/d`$.
In the whole fixed window $`b/V_u\to1/c`$. Therefore, for fixed $`j`$,
the centered second difference of $`E`$ at $`k+j`$ tends to $`1/c`$
by the triangular integral. The centered first difference
$`(E(k-1)-E(k+1))/2`$ is $`d\log w_k+O(d^{-1})`$ by the bound on
the third derivative. By (2) the ratios of the neighboring
variances tend to one, so (3) makes each of the required
differences of $`\log L_i`$ equal to $`o(1)`$. Combining these
facts with (5) and the binomial normalization calculation
proves (1).
