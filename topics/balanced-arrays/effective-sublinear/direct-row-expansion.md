# Explicit expansion after conditioning on the row size

For integers $`d\ge10`$ and $`0\le\ell\le d`$, let $`I`$ be a uniform
$`\ell`$-subset of $`\{1,\ldots,d\}`$. Write $`p=\ell/d`$, $`v=p(1-p)`$,
and let $`y=(y_1,\ldots,y_d)`$ be real with $`\sum_j y_j=0`$.
Put $`Q_b=\sum_j y_j^b`$, $`M=\max_j|y_j|`$, and
$`L=\sum_{j\in I}y_j`$. The characteristic function is the
conditional row factor obtained by taking the coefficient of
degree $`\ell`$ in the row marker and dividing by $`\binom d\ell`$.

Define the following real coefficients, with the falling factorial
notation $`(m)_b=m(m-1)\cdots(m-b+1)`$:

$$
a=\frac{d v}{d-1},\qquad
\gamma=a\frac{d-2\ell}{d-2},\qquad
\xi=\frac{(\ell)_2(d-\ell)_2}{(d)_4},\qquad
A_4=a-6\xi,\qquad B_4=\xi-a^2 .
$$

The cumulants of $`L`$ of orders one through four are
$`0`$, $`aQ_2`$, $`\gamma Q_3`$, and $`A_4Q_4+3B_4Q_2^2`$.
The coefficients satisfy

$$
|\gamma|\le a,\qquad |A_4|\le a\le 2v,\qquad
|B_4|\le \frac{2v}{d},\qquad
|\kappa_4(L)|\le6v(Q_4+Q_2^2/d).
$$

If $`M\le1/2`$, the analytic logarithm through zero gives

$$
\log\mathbb E e^{iL}
=-\frac a2Q_2-\frac{i\gamma}{6}Q_3
+\frac{A_4}{24}Q_4+\frac{B_4}{8}Q_2^2+R,
\qquad
|R|\le 8vQ_2M^3,\qquad |\Re R|\le6vQ_2M^4 .
$$

The expansion is a quantitative version of the uniform row logarithm
in the sparse fixed-profile argument. It applies at both ends of the
row-size range by complementation. [Sparse fixed-profile expansion](https://github.com/ProgramComputer/open-math-research/blob/main/topics/balanced-arrays/eventual-all/sparse-fixed-profile-edgeworth.md#uniform-logarithmic-expansion-for-one-row)

## Exact moments and fourth coefficient bounds

Put $`P_b=(\ell)_b/(d)_b`$, the inclusion probability for a specified
$`b`$-element subset. The mean is $`P_1\sum_j y_j=0`$.
The second raw moment is $`(P_1-P_2)Q_2=aQ_2`$.
In the third raw moment, terms with precisely one, two and three
distinct indices contribute $`Q_3`$, $`-3Q_3`$ and $`2Q_3`$, before
multiplication by $`P_1,P_2,P_3`$ respectively. The coefficient is
$`P_1-3P_2+2P_3=a(d-2\ell)/(d-2)`$, using
$`P_2-P_3=a(\ell-1)/(d-2)`$.

For the fourth raw moment, grouping monomials by their number of
distinct indices gives the following coefficients before multiplying
by the corresponding inclusion probability:

$$
Q_4,\qquad 3Q_2^2-7Q_4,\qquad 12Q_4-6Q_2^2,\qquad 3Q_2^2-6Q_4,
$$

in order from one through four distinct indices.

For two distinct indices, the exponent patterns $`(3,1)`$ and $`(2,2)`$
contribute $`-4Q_4`$ and $`3(Q_2^2-Q_4)`$. For three distinct indices
the sum over the two singleton factors distinct from index $`j`$ is
$`y_j^2-Q_2/2`$, which gives the third expression. The last expression follows by
summing all four expressions to zero, since $`(\sum_j y_j)^4=0`$.
The identity $`P_2-2P_3+P_4=\xi`$ is inclusion-exclusion for two
specified elements inside and two specified elements outside $`I`$.
The $`Q_4`$ coefficient equals $`(P_1-P_2)-6\xi`$, and the fourth
cumulant subtracts $`3a^2Q_2^2`$ from the fourth raw moment.

For $`1\le\ell\le d-1`$, let $`u=\ell(d-\ell)`$. Then

$$
\frac{\xi}{a}=\frac{u-d+1}{(d-2)(d-3)},\qquad
\frac{\xi}{a}-a=\frac{(4d-6)a-(d-1)}{(d-2)(d-3)}.
$$

The first ratio lies between zero and
$`(d-2)/(4(d-3))\le1/3`$, by
$`(\ell-1)(d-\ell-1)\le(d-2)^2/4`$.
Thus $`|a-6\xi|\le a`$. Since $`0\le a\le d/(4(d-1))`$, the numerator
in the second ratio is at least $`-(d-1)`$ and at most
$`(d-2)/(2(d-1))`$. Hence
$`|B_4|\le d v/[(d-2)(d-3)]\le2v/d`$ at $`d\ge10`$.
The bound on $`\gamma`$ follows from $`|d-2\ell|\le d-2`$.
The fourth cumulant bound follows by taking absolute values.
For $`\ell=0,d`$, all coefficients and cumulants vanish.

## A zero-free coefficient bound with explicit constants

Assume $`M>0`$ and $`0<\ell<d`$. Put
$`K(z)=\log\mathbb E e^{zL}`$, taking the branch with $`K(0)=0`$.
It is analytic for $`|z|<\pi/(2M)`$. In this disk each $`u_j=e^{zy_j}`$
has positive real part. All roots of $`\prod_j(w+u_j)`$ are strictly in the
left half-plane, as are the roots of each nonconstant derivative
by Gauss–Lucas. The derivative of order $`d-\ell`$ at zero is
$`(d-\ell)!e_\ell(u)`$, so the row moment generating function
$`e_\ell(u)/\binom d\ell`$ has no zeros in the disk.

For $`|z|M\le1`$, write $`t=\Re z`$. If $`\ell>d/2`$, replace $`L`$ in the
modulus bound by the negative sum over the uniform complement.
Let $`q=\min(p,1-p)\le1/2`$ and choose $`t`$ or $`-t`$ accordingly.
The triangle inequality and the elementary symmetric mean inequality
give

$$
\log|\mathbb E e^{zL}|
\le qd\log\left(\frac1d\sum_j e^{\pm t y_j}\right)
\le q t^2 Q_2
\le 2v |z|^2 Q_2.
$$

For the second inequality use $`e^w\le1+w+w^2`$ for real $`|w|\le1`$,
which follows by summing the absolute Taylor remainder from degree
two, and then use $`\sum_j y_j=0`$. The symmetric mean inequality
follows also by pair averaging positive variables with fixed sum,
since that preserves the pair's sum and increases its product,
and each elementary symmetric polynomial is affine in these two
quantities with nonnegative coefficients.

Let $`K(z)=\sum_{b\ge1}c_bz^b`$, $`r_0=1/M`$, and
$`H=2vQ_2/M^2`$. On the circle of radius $`r_0`$,
$`H-\Re K`$ is nonnegative and has mean $`H`$ because $`K(0)=0`$.
Its Fourier coefficient at positive index $`b`$ is
$`-c_b r_0^b/2`$, which is bounded in modulus by its mean.
This gives the coefficient bound

$$
|c_b|\le 4vQ_2 M^{b-2}\qquad(b\ge1).
$$

The coefficients are real since $`K`$ is real on the real segment
through zero. At $`z=i`$, the tail from degree five is bounded by
$`4vQ_2M^3/(1-M)\le8vQ_2M^3`$. Its real part has only even
degrees, starting at degree six, and is bounded by
$`4vQ_2M^4/(1-M^2)\le6vQ_2M^4`$. This proves the expansion.
If $`M=0`$, or if the row is empty or full, the logarithm is
identically zero. The formulas include these cases.

## Summed form in the proposed density window

Suppose $`u=\log n\ge10^6`$, $`100/u\le s=d/n\le1`$, $`x=k/n\in[s/3,1-s/3]`$ and each $`p_i`$ is within $`n^{-1/4}`$ of $`x`$. Since $`x(1-x)\ge2s/9`$, the identity $`\sum_i p_i(1-p_i)=nx(1-x)-\sum_i(p_i-x)^2`$ gives $`\sum_i v_i\ge d/5`$, using $`n^{-1/2}<s/50`$. Also $`d\ge100n/u>10`$.
Put $`\lambda=\sum_i a_i`$, $`\Gamma=\sum_i\gamma_i`$,
$`A_{\ast}=\sum_i A_{4,i}`$ and $`B_{\ast}=\sum_i B_{4,i}`$.
In the centered angular coordinates of the column Fourier integral,
the logarithm of the independent row factors sums to

$$
-\frac{\lambda}{2}Q_2-\frac{i\Gamma}{6}Q_3+
\frac{A_{\ast}}{24}Q_4+\frac{B_{\ast}}{8}Q_2^2+R_{\ast},
\qquad |R_{\ast}|\le8\lambda Q_2M^3,\quad
|\Re R_{\ast}|\le6\lambda Q_2 M^4 .
$$

Here $`\lambda\ge d/5`$, $`|\Gamma|\le\lambda`$,
$`|A_{\ast}|\le\lambda`$ and $`|B_{\ast}|\le2\lambda/d`$.
These are local estimates independent of a torus localization bound.

For clarity, the summed bounds give uniform control of the Gaussian
cubic and the quartic mean. Under the zero-sum Gaussian
$`Y_j=(Z_j-\overline Z)/\sqrt\lambda`$, with independent standard
normals $`Z_j`$, the projection matrix
$`P=I-\mathbf1\mathbf1^{\mathsf T}/d`$ has zero row sums. The linear Wick
term in the variance of $`Q_3(Y)`$ cancels, and
$`\sum_{j,l}P_{jl}^3=(d-1)(d-2)/d\le d`$. Thus
$`\mathrm{Var}(\Gamma Q_3/6)\le d/(6\lambda)\le5/6`$, giving
$`\mathbb E\cos(\Gamma Q_3/6)\ge7/12`$.
The Gaussian quartic exponent
$`\Pi=A_{\ast}Q_4/24+B_{\ast}Q_2^2/8`$ satisfies
$`|\mathbb E\Pi|\le3d/(8\lambda)\le15/8`$ because
$`\mathbb E Q_4\le3d/\lambda^2`$ and
$`\mathbb E Q_2^2=(d-1)(d+1)/\lambda^2`$.
Moreover
$`\|Q_4-\mathbb E Q_4\|_2\le\sqrt{96d}/\lambda^2`$ by the fourth-power
Wick covariance and $`\sum_{j,l}P_{jl}^2=d-1`$.
The identity $`\lambda Q_2\sim\chi^2_{d-1}`$ gives
$`\|Q_2^2-\mathbb E Q_2^2\|_2\le4d^{3/2}/\lambda^2`$.
Consequently $`\|\Pi-\mathbb E\Pi\|_2\le (3/2)\sqrt d/\lambda`$.
The direct row method therefore leaves a bounded Gaussian quartic
mean and a uniformly positive Gaussian cubic characteristic factor
on the stated density window.
