# A single maximum for the row-slack error

Fix integers $`d>r\ge2`$, put $`c=d-r`$ and $`R=rc/d`$, and allow $`s`$ to run over the integers from zero to $`nr`$. With $`nr-s=dk+\ell`$, $`0\le\ell<d`$, the prescribed column sums are $`k+1`$ in the first $`\ell`$ columns and $`k`$ in the others. These margins are feasible by placing the ones of successive columns into the next available positions in a repeating cyclic order of the rows. Within each column the positions are distinct and all row loads differ by at most one. Column permutations preserve the distribution of the row loads. The statistic $`E_n`$ is defined on the [topic page](README.md).

## The tilted row law

Give a subset of $`r-j`$ columns probability proportional to $`x^j`$, for $`x>0`$ and $`0\le j\le r`$. Let $`J`$ be its deficit, $`\pi_j=\Pr(J=j)`$, $`t=\mathbb E J`$, $`p=\pi_0`$, $`V=\mathrm{Var}(J)`$ and $`g(t)=1/(1+t)-p`$. The map $`x\mapsto t`$ is analytic, strictly increasing from zero to $`r`$, and $`x\,dt/dx=V`$. Also $`x\,dp/dx=-tp`$. Summing $`(c+j)\pi_j=x(r-j+1)\pi_{j-1}`$ over $`1\le j\le r`$, and then differentiating in $`\log x`$, gives

$$
x(r-t)=t+c(1-p),\qquad (1+x)V=x(r-t)-ctp.
$$

Set $`u=(1+t)g=1-(1+t)p`$. Substitution gives

$$
V=\frac{(r-t)(1+t)(t+cu)}{r+dt+cu},\qquad
g'(t)=\frac{F(t,u)}{(1+t)^2(r-t)(t+cu)},
$$

where

$$
F(t,u)=(d+1)t^2-[rc+(r-2c)t+dt^2]u-ctu^2 .
$$

The denominator is positive because $`1+x>0`$ and $`(1+x)V=t+cu`$. The equation $`F(t,h)=0`$ has a unique positive solution $`h(t)\in(0,1)`$, since $`F(t,0)>0`$, $`F(t,1)=(t-r)(t+c)<0`$ and the product of the two roots is negative. At the positive root $`F_u<0`$. On that curve $`F_t/h=2rc/t+r-2c+ch>0`$, so $`h'>0`$.

When the actual trajectory meets this curve, $`g'=0`$ and $`u'=u/(1+t)`$. Differentiating $`F(t,u(t))`$ there gives $`hD/(1+t)`$ with

$$
D(t)=rc(1+2/t)+r-2c-dt^2+c(1-t)h(t).
$$

For $`t\le1`$, the terms $`rc+r-dt^2\ge c(r-1)`$ and $`2rc/t-2c\ge0`$ show that $`D>0`$. If $`t\ge1`$ and $`t^2\le R`$, then $`D\ge r+c(2r/t-1-t)>0`$ because $`t^2<r`$. On $`1\le t<r`$, $`D`$ is strictly decreasing by $`h'>0`$. Its limit at $`r`$ is $`d(1-r^2)<0`$, since $`h(r)=1`$. Thus it has exactly one zero $`T>\max\{1,\sqrt R\}`$.

Write $`b=(r-1)(c+1)/(r(c+2))<1`$. Expanding the masses at small $`x`$ gives $`p=1-t+bt^2+O(t^3)`$, so $`g=(1-b)t^2+O(t^3)`$. At $`y=1/x\downarrow0`$, $`r-t=dy+O(y^2)`$, $`V=dy+O(y^2)`$ and $`p=O(y^r)`$, so $`g'=tp/V-1/(1+t)^2`$ is negative near $`r`$. The sign of $`F`$ starts positive. It cannot have a first zero before $`T`$, since its derivative at such a zero is positive. Nor can a first zero occur at $`T`$. Indeed, there $`F=F'=0`$ would imply $`u'=h'`$ because $`F_u\ne0`$. The derivative along the trajectory of the smooth function $`F_t+F_u[g+(1+t)g']`$ at this contact equals its derivative along $`h`$. Along $`h`$ this function is $`hD/(1+t)`$, whose derivative at $`T`$ is strictly negative. Hence $`F''<0`$, inconsistent with $`F>0`$ just to the left of its zero. After $`T`$, every zero has strictly negative derivative. The negative sign near $`r`$ therefore gives exactly one zero $`t_*`$, and $`g''(t_*)<0`$. This proves strict increase on $`(0,t_*)`$ and strict decrease on $`(t_*,r)`$.

## Local probabilities at fixed dimension

Let $`X\in\{0,1\}^d`$ be one row under this tilt, $`m=\mathbb E X=(r-t)\mathbf1/d`$ and $`\Sigma=\mathrm{Cov}(X)`$. Conditioning $`n`$ independent rows on the prescribed margin vector gives the uniform array measure. In original column coordinates that vector is $`nm+a`$ for $`a=\mathbf1_{[\ell]}-(\ell/d)\mathbf1`$, so $`a\cdot\mathbf1=0`$.

We give details of the local expansion to make the uniformity near the two endpoints explicit. For bounded offsets $`v`$ with $`Nm+v`$ integral, put $`\tau=\min(1,t,r-t)`$. Uniformly for $`N\tau`$ above a sufficiently large constant,

$$
\Pr\left(\sum_{i=1}^N X_i=Nm+v\right)
=\frac{1}{(2\pi N)^{d/2}\sqrt{\det\Sigma}}
\left(1+\frac{H(v,t)}N+O((N\tau)^{-2})\right).
$$

With $`G`$ normal of covariance $`\Sigma^{-1}`$, and $`K_j(G)`$ the $`j`$th cumulant of the scalar product $`G\cdot X`$ for a fixed $`G`$, the coefficient is

$$
H(v,t)=\mathbb E_G\left[\frac{K_4(G)}{24}
 -\frac12\left(v\cdot G+\frac{K_3(G)}6\right)^2\right].
$$

All error constants may depend on $`d,r`$ and the offset bound. We justify this expansion and the regularity used below.

* Near $`t=0`$ use integer affine coordinates $`(X_1,\ldots,X_{d-1},J)`$. Their linear part has determinant of absolute value one. For each $`h<d`$, a pair of cap-size rows swapping columns $`h,d`$ has difference $`(e_h,0)`$ and probabilities bounded below. Deleting column $`d`$ from a cap-size row containing it gives a pair differing only by the deficit unit, with product of probabilities at least a constant times $`t`$. Squaring the modulus of the characteristic function expresses its loss from one as a sum of the corresponding $`1-\cos`$ terms. Thus its modulus on $`[-\pi,\pi]^d`$ is bounded by $`\exp[-C(\sum_{h<d}\sin^2(\theta_h/2)+t\sin^2(\theta_d/2))]`$ for some $`C>0`$. This also bounds the covariance from below in the corresponding scaled coordinates. The variance of $`J`$ is $`O(t)`$, giving the matching upper bound by Cauchy–Schwarz.
* Scale the first $`d-1`$ angles by $`1/\sqrt N`$ and the last by $`1/\sqrt{Nt}`$. Write $`z`$ for the rescaled vector. The centered log characteristic function is jointly analytic in the angles and $`t`$ on a fixed complex neighborhood of zero, since $`x`$ has an analytic inverse at $`t=0`$ and the characteristic function is uniformly close to one near angle zero. Each angular derivative that uses the last coordinate is $`O(t)`$ there. Indeed at $`t=0`$ the deficit vanishes identically. Pure transverse derivatives are bounded. In the rescaled exponent the degree-$`j`$ Taylor terms, $`j\ge3`$, are bounded by $`C_j(Nt)^{1-j/2}|z|^j`$. The offset contributes a linear term bounded by $`C(Nt)^{-1/2}|z|`$.
* On $`|z|\le(Nt)^{1/20}`$ expand the logarithm through order five. The sixth-order remainder is bounded by $`C(Nt)^{-2}|z|^6`$ by the same derivative bounds. Exponentiation around the Gaussian gives the linear-plus-cubic term, the quartic and half the square of the linear-plus-cubic term, and odd terms of order $`(Nt)^{-3/2}`$. All odd terms integrate to zero on the symmetric ball. The omitted terms have Gaussian integral $`O((Nt)^{-2})`$, by the uniform positive lower covariance bound and the bounds just given. Outside the ball the torus estimate and $`\sin^2(\theta/2)\ge\theta^2/\pi^2`$ give a Gaussian tail. Undoing the invertible coordinate change in the Gaussian averages gives precisely the displayed $`H`$.
* Near $`t=r`$, write $`\eta=r-t`$. Empty and singleton rows give the corresponding torus bound with weight $`\eta`$ in every coordinate. All angles scale by $`1/\sqrt{N\eta}`$, and every positive-order angular derivative of the centered logarithm is $`O(\eta)`$ on a fixed complex neighborhood. The same proof now uses $`N\eta`$. Away from the endpoints all coordinate variances are bounded above and below as quadratic forms, using the empty and singleton rows. Continuing the Taylor expansion through order seven on a compact interior interval gives a second analytic coefficient divided by $`N^2`$ and uniform relative remainder $`O(N^{-3})`$. The terms of odd order vanish by the same parity argument.

The cumulants are analytic in the tilt and Gaussian moments are polynomials in the entries of $`\Sigma^{-1}`$. Thus $`H`$ is analytic in the interior and meromorphic at both endpoints for offsets analytic there. Here the endpoint odds $`x`$ or $`1/x`$ are analytic functions of $`t`$ near the corresponding endpoint. The preceding bounds give $`H=O(1/\tau)`$, so any endpoint pole has order at most one.

## Removing the phase from the first correction

Mark one row of deficit $`j`$ and call its indicator vector $`w`$. Its conditional probability in the array is its tilted probability times the ratio of the local mass for $`n-1`$ rows at offset $`a+m-w`$ to the mass for $`n`$ rows at $`a`$. The preceding estimates give this ratio as

$$
1+\frac{d/2+H(a+m-w,t)-H(a,t)}n+O((n\tau)^{-2}).
$$

Changing $`n-1`$ to $`n`$ in the correction is allowed since $`H=O(1/\tau)`$. The quadratic dependence of $`H`$ on its offset is $`-v^{\mathsf T}\Sigma^{-1}v/2`$; its remaining dependence on $`v`$ is affine. Therefore the only dependence on $`a`$ in this difference is $`-a^{\mathsf T}\Sigma^{-1}(m-w)`$. Averaging over the uniform row of size $`r-j`$ removes it. Indeed $`\mathbb E(m-w\mid J=j)=(j-t)\mathbf1/d`$ and the permutation-invariant covariance preserves the span of $`\mathbf1`$. Write $`C_j(t)`$ for the averaged correction, including $`d/2`$. It is analytic in the interior, has at most simple poles at the endpoints, and is independent of $`\ell`$. Under the conditioned law,

$$
\Pr_n(J=j)=\pi_j\big[1+C_j(t)/n+O((n\tau)^{-2})\big].
$$

On a compact subinterval of $`(0,r)`$ there is also a second analytic coefficient, possibly phase dependent, with relative error $`O(n^{-3})`$ after including it.

## Uniform comparison at both endpoints

When $`t=s/n`$ is small, use the exact identity

$$
E_n(s)=\frac{s(s-1)}{n+s-1}-n\sum_{j=2}^r(j-1)\Pr_n(J=j).
$$

It follows because the sum of all row deficits is $`s`$. The weight $`\pi_j`$ is $`O(t^j)`$, so the total error after multiplication by $`n`$ is $`O(nt^2/(nt)^2)=O(n^{-1})`$. The leading term is $`ng(t)`$ since $`\sum_{j\ge2}(j-1)\pi_j=t-1+p`$. The smooth correction is

$$
B(t)=-\frac{t}{(1+t)^2}-\sum_{j=2}^r(j-1)\pi_j C_j(t).
$$

It extends analytically to zero by the pole bound. Thus $`E_n(s)=ng(t)+B(t)+O(n^{-1})`$ uniformly when $`s`$ exceeds a sufficiently large constant and $`t`$ is near zero. For $`t`$ bounded away from zero use instead $`E_n(s)=n[1-\Pr_n(J=0)]-ns/(n+s-1)`$. The corresponding analytic correction is $`-t/(1+t)^2-p C_0(t)`$. In the overlapping interior the two formulas agree, for example since $`\sum_j \Pr_n(J=j)=1`$ and $`\sum_j j\Pr_n(J=j)=t`$ exactly by row exchangeability, which force $`\sum_j\pi_j C_j=\sum_j j\pi_j C_j=0`$ by taking fixed-$`t`$ limits through feasible grids. Continuity covers irrational $`t`$. Near $`r`$ we have $`p=O((r-t)^r)`$, so the same relative remainder gives $`O(n^{-1})`$ in $`E_n`$ and the correction again has a removable singularity. This gives a common smooth $`B`$ on the closed interval. On any compact interior interval and at each fixed phase the stronger expansion is

$$
E_n(s)=ng(t)+B(t)+B_{2,\ell}(t)/n+O(n^{-2}),
$$

with analytic $`B_{2,\ell}`$.

Two small integer ends remain. For bounded $`s`$ and large $`n`$, specify how many row deficits equal each positive $`j`$ and let $`m_+`$ be the number of positive deficits. Ignoring column margins, the weight of this profile is proportional to $`(n)_{m_+}\prod_{j\ge1}(h_j/h_0)^{m_j}/m_j!`$, where $`h_j=\binom d{r-j}`$. For each profile the probability of the required margins is a common positive constant times $`n^{-(d-1)/2}(1+O_s(1/n))`$. To see this, condition on the bounded number of positive-deficit rows. All other rows are independent uniform $`r`$-subsets. Since the last margin is fixed by the total, only the first $`d-1`$ coordinates need be prescribed. Their offsets from the mean stay bounded. The differences of $`r`$-subsets span the integer lattice in these coordinates by the swaps above. The ordinary fixed-covariance Fourier expansion therefore gives the estimate uniformly, including after averaging the exceptional rows.

Compared with $`s`$ single deficits, the weight of a profile with one double and $`s-2`$ singles has ratio $`bs(s-1)/(n-s+1)`$ before margin conditioning and a further factor $`1+O_s(1/n)`$ afterwards. All profiles with $`m_+\le s-2`$ have relative weight $`O_s(n^{-2})`$. Consequently

$$
E_n(s)=\frac{(1-b)s(s-1)}n+O_s(n^{-2}).
$$

This also holds for $`s=0,1`$, where $`E_n`$ is exactly zero. At the opposite end, if $`L=nr-s`$ stays bounded, first choose the columns independently with their prescribed sizes. The expected number of rows of size at least $`r`$ is at most $`n\binom dr(L/n)^r`$, by summing over sets of columns. The event of satisfying the cap has probability at least $`1-n\binom d{r+1}(L/n)^{r+1}`$. Conditioning gives $`\mathbb E M=n+O_L(n^{-1})`$ for $`r\ge2`$. Consecutive excesses at this end thus have difference $`-1/(1+r)^2+O_L(1/n)`$.

## Consequences for the original fibers

Whenever $`s`$ and $`nr-s`$ exceed fixed sufficiently large constants, the common smooth correction gives

$$
E_n(s+1)-E_n(s)=g'(s/n)+O(n^{-1}).
$$

Here and below take differences only where the indices exist. Near zero $`g'(t)=2(1-b)t+O(t^2)`$, so the sign is strictly positive for all $`s`$ above a fixed constant in that neighborhood. The bounded-$`s`$ expansion supplies strict increase at every remaining $`s\ge1`$. The bounded-load argument above supplies strict decrease near $`nr`$. In the bulk $`g'`$ is separated from zero off any fixed neighborhood of $`t_*`$. Because $`g''(t_*)<0`$, the sign is also determined outside $`|s-nt_*|\le C`$ in that neighborhood, with $`C`$ depending on $`d,r`$. This gives the stated scale-one result and the one-step signs through both tails.

For each fixed residue of $`s`$ modulo $`d`$, take differences with step $`d`$. In a fixed interval about $`t_*`$ where $`g''`$ is strictly negative, the stronger interior expansion at that phase gives

$$
E_n(s+d)-2E_n(s)+E_n(s-d)=\frac{d^2}{n}g''(s/n)+O(n^{-2})<0.
$$

On the two sides, the one-step signs already give strictly positive and strictly negative fixed-phase differences respectively, including the first possible step out of zero because $`d\ge3`$. Hence there is one maximizing grid point or one pair of consecutive tied grid points at that phase. The one-step estimate puts them at $`nt_*+O_{d,r}(1)`$. When $`r=1`$ every deficit is zero or one and $`M=s`$ deterministically, which gives the stated exceptional formula.
