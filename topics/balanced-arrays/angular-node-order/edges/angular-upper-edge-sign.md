# Exact signs of the saturated-edge limiting functions

For integers $d\ge2$, $0\le s<d$, and $j\ge1$, put

$$
\theta=\frac{\pi}{d},\qquad m=dj+s,\qquad
\lambda=\frac{\theta m}{\sin\theta},\qquad
E_{d,s}(\lambda)=\sum_{h\ge0}(-1)^h\frac{\lambda^{s+dh}}{(s+dh)!}.
$$

Then $(-1)^j E_{d,s}(\lambda)>0$ for every such triple.
In fact the following strict lower bounds hold:

$$
(-1)^j E_{d,s}(\lambda)>
\begin{cases}
\displaystyle\frac{\lambda^m}{27m!},&4m\le d^2,\\[6pt]
\displaystyle\frac{5}{3d}e^{\lambda\cos\theta},&4m\ge d^2 .
\end{cases}
$$

At equality both bounds apply. This proves the sign for the limiting
function. A transfer from the original array integral requires its
own estimate.

## Two adjacent terms when $4m\le d^2$

Here $m\ge d$ forces $d\ge4$. Let $\alpha=\lambda/m=\theta/\sin\theta$.
The sine Taylor inequality and $-\log(1-x)\le x/(1-x)$ give

$$
0\le\log\alpha\le\frac{\theta^2}{6-\theta^2}
\le\frac{10}{6d^2-10}\le\frac2{d^2},
$$

using $\pi^2<10$ and $d\ge4$.

Normalize the series by its central magnitude $\lambda^m/m!$
and multiply it by $(-1)^j$. The adjacent terms on both sides
are then negative. Their absolute magnitudes are

$$
L=\frac{m(m-1)\cdots(m-d+1)}{\lambda^d},
\qquad
R=\frac{\lambda^d}{(m+1)(m+2)\cdots(m+d)}.
$$

For $L$ apply $\log(1-x)\le-x$ to each factor, and for $R$ apply
$\log(1+x)\ge x/(1+x)$. This gives

$$
\begin{aligned}
\log L
&\le-\frac{d(d-1)}{2m}\le-\frac32,\\
\log R
&\le d\log\alpha-\frac{d(d+1)}{2(m+d)}
 \le \frac2d-\frac{d+1}{d}\le-\frac12.
\end{aligned}
$$

The second bound uses $m+d\le d^2/2$. Both tails decrease outward:
the ratio of successive right terms decreases because its denominator
is a product of $d$ increasing factors, and the ratio of successive left
terms decreases because its numerator is a product of $d$ decreasing
factors. The first ratios are $R<1$ and $L<1$. Starting from distance
two, pair each positive term with the next negative term on its side.
The paired contributions and a possible unpaired last positive term
are nonnegative. Absolute convergence also permits this pairing on
the infinite right side. Hence the normalized signed value is at least
$1-L-R$. Since $e^{1/2}>3/2$, one has
$L+R<(2/3)^3+2/3=26/27$.

## The aligned conjugate pair when $4m\ge d^2$

Use the odd-root filter with $\theta_\ell=(2\ell+1)\theta$:

$$
E_{d,s}(\lambda)
 =\frac1d\sum_{\ell=0}^{d-1}
 e^{-is\theta_\ell}\exp\bigl(\lambda e^{i\theta_\ell}\bigr).
$$

Indeed, after expanding the exponential the angular average vanishes
unless the power index is $s+dh$. In that case its angular factor is
$e^{i\pi h}=(-1)^h$. The condition $0\le s<d$ ensures that all
surviving nonnegative indices have $h\ge0$.

The terms at angles $\pm\theta$ sum to

$$
\frac2d e^{\lambda\cos\theta}
\cos(\lambda\sin\theta-s\theta)
=\frac2d e^{\lambda\cos\theta}(-1)^j,
$$

because $\lambda\sin\theta-s\theta=(m-s)\theta=j\pi$.
For each other positive-angle representative
$\beta=(2\ell+1)\theta\le\pi$ with $\ell\ge1$,

$$
\cos\theta-\cos\beta
=2\sin(\ell\theta)\sin((\ell+1)\theta)
\ge\frac{8\ell^2}{d^2}.
$$

To see this, use
$\sin x\ge(2/\pi)\min(x,\pi-x)$ on $[0,\pi]$.
Here $\ell\le(d-1)/2$, so both sine factors are at least
$2\ell/d$. This also covers the singleton angle $\pi$ when $d$
is odd. Counting it as if it had a conjugate only increases the
error bound.

Since $\lambda\ge m\ge d^2/4$, the absolute magnitude of all
nonprincipal terms, divided by $2e^{\lambda\cos\theta}/d$, is
at most

$$
\sum_{\ell\ge1} e^{-2\ell^2}
\le \sum_{\ell\ge1}e^{-2\ell}
=\frac{1}{e^2-1}<\frac16 .
$$

This gives the asserted strict lower bound in this range.
The two cases exhaust all $m$ and use no row-height cutoff.
