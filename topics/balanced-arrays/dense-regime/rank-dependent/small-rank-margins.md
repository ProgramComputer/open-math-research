# Equal-column conditioning for small rank

Let $a_k$ count binary $n\times d$ matrices with all column sums $k$ and row sums at most $r$. Write $S=dk$, $\mu=S/n$, $p=k/n=\mu/d$, $b=d^2/n$, and $U_S=[z^S]H(z)^n$ for $H(z)=\sum_{j=0}^r\binom dj z^j$. Fix $\varepsilon,C,c>0$. Suppose $r\le n^{1/5-\varepsilon}$, $b\le Cr$, and $b\log n/r\to\infty$. Uniformly for integer $cd\le k\le nr/d$,

$$
a_k=\frac{\binom nk^d}{\binom{nd}{dk}}U_S
\exp\left(-\frac12+\frac{\sigma^2}{2\mu(1-p)}
+O(n^{-\varepsilon/2})\right).
$$

Here $\sigma^2$ is the variance of the capped-binomial tilt with mean $\mu$, and is zero at saturation. Any feasible shift of such a quota by $O((\log n)^A)$ for fixed $A$ also satisfies the bound with $c/2$, since $d\gg\sqrt{n/\log n}$. This is a coefficient comparison.

## Fixed row profiles

Greenhill, McKay and Wang, *Asymptotic enumeration of sparse 0–1 matrices with irregular row and column sums*, JCTA 113 (2006), 291–324, Theorem 1.3 and §5, Corollary 5.2, require $S\to\infty$, $1\le st=o(S^{2/3})$ for maximum degrees $s,t$ on the two sides, and $(1+\mu_2)(1+\nu_2)=O(S^{1/3})$. With equal columns $k$, $\nu_2=0$ and $\mu_2=\sum_i(s_i-\mu)^2/[n\mu(1-p)]$. The count is $\binom nk^d\prod_i\binom d{s_i}/\binom{nd}{dk}$ times $\exp(-1/2+\mu_2/2+O(st/S^{2/3}))$. The error is uniform and neither aspect ratio has a separate lower bound. [Journal DOI](https://doi.org/10.1016/j.jcta.2005.03.005), [authors' final text, Corollary 5.2](https://web.maths.unsw.edu.au/~csg/papers/irregular-final.pdf#page=33).

In the small-rank regime, $s\le r$, $t=k$, $S\ge cd^2$, $d=o(n)$, $p\le r/d=o(1)$, $\mu\ge cb$, and $r/\mu=O(\log n)$. Also

$$
\frac{rk}{(dk)^{2/3}}\le \left(\frac{nr^4}{d^3}\right)^{1/3}
=n^{-1/6}r^{5/6}(r/b)^{1/2}
=O(n^{-5\varepsilon/6}\sqrt{\log n}).
$$

Because $s_i^2\le r s_i$, one has $\mu_2\le(r-\mu)/(1-p)\le2r$. Also $S\gg nr/\log n$ and $r^3/S=O(r^2\log n/n)=o(1)$. These checks cover every capped row profile.

## Summing weighted profiles

Assume first $0<\mu<r$. Choose the unique $z>0$ such that $X$ has mean $\mu$ under probabilities $\binom dj z^j/H(z)$ at $0\le j\le r$. The mean increases continuously in $\log z$ from 0 to $r$, with strictly positive derivative equal to its variance. Independent copies $X_i$, conditioned on $T=\sum_iX_i=S$, give the profile weights $\prod_i\binom d{s_i}/U_S$.

The bound $\sigma^2\le\mu(1-p)$ follows by size biasing. Weighting by $X$ and then subtracting 1 gives the $(d-1)$-trial binomial tilt truncated at $r-1$. Weighting by $d-X$ gives the same tilt truncated at $r$. The first law is stochastically dominated by the second. The mean inequality $\mathbb E[X^2]/\mu-1\le(d\mu-\mathbb E[X^2])/(d-\mu)$ gives the bound. Here $r<d$ eventually.

Set $Y_i=(X_i-\mu)^2/[\mu(1-p)]$, $\overline Y=n^{-1}\sum_iY_i$, and $M=2r^2/\mu=O(r\log n)$. Then $0\le Y_i\le M$ and $m=\mathbb EY_i\le1$. For $M/n\le1$, the chord bound on $e^x$ gives $\mathbb E e^{Y_i/n}\le1+2/n$ and $\mathbb E e^{\overline Y}\le e^2$.

The row mass function is log-concave with interval support, and convolution preserves these properties. For the mass $\pi$ of $T$, linearly interpolate $\log\pi$ over $[0,nr]$. Jensen's inequality and the entropy bound yield $\log\pi(\mathbb ET)\ge\mathbb E\log\pi(T)\ge-\log(nr+1)$. Thus $\mathbb P(T=S)\ge1/(nr+1)$.

Hoeffding's inequality gives $\mathbb P(|\overline Y-m|>n^{-1/5})\le2\exp(-2n^{3/5}/M^2)$, smaller than every negative power of $n$ because $M=O(n^{1/5-\varepsilon}\log n)$. By Cauchy–Schwarz and the exponential-moment bound, the exceptional contribution to $\mathbb E[e^{\overline Y/2}\mid T=S]$ is also smaller than every negative power after paying at most $nr+1$. On the complement $e^{\overline Y/2}=e^{m/2}(1+O(n^{-1/5}))$. Thus the conditional average is $e^{m/2}(1+O(n^{-1/5}))$. The uniform fixed-profile error carries through the positive sum multiplicatively. Both errors are $O(n^{-\varepsilon/2})$ for the nonempty range $0<\varepsilon\le1/5$.

At $\mu=r$, there is only the constant profile. Take $X_i=r$ deterministically, $Y_i=0$, and $U_S=\binom dr^n$. The same margin comparison applies. When $nr/d$ is nonintegral, the highest quota belongs to the finite-tilt case.

[Related enumeration theorems and priority check](literature.md)
