# Variance after conditioning two balanced columns

Let $2\le r\le d-2$, and independently choose a uniform $r$-subset of $[d]$ in each of $n$ rows. Suppose $k=nr/d$ is an integer with $1\le k<n$. Write $q=r/d$ and $C_i$ for column $i$'s sum. Then

$$
0<
\mathrm{Var}(C_3\mid C_1=C_2=k)
-nq(1-q)\frac{d(d-3)}{(d-1)(d-2)}
\le \frac{2(d-1)}{r(d-r)(d-2)^2}.
$$

The subtracted term is the conditional variance of a Gaussian with the original column covariance. It is strictly too small for an induction requiring exact Gaussian variance contraction at every conditioning step. The additive error bound is uniform in $n$.

Let $L$ count rows occupied in both first columns after conditioning $C_1=C_2=k$. If $L=l$, the pattern counts for $11,10,01,00$ are $l,k-l,k-l,n-2k+l$. Put $\lambda=(r-1)(d-r-1)/(r(d-r))$ and let $w_l$ be the unnormalized conditional weight. Taking the ratio of the multinomial weights at neighboring overlap sizes gives

$$
l(n-2k+l)w_l=\lambda(k-l+1)^2w_{l-1}.
$$

On the support $\max(0,2k-n)\le l\le k$ both boundaries disappear in the summed identity, giving $\mathbb E[L(n-2k+L)]=\lambda\mathbb E[(k-L)^2]$. The unconditioned mean overlap $\ell_*=nr(r-1)/(d(d-1))$ obeys $\ell_*(n-2k+\ell_*)=\lambda(k-\ell_*)^2$ by the four one-row pattern probabilities. Write $\mu=\mathbb E L$ under conditioning. Subtraction gives

$$
(\ell_*-\mu)
\big[n-2k+\ell_*+\mu+\lambda(2k-\ell_*-\mu)\big]
=(1-\lambda)\mathrm{Var}(L).
$$

The bracket is at least $\mu>0$, since $n-2k+\ell_*$ is the unconditioned mean number of $00$ rows and both $\ell_*$ and $\mu$ are at most $k$. The support contains at least two values and every pattern has positive probability, so the variance is positive. Moreover $\mathrm{Var}(L)\le\mu$. Indeed, the likelihood ratio of the size-biased law of $L$ to the law of $L+1$ is proportional to $(k-l+1)^2/(n-2k+l)$ on their common support and decreases. Any unmatched mass of the size-biased law is below this support, and any unmatched mass of $L+1$ is above it. The resulting single crossing gives $\mathbb E L^2/\mu\le\mu+1$. This proves $0<\ell_*-\mu\le1-\lambda$.

For fixed first two columns, write $s_i$ for the number of their occupied cells in row $i$. The third-column bits are independent with probabilities $(r-s_i)/(d-2)$. Their sum has mean $k$ for every history, while $\sum_i s_i^2=2k+2L$. Hence after conditioning the two sums, the variance is

$$
k-\frac{nr^2-4rk+2k+2\mu}{(d-2)^2}.
$$

Replacing $\mu$ by $\ell_*$ gives the Gaussian value in the theorem. Equivalently the original sums have diagonal variance $v=nq(1-q)$ and off-diagonal covariance $-v/(d-1)$, giving the Gaussian conditional variance $v(1-2/((d-1)(d-2)))$ by the Schur complement for the first two sums. Thus the excess is exactly $2(\ell_*-\mu)/(d-2)^2$, and $1-\lambda=(d-1)/(r(d-r))$ gives the bound.

**Independent check.** An agent-assisted review checked the weight recurrence and boundaries, likelihood-ratio order, and both variance expressions. [Exact checker](conditional-variance-check.py) independently computes the pattern probabilities and checks all 966 integral-margin inputs with $2\le n\le40$, $4\le d\le22$, and $2\le r\le d-2$. This leaves the variance after more than two balanced columns open.
