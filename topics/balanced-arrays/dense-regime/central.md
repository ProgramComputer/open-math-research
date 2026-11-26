# Dense positive-slack saddle for the balanced-array coefficients

Assume $d/n\to\delta\in(0,\infty)$, $r/d\to\rho\in[0,1]$, $x=k/n\to x_0\in(0,1)$ and

$$
h_n=(r-dx)/\sqrt d\longrightarrow H\in(0,\infty].
$$

The following estimates give the variance and the probability of an exact total for the capped row distribution. The [main proof](proof.md) uses them for the labeled arrays.

## Row tilt, moments and variance

Let $G(z)=\sum_{s=0}^r\binom ds z^s$, and choose the unique real $\eta$ with mean $dx$ under the law

$$
\Pr(S=s)=\binom ds e^{\eta s}/G(e^\eta),\qquad 0\le s\le r.
$$

The mean strictly increases with $\eta$ since its derivative is the variance. The expectation runs from zero to $r$, and the target mean is strictly between them. This is a binomial law of success probability $b=e^\eta/(1+e^\eta)$ conditioned on $S\le r$.

Put $v_0=x_0(1-x_0)$. At the trial values $\eta=\log(x/(1-x))+\tau/\sqrt d$ with $\tau$ in a fixed bounded interval, the unrestricted standardized variable $(S-dx)/\sqrt d$ converges to $N(\tau v_0,v_0)$ when $\tau$ converges. For instance, this follows by expanding the binomial characteristic function at frequency $u/\sqrt d$. The cap event has probability bounded away from zero on each compact set of trials, and the tilted variable converges to this normal conditioned to lie at most $H$. When $H=\infty$ the conditioning disappears. The bound away from zero follows by the same convergence and positivity of the limiting normal left-tail probability, using compactness to make it uniform over trials. Uniform Hoeffding tails about $db$ for each binomial, with $db-dx=O(\sqrt d)$, give a uniform sub-Gaussian bound for the standardized conditioned variable. Its moments of every fixed order converge.

For $H$ finite positive, the family of truncated normals is an exponential family with density proportional to $\exp(\tau z-z^2/(2v_0))$ on $z\le H$. Its mean is a continuous strictly increasing function of $\tau$, ranging from $-\infty$ to $H$. The lower limit is obtained by centering at the unrestricted mean $\tau v_0\to-\infty$, where truncation is negligible. The upper limit follows, for example, by writing the density of the distance $H-z\ge0$ as proportional to $\exp(-(\tau-H/v_0)(H-z)-(H-z)^2/(2v_0))$ and scaling this distance by $\tau-H/v_0$. Hence a unique finite $\tau_{\star}$ gives mean zero. For $H=\infty$, mean zero gives $\tau_{\star}=0$. Choose finite trial endpoints with opposite mean signs. Monotonicity and convergence bracket the actual tilt between them for large $n$, and uniqueness gives convergence of its parameter $\tau_n=\sqrt d[\eta-\log(x/(1-x))]$ to $\tau_{\star}$. Thus under the actual tilt

$$
\frac{\mathrm{Var}(S)}d\longrightarrow v>0,
$$

with $v=v_0$ for $H=\infty$. The same limit holds uniformly at real quota shifts in every fixed bounded interval. To see uniformity, any sequence of such shifts still has the same $x_0,H$, since the effect on $h_n$ is only $O(\sqrt d/n)=o(1)$. Apply the preceding sequential argument. This also shows that all fixed lattice shifts lie a diverging number of quota steps below the maximal quota, since $D-k=n h_n/\sqrt d+O(1)\to\infty$.

## Local central limit estimate

Let $S_1,\ldots,S_n$ be independent copies of the tilted $S$, and let $\phi(t)=\mathbb E e^{it(S-dx)}$. Fourier inversion gives

$$
\Pr\left(\sum_i S_i=dk\right)=(2\pi)^{-1}\int_{-\pi}^{\pi}\phi(t)^n\thinspace dt.
$$

For $|t|\le a/\sqrt d$ with sufficiently small fixed $a>0$, use an independent copy $S'$ to write $1-|\phi(t)|^2=\mathbb E[1-\cos(t(S-S'))]$. The variance lower bound and fourth-moment upper bound give $1-|\phi(t)|^2\ge cdt^2$, hence $|\phi(t)|\le e^{-c' dt^2}$. At $t=u/\sqrt{nd}$ with $u$ fixed, the bounded standardized third moment and mean zero imply $\phi(t)^n\to e^{-vu^2/2}$ by Taylor expansion.

For $a\le\sqrt d|t|\le M$ with fixed $M$, the limiting centered truncated-normal characteristic function has modulus strictly less than one away from zero. Convergence there is uniform from weak convergence of the standardized variables and their uniformly bounded first absolute moments. For $M/\sqrt d\le |t|\le\pi$, summation by parts gives

$$
|\phi(t)|\le \frac{2\max_s \Pr(S=s)}{|1-e^{it}|}\le\frac{C}{\sqrt d|t|}.
$$

In the first step the total variation of successive masses, padded with zeros, is twice the largest mass by unimodality of the truncated binomial. In the second step the largest binomial mass is $O(d^{-1/2})$ by Stirling and the truncation probability is bounded below. Choose $M$ large enough to bound this last display by a constant less than one. The normalized small-frequency integrals converge by Gaussian domination, while the other integrals are negligible even after multiplication by $\sqrt{nd}$. Thus

$$
\Pr\left(\sum_i S_i=dk\right)
=\frac{1+o(1)}{\sqrt{2\pi n\mathrm{Var}(S)}}.
$$
