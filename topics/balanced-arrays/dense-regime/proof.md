# Real zeros of balanced arrays when the number of columns grows at least linearly

**Theorem.** For every $\epsilon>0$ there is an $N(\epsilon)$ such that for every integer $n\ge N(\epsilon)$, every $d\ge\epsilon n$, and every $1\le r\le d$, the balanced-array polynomial has exactly $D=\lfloor nr/d\rfloor$ distinct negative zeros. The cutoff is existential.

Write $a_k$ for the number of labeled binary $n\times d$ matrices with every column sum $k$ and every row sum at most $r$, and $P(q)=\sum_{k=0}^D a_kq^k$. Positivity through degree $D$ follows by filling each column with the next $k$ labels in a cyclic list of the $n$ rows. This gives each row at most $\lceil dk/n\rceil$ ones. The constant coefficient is one. This is a uniform growing-dimension specialization of [Alexandersson's conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays).

## Ordered test points

For $1\le k<D$ set $t_k=\sqrt{a_{k-1}/a_{k+1}}$ and $\Gamma_k=a_k^2/(a_{k-1}a_{k+1})$. We use the normalized log-concavity theorem for the labeled arrays, proved via Kahn and Neiman's orientation inequality. It gives

$$
\Gamma_k\ \ge\left(1+\frac1k\right)^d\left(1+\frac1{n-k}\right)^d\ \ge (1+2/n)^{2d}.
$$

In particular the positive $t_k$ are strictly increasing, since $a_i/a_{i-1}$ decreases strictly. [Orientation proof](../orientation-normalization.md)

Call a node successful if $(-1)^k P(-t_k)>0$. The two neighboring terms each have magnitude $a_kt_k^k/\sqrt{\Gamma_k}$. On either side, successive magnitudes decrease moving away from index $k$, so pairing terms from distance two onward gives a nonnegative total after multiplying by $(-1)^k$. Thus $\Gamma_k>4$ implies success. If all internal nodes are successful, the signs at zero and at sufficiently large negative argument complete $D$ sign changes. The degree makes all roots simple. This also handles degrees zero and one directly.

Suppose the uniform conclusion fails. Choose a sequence with $n\to\infty$, $d/n\ge\epsilon$ and a failed internal node $k$ in each row. Then $\Gamma_k\le4$. The displayed bound forces $d/n$ bounded above. Pass to a subsequence on which $d/n\to\delta\in(0,\infty)$, $r/d\to\rho\in[0,1]$ and $x=k/n\to x_0$. Since $d\log(1+1/k)\ge d/(k+1)$ and likewise at $n-k$, a failed node requires $0<x_0<1$. The capacity bound implies $x_0\le\rho$.

## From fixed margins to a scalar coefficient

The following comparison applies to any such compact density and aspect ratio, at all feasible quotas including the largest one. Put $\mu=dx$, $H(z)=\sum_{s=0}^{r}\binom ds z^s$ and $A_k=[z^{dk}]H(z)^n$. When $0<\mu<r$ give $S$ the distribution proportional to $\binom ds z^s$ on $0\le s\le r$, with $z>0$ chosen for mean $\mu$. Existence and uniqueness follow since the derivative of the mean in $\log z$ is the positive variance. At $\mu=r$ take $S=r$ deterministically. Write $V=\mathrm{Var}(S)$ and $K_k=\binom nk^d/\binom{nd}{dk}$. We claim

$$
a_k=K_k A_k\exp\left(-\tfrac12+\frac{V}{2d x(1-x)}+o(1)\right). \tag{1}
$$

To control exceptional row margins in the **actual** counting measure, choose an array uniformly and condition on all rows except a pair. Each column requires either zero, one or two entries in the pair. If $b$ columns require one entry, the gap between the pair of row sums has the law of $2Y-b$, where $Y$ is binomial $(b,1/2)$ conditioned on a central symmetric interval. Indeed the columns requiring two ones contribute equally, and the two caps cut out precisely such an interval. This conditioning can only decrease the absolute gap. The binomial tail bound gives probability at most $2\exp(-L^2/(2d))$ for an absolute gap larger than $L$ (including $b=0$ by determinism). Since the mean row margin is $\mu$, a row deviation larger than $L$ requires such a gap. A union bound over pairs shows that row profiles with maximum deviation exceeding $d^{1/2+\eta}$ contribute $o(a_k)$ for any fixed $\eta>0$.

On the remaining profiles apply the dense binary-matrix enumeration theorem of Canfield, Greenhill and McKay. Use $n$ rows, $d$ columns, density $x$, equal column margins $k$ and row margins $s_i$ with sum $dk$. The margins are positive on these profiles for large $n$. Both dimensions are comparable, and $x(1-x)$ is bounded below, so the two dimension-growth conditions and the logarithmic density condition of their theorem hold. Take its deviation exponent $\eta$ sufficiently small. The estimate is uniform on the specified profiles (equivalently, any sequence of such profiles satisfies the same hypotheses). Since the column deviations vanish, the number with that precise profile is

$$
K_k\prod_{i=1}^n\binom d{s_i}\thinspace
\exp\left[-\tfrac12+\frac{1}{2x(1-x)}\frac{\sum_i(s_i-\mu)^2}{nd}+o(1)\right].
$$

[Canfield, Greenhill and McKay, Theorem 1, *J. Combin. Theory Ser. A* 115 (2008)](https://doi.org/10.1016/j.jcta.2007.03.009) · [Theorem and full hypotheses](https://web.maths.unsw.edu.au/~csg/papers/CGM.pdf)

Under independent copies $S_i$ conditioned on $\sum_i S_i=dk$, each profile has probability $\prod_i\binom d{s_i}/A_k$. The probability of the conditioning event is at least $1/(nd+1)$. Indeed the sum has a log-concave mass function on an integer interval, since convolution preserves log-concavity with interval support (see the order-two Toeplitz argument in the [endpoint estimate](saturated.md)). Interpolating its log mass linearly, Jensen's inequality at the integer mean gives log mass at least the negative of the entropy. The entropy is at most $\log(nd+1)$. The deterministic endpoint satisfies the same bound.

For clarity, the tilted single-row variable satisfies $\Pr(|S-\mu|>y)\le2e^{-2y^2/d}$ throughout the parameter range. To see this, compare it with a binomial of the same mean. Their mass ratio on $0,\ldots,d$ is a geometric sequence up to $r$ and zero above. Its superlevel set at one is an interval. For any convex function, subtract an affine secant with endpoints between the two masses' sign changes. The function after subtraction is nonpositive inside the interval and nonnegative outside. Equal total mass and mean then show that the convex expectation for $S$ is at most that for the binomial. One may take half-integer secant endpoints just outside the interval, including at an end of the support. Identical laws and deterministic endpoint laws need no comparison. Comparing exponential moments gives the stated bound by Hoeffding's binomial estimate.

In particular $Y_i=(S_i-\mu)^2/d$ have a uniform exponential moment at some positive constant, and $W=n^{-1}\sum_iY_i$ has mean $V/d$. For any fixed tolerance $u>0$, exponential Markov gives $\Pr(|W-V/d|>u)\le2e^{-c_u n}$ from the uniform quadratic expansion bound of the centered moment-generating function at zero. Also $\mathbb E e^{C W}$ is bounded uniformly for each fixed $C$, since it is $(\mathbb E e^{CY_1/n})^n$. The probability that any row is irregular is at most $2n\exp(-2d^{2\eta})$. Cauchy–Schwarz bounds the exponentially weighted expectation on either exceptional event by a constant times the square root of that event's probability. Dividing by the conditioning probability still gives $o(1)$. Consequently the conditional average of $e^{W/[2x(1-x)]}$ over regular profiles is $\exp(V/[2d x(1-x)])+o(1)$, by letting $u$ decrease to zero. Together with the relative tail estimate for the actual arrays, this proves (1).

At any bounded shift of the quota with density tending to $x_0$, the centered second difference of $\log K_k$ tends to zero. In fact the two log-curvatures of $\binom nk^d$ and $\binom{nd}{dk}$ both tend to $\delta/[x_0(1-x_0)]$. For the second, the exact curvature before taking logs is the product over $1\le j\le d$ of

$$
\left(1+\frac{d}{dk-d+j}\right)
\left(1+\frac{d}{nd-dk-d+j}\right).
$$

Taking logarithms and summing gives the limit, and the first log-curvature follows from the adjacent-binomial formula.

## Vanishing scaled slack

Pass to a subsequence so that $(r-\mu)/\sqrt d\to h\in[0,\infty]$. If $h=0$, then $r/d\to x_0\in(0,1)$. The [endpoint estimate](saturated.md) shows that $\log(A_k^2/(A_{k-1}A_{k+1}))\to+\infty$, including when $k+1$ is exactly saturated. At each of these three quotas it also gives $V/d\to0$. Equation (1) and the cancellation for $K_k$ imply $\Gamma_k\to\infty$. This contradicts the necessary condition for a failed node.

## Positive or infinite scaled slack

If $0<h\le\infty$, the [central estimate](central.md) gives $V/d\to v>0$ and

$$
\Pr\left(\sum_iS_i=dk\right)\sim (2\pi nd v)^{-1/2}.
$$

The variance limit holds uniformly for any real quota shift in a bounded interval. The local probability estimate applies at every fixed integer shift with the same $v$. There are arbitrarily many available quotas on both sides of $k$, since $k/n\to x_0>0$ and $D-k=\lfloor(n/d)(r-\mu)\rfloor\to\infty$.

Set $E(k)=n\log H(z)-dk\log z$ at the row tilt chosen for the (possibly real) quota. Differentiation gives $E''(k)=-d^2/(nV)$, which tends uniformly on bounded shifts to $-\delta/v$. At integer quotas $A_k=e^{E(k)}\Pr(\sum S_i=dk)$. Integrating the second derivative with the triangular second-difference weight, then applying (1), gives

$$
\log\Gamma_{k+j}\longrightarrow g=\delta/v>0
$$

for every fixed integer $j$. The local probability prefactors have a common asymptotic equivalent, the variance corrections have a common limit, and the $K_k$ curvature tends to zero.

Normalize the magnitude of each term at $-t_k$ by the magnitude of its central term. For $j=1$ the normalized term equals $\Gamma_k^{-1/2}$. For $j\ge1$ its exact magnitude on the right is $\Gamma_k^{-j/2}\prod_{i=1}^{j-1}\Gamma_{k+i}^{-(j-i)}$, and on the left the same formula uses $k-i$. Set missing terms equal to zero. The local limits give $e^{-g j^2/2}$ at each fixed offset. The global bound $\log\Gamma_i\ge c_0>0$ holds for every internal $i$ for large $n$, by normalized log-concavity and $d/n\to\delta>0$. Thus the terms are dominated by the summable sequence $e^{-c_0j^2/2}$. Dominated convergence and Poisson summation for the Gaussian give

$$
\frac{(-1)^kP(-t_k)}{a_kt_k^k}
\longrightarrow \sum_{j\in\mathbb Z}(-1)^j e^{-g j^2/2}
=\sqrt{\frac{2\pi}{g}}\sum_{m\in\mathbb Z} e^{-2\pi^2(m+1/2)^2/g}>0 .
$$

This also contradicts failure. Every possible subsequence of failed internal nodes has now been excluded. The sign changes and the degree prove the theorem.
