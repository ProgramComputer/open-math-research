# All zeros at a rank-dependent dimension bound

This result concerns the original labeled arrays in Per Alexandersson’s balanced-array conjecture for uniform matroids. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**Theorem.** For each fixed $0<\varepsilon<1/5$ there are constants $C_\varepsilon>0$ and $N_\varepsilon\ge3$ with the following property. Let $n\ge N_\varepsilon$ and $1\le r\le d$ be integers. Suppose

$$
d\ge C_\varepsilon\sqrt{\frac{nr}{\log n}}
\quad\text{and}\quad
\left(r\le n^{1/5-\varepsilon}\ \text{or}\ d\ge n^{3/4+\varepsilon}\right).
$$

Then the balanced-array polynomial has precisely $D=\lfloor nr/d\rfloor$ simple negative zeros. In particular, for every fixed cap $r$, all sufficiently large $n$ and all $d\ge C_r\sqrt{n/\log n}$ have this property. The constants are existential. The conclusion concerns the polynomial that counts labeled binary matrices by their common column sum, for the original row cap. The remaining parameters of [Alexandersson's conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) are open.

Here is one family covered by the first alternative. Take $r=2$ and $d=\lceil\sqrt n/(\log n)^{1/4}\rceil$. For large $n$ the ratio of the displayed dimension to $\sqrt{nr/\log n}$ tends to infinity. For an example covered by the second alternative, take $d=\lceil n^{4/5}\rceil$ and $r=\lfloor n^{3/5}\sqrt{\log n}\rfloor$, with $\varepsilon=1/40$.

## A weak coefficient ratio and its neighborhood

Write $P(q)=\sum_{i=0}^D a_iq^i$. All its coefficients through $D$ are positive: assign the $i$ ones in each column cyclically along consecutively repeated row labels. Every row then has at most $\lceil di/n\rceil$ ones. For $1\le i<D$ set $t_i=\sqrt{a_{i-1}/a_{i+1}}$ and $\Gamma_i=a_i^2/(a_{i-1}a_{i+1})$. The [orientation inequality](../../orientation-normalization.md) gives

$$
\Gamma_i\ge (1+1/i)^d(1+1/(n-i))^d>1.
$$

The $t_i$ increase strictly. If $(-1)^iP(-t_i)>0$ throughout, the signs at zero, at these nodes and at large negative argument give $D$ distinct negative roots. Further, $\Gamma_i>4$ forces the sign at $i$: each adjacent term has magnitude $1/\sqrt{\Gamma_i}$ relative to the central term, and the remaining outward alternating tails start positive with decreasing magnitudes. Degrees zero and one are immediate.

Suppose there were no uniform constants. Choose a sequence of exceptions with $n\to\infty$ and $d/\sqrt{nr/\log n}\to\infty$. Retain a subsequence lying in one of the two alternatives. The [logarithmic dimension theorem](../logarithmic-window.md) implies $d\log n/n$ is bounded on the exceptions. Put $\delta=d/n$, $b=d^2/n$ and $J=\lceil(\log n)^2\rceil$. We have

$$
\frac{b\log n}{r}\longrightarrow\infty,\qquad
\frac rd=\frac{r}{b\log n}\delta\log n\longrightarrow0.
$$

Choose a failed internal node $k$ for each exception. The necessary inequality $\Gamma_k\le4$ implies $k\ge d/\log4-1$. As $k\le nr/d$, we get $b=O(r)$. We also have $b\ge1/\log n$ and $d\ge\sqrt{n/\log n}$ eventually. At every feasible real quota $u$ with $|u-k|\le J+2$, write $p=u/n$ and $\mu=du/n$. Throughout this window $u\ge c d$, $\mu\ge cb$ and $p\le r/d=o(1)$, with an absolute $c>0$. At every internal index, including those outside the window,

$$
\log\Gamma_i\ge \frac{d}{i+1}\ge\frac{d}{D+1}\ge c_0\frac br
$$

for a fixed $c_0>0$ and large $n$. The last bound uses $D+1\le nr/d+1$ and $nr/d\ge k\to\infty$.

## The cost of fixing the column sums

Set $H(z)=\sum_{s=0}^r\binom ds z^s$. At a real quota $0<u<nr/d$, let $S$ have probabilities proportional to $\binom ds z^s$ on $0,\ldots,r$, with its mean fixed at $\mu$. The unique $z>0$ exists since the derivative of the mean in $\log z$ is its positive variance $V(u)$. At the endpoints take deterministic laws. We have $V\le \mu(1-p)\le r$ by comparison with a binomial of mean $\mu$. Define $E(u)=n\log H(z)-du\log z$. It extends continuously to the endpoints by the entropy identity for the tilted row and satisfies $E''(u)=-b/V(u)$ in the open interval.

For an integer $i$ in the window let $L_i$ be the probability that $n$ independent such rows at quota $i$ have total size $di$. The scalar coefficient $[z^{di}]H(z)^n$ is $e^{E(i)}L_i$. Its conditional row profiles have weights proportional to $\prod_j\binom d{s_j}$. Applying the [Greenhill–McKay–Wang estimate](small-rank-margins.md) in the first alternative and the [Liebenau–Wormald estimate](large-dimension-margins.md) in the second gives, uniformly on feasible integer quotas in the window,

$$
\log a_i=\log K_i+E(i)+\log L_i-\tfrac12+B_i+O(n^{-\beta}),\qquad
K_i=\frac{\binom ni^d}{\binom{nd}{di}},\qquad
B_i=\frac{V(i)}{2\mu(1-p)}
$$

for some $\beta>0$. Both estimates include exact saturation. Also $0\le B_i\le1/2$ and $1/(nr+1)\le L_i\le1$. For the lower bound, interpolate the logarithm of the log-concave lattice mass of the sum linearly, then apply Jensen at its integer mean. Its entropy is at most $\log(nr+1)$.

Put $\mathcal D f(i)=2f(i)-f(i-1)-f(i+1)$. For neighboring feasible quotas in the window we have $|\mathcal D\log K_i|=O(d/i^2+d/(n-i)^2)=O(1/d)$. In the denominator's adjacent binomial ratio, the $d$ factors $1+d/(di-d+h)$, $1\le h\le d$, each have logarithm differing from $\log(1+1/i)$ by $O(i^{-2})$. The other $d$ factors have the corresponding estimate with $n-i$ in place of $i$. The numerator contributes exactly $d$ copies of each limiting logarithm.

## Near and away from zero variance

The [lattice estimates](small-variance.md) give $|dV/d\mu|\le C(1+\sqrt V)$ and, when $n\min(1,V)\ge1$,

$$
L_i=(2\pi nV(i))^{-1/2}
\left(1+O\bigl((n\min(1,V(i)))^{-1/2}\bigr)\right).
$$

In particular $\sqrt{1+V}$ is Lipschitz in $\mu$ with absolute constant. This extends up to the deterministic endpoints by continuity. Writing $V_k=V(k)$, we obtain on any feasible interval $|u-k|\le h$,

$$
|V(u)-V_k|\le C\left(\sqrt{1+V_k} \delta h+\delta^2h^2\right).
$$

Choose $\eta=1/16$. If $V_k<b n^{-\eta}$, the last inequality implies $V(u)\le Cb n^{-\eta}$ at $|u-k|\le1$. Indeed $\delta=\sqrt{b/n}$, $b\ge1/\log n$, and each of $\delta$, $\sqrt{b n^{-\eta}} \delta$ and $\delta^2$ is $O(b n^{-\eta})$. On the central half of the unit window, the entropy curvature is at least $c_1n^\eta$ in magnitude. Concavity gives $\mathcal D E(k)\ge c_2 n^\eta$ by the triangular second-difference integral. If an outer endpoint is exactly saturated, retain the central half of the integral and use concavity and continuity on the rest. The probability terms cost at most $2\log(nr+1)$ and all other contributions to $\log\Gamma_k$ are bounded. This contradicts $\Gamma_k\le4$.

Now suppose $V_k\ge b n^{-\eta}$. On the whole feasible part of the window $h=J+2$, the relative variation of $V$ is bounded by

$$
C\left[\left(n^{\eta-1/2}/\sqrt b+n^{(\eta-1)/2}\right)h
+n^{\eta-1}h^2\right].
$$

It is smaller than a fixed negative power of $n$. In fact this estimate, multiplied by $n^\eta$, is still smaller than a fixed negative power, since $b\ge1/\log n$. Neither deterministic endpoint $u=0$ nor the real upper endpoint $u=nr/d$ can lie in this window, since each has variance zero. This excludes the upper endpoint even when it is nonintegral. Thus all integer offsets through $J+1$ exist on both sides. Write $g=b/V_k\le n^\eta$. The resulting bound on $|E''(u)+g|$ is $O(n^{-\gamma})$ throughout for some $\gamma>0$. We also have $nV(u)\ge c n^{1-\eta}/\log n$. The local limit estimate shows that $\log L_i$ differs from $-\tfrac12\log(2\pi n V_k)$ by a negative power of $n$ uniformly.

For the correction $B(u)=V(u)/(2\mu(1-p))$, write $v=\mu(1-p)$. Its derivative satisfies $|dv/du|\le\delta$. The variance derivative bound and $V\le v$ give $|B'(u)|\le C\delta(1+\sqrt v)/v$. Since $v\ge c b$ in the window, its total variation is $O(h(1+b^{-1/2})/\sqrt n)$. Integrating $-E''$ against the triangular weight of mass one and using the remaining estimates gives, with a fixed $\kappa>0$,

$$
\log\Gamma_{k+j}=g+O(n^{-\kappa})\qquad(|j|\le J).
$$

In particular $b/r\le g\le\log4+O(n^{-\kappa})<2$.

## Recovering all signs

For $j\ge1$ the magnitude of the term at offset $j$ or $-j$ at $-t_k$, divided by $a_k t_k^k$, is exactly $\Gamma_k^{-j/2}\prod_{\ell=1}^{j-1}\Gamma_{k\pm\ell}^{-(j-\ell)}$ when that term exists. Missing terms have magnitude zero. The global lower bound on curvature bounds every magnitude by $\exp(-c_0bj^2/(2r))$. On $|j|\le J$ the magnitude is $\exp(-gj^2/2+O(j^2n^{-\kappa}))$. Thus the normalized signed polynomial differs from $\sum_{j\in\mathbb Z}(-1)^j e^{-g j^2/2}$ by at most

$$
O(J^3n^{-\kappa})+
O\left((r/b)^{1/2}\exp(-c_3 bJ^2/r)\right)=O(n^{-\kappa'})
$$

with $\kappa'>0$. Indeed $b/r$ is bounded above on the failed sequence and $b\log n/r\to\infty$. Poisson summation gives

$$
\sum_{j\in\mathbb Z}(-1)^j e^{-g j^2/2}
=\sqrt{\frac{2\pi}{g}}\sum_{m\in\mathbb Z}
\exp\left(-\frac{2\pi^2(m+1/2)^2}{g}\right)
\ge\sqrt\pi\exp\left(-\frac{\pi^2r}{2b}\right).
$$

Because $r/b=o(\log n)$, this lower bound eventually exceeds the comparison error. The node succeeds, a contradiction. This proves the uniform theorem and hence the fixed-rank assertion.
