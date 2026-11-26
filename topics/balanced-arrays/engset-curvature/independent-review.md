# Independent review of carried-load curvature and finite extensions

Signed by agent-assisted reviewer four_blind, 2026-11-26.

**Verdict.** The carried-load differential inequality and the three fixed-shape asymptotic regimes for the actual extension sequence check out. The global finite extension-concavity assertion is a conjecture. The compact interior, fixed lower quota, and fixed upper deficit results leave moving boundary windows with diverging distances untreated.

## Engset source and variance comparisons

I checked the [corrected Azimzadeh–Carpenter paper](https://arxiv.org/pdf/1511.00291v5), especially its Engset formula, Lemma 2, and §5 Theorem 7. The source uses $N=d$ sources and $m=r$ servers. Its call-blocking expression at idle-source intensity $z$ uses the $d-1$ other sources, giving $B=\binom{d-1}{r}z^r/G_r(z)$. The paper’s Lemma 2 concerns varying the trial probability $P$ at fixed offered parameter $\alpha$, hence affine changes in inverse intensity $1/\alpha-1+P$. It does not differentiate in the actual carried load $x$. Theorem 7 does apply to an intermediate quantity in this proof. Use its parameters $b=r-1$ and $c=d-r+1$, for $r\ge2$. Coefficient ratios give $U(y)/U(0)=h_0(y)$ and $h'_0=(b/c)h_1$. Therefore the decrease of $h_1/h_0^2$ proves convexity of $1/U$. The elementary coefficient argument gives strict pointwise positivity of the second derivative for the binomial coefficients in question. The derivative input and the change of differentiation variable should be credited distinctly. [Version of record](https://doi.org/10.1016/j.orl.2016.02.011)

The variance estimates also follow from the classical same-mean convex-order crossing criterion. In particular the **lower** bound is a comparison with $Y\sim\mathrm{Bin}(r,dx/r)$. The consecutive ratios of the likelihood ratio $\Pr(S=j)/\Pr(Y=j)$ increase strictly for $r\ge2$, since they are a constant times $(d-j+1)/(r-j+1)$ at step $j$. Thus the signed mass difference has signs positive, negative, positive in order, with exactly two crossings after ignoring zeros. Normalization and equality of means exclude a single crossing unless the laws agree. Subtracting the chord of any convex function through the crossing points proves $Y\le_{\mathrm{cx}}S$. For the strictly convex quadratic the comparison is strict. At $r=1$ the laws agree. The **upper** bound compares with $Z\sim\mathrm{Bin}(d,x)$. The tilted law is log-concave relative to $Z$ since their log-ratio is affine on $0,\ldots,r$ and its support is truncated. The same crossing argument now gives $S\le_{\mathrm{cx}}Z$, with strict variance inequality since $r<d$. Thus the two variance bounds are standard convex-order consequences, also obtained from the differential argument. [Karlin–Novikoff crossing method](https://doi.org/10.2140/pjm.1963.13.1251) · [Whitt, relative log-concavity and variability](https://doi.org/10.2307/3213865)

I checked the identities $e^{-g}=1-B$, $w=y+1/U$, and the chain rule for $g''$. They give
$$
g''-(g')^2-\frac{2g'}{1-x}=\frac{(1+w)^4 w''}{y(w')^3}.
$$
Here $w'>0$ by strict monotonicity of the carried-load map and $w''\ge0$ by reciprocal convexity. In the coefficient argument the bracket and the products $u_i u_{N-i}$ are symmetric and both are nondecreasing toward the midpoint, including support zeros. At $r\ge2$ the constant coefficient $2(u_1^2-u_0u_2)$ is strictly positive. Writing $J=d/V-1/x$ gives $J'-J^2=g''-(g')^2-2g'/(1-x)$. Differentiating $V$ with respect to $x$ gives $V'=d\kappa_3/V$, which yields exactly the stated third cumulant inequality.

## Actual extension regimes

Deletion of one entry per column gives exactly $(k+1)^d$ choices per destination array and proves the average extension formula. For the interior proof, the empty subset and every singleton in each tilt give a uniform torus gap away from zero and uniform positive covariance on a compact density interval. For bounded scaled frequency the logarithmic Taylor terms through degree seven retain orders through $n^{-5/2}$. The degree-eight remainder and the exponential remainder are $O(n^{-3})$ times a fixed polynomial in scaled frequency against the Gaussian majorant. Integrating the odd terms on the symmetric domain gives zero. This is enough control on adjacent differences of $\log a_k$, even if the error term itself is not differentiable. The $O(n^{-3})$ error becomes $O(n^{-2})$ in $u_k$ after taking adjacent differences and multiplying by the leading factor of order $n$. The perspective identity is $h''(x)=Y''(w)/x^3$, and because $w'>0$ and $w''>0$, $Y''(w)=-w''/(w')^3<0$.

At fixed positive lower quota, the first failure-probability term is $-\binom{d}{r+1}k^{r+1}n^{-r}$ in $\log p_k$. The two-row event error after summing over pairs is $O(n^{-2r})$, contained in the written $O(n^{-r-1})$ for the stated range. Thus $u_k=(n-k)-\binom d{r+1}\Delta(k^{r+1})n^{1-r}/d+O(n^{-r})$ for each fixed quota, which gives the claimed third forward difference after centering the second difference. The third forward difference is positive even at the smallest allowed center because it is an integral of the positive third derivative off the zero endpoint.

At fixed excess $e$ the projected covariance of a uniform $r$-subset on the first $d-1$ labels is
$$
\Sigma=\lambda\left(I_{d-1}-\frac{\mathbf1\mathbf1^{\mathsf T}}d\right),
\qquad
\lambda=\frac{r(d-r)}{d(d-1)}.
$$
The determinant is $\lambda^{d-1}/d$. The projected support differences contain each unit vector by exchanging it with label $d$, so the lattice span has unit covolume and there is a single Fourier peak. Consequently the Gaussian factor is
$$
C_{d,r}=\frac{\sqrt d}{(2\pi\lambda)^{(d-1)/2}}.
$$
Conditioning on any of the finitely many possible defective-row patterns moves the first $d-1$ target margins only a bounded distance from their mean. This stays in the same Gaussian regime, including $e=0$ in its feasible residue class. The remaining column equation follows from the prescribed total. There are $O(n^{e-1})$ choices for all profiles with fewer than $e$ defective rows, so the same local bound makes their contribution lower order. The stated falling-factorial limit for $u_k$ and its strict concavity follow. A fixed distance $D-k\ge2$ leaves the third extension nonzero, even when the residue $nr\bmod d$ is zero.

## Conditional normalized third difference and replay

Set $q_k=p_{k+1}/p_k=(u_k/(n-k))^d$. Normalized log-concavity makes $q_{k+1}\le q_k$, so $v=u_k-u_{k+1}\ge u_k/(n-k)$. If the finite concavity inequality holds at $k$, then
$$
u_{k-1}u_{k+1}\le u_k^2-v^2\le u_k^2\left(1-\frac1{(n-k)^2}\right).
$$
The last factor is exactly $(n-k-1)(n-k+1)/(n-k)^2$. Dividing by the appropriate parallel affine factors proves $q_k^2\ge q_{k-1}q_{k+1}$. Equivalently, $\Delta^3\log p_{k-1}\le0$ and the normalized curvature at $k+1$ is at least its value at $k$. These conclusions hold only at centers $1\le k\le D-2$ where the three positive extension values exist and the additional concavity hypothesis is known.

I replayed the pinned archive screen. It read 1,659 distinct vectors and certified all 14,570 tested interior differences. At dyadic scale $2^{256}$, integer flooring of each $d$th root bounds the error by one unit, so the difference error has absolute value less than two units. These observations certify the tested set. They do not prove the global finite inequality.

## Conditional linear dimension bound

I also checked the tilted sign argument in [curvature-reduction.md](curvature-reduction.md). At a difficult index $G_k\le4$, the sector proof’s binomial inequality localizes $k$ to $(.23n,.77n)$ using only $d\ge n/4$, independently of its high-cap theorem. On $[k-1,k]$ the derivative of $\log g$ is bounded in absolute value by $2/(.228^2n)$ when $d<n$. The exponential of this bound is at most $1/(1-\eta)<1001/1000$, where $\eta=2/(.228^2\cdot65536)$. Since $G_i/g_i$ is exactly the normalized curvature, the stipulated inequality from $k-1$ to $k$ gives $G_{k-1}<(1001/1000)G_k$.

For the tilted node $sx_k$ the first left magnitude is $1/(s\sqrt{G_k})$, the second is $1/(s^2G_kG_{k-1})$, and the ratio of third to second is $1/(s\sqrt{G_k}G_{k-1}G_{k-2})$. Both tails decrease outward by strict log-concavity, so the unretained paired terms have nonnegative total. The nodes are strictly ordered even at an unshifted-to-shifted join since $x_{k+1}/x_k=\sqrt{G_kG_{k+1}}>13/4>1/s$.

With $a=s+1/s$, the lower function $1-a/\sqrt G+b/G^2$ uses rational $0<b<B$. Positivity at $G=m$ is exactly the checker’s first squared comparison between positive quantities. The second squared comparison proves $aG^{3/2}>4b$ for all $G\ge m$, which is precisely the derivative sign. The lower curvature bound follows from the positive Taylor terms for $\exp((59/50)n/(n+2))$ and their monotonicity with $n$. Thus the statement gives a real-rootedness theorem **conditional** on precisely the stated adjacent normalized-curvature hypotheses. It supplies no unconditional proof at slope $59/200$.
