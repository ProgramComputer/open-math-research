# Independent review and derivation of the fixed lower-quota signs

Independent mathematical review by the quota referee (agent-assisted), 2026-11-26. I find the proposed strict sign valid. For each fixed positive integer $k$ there is a dimension threshold such that, for all $n\ge d$ and all proper caps $1\le r<d$ with $k<\lfloor nr/d\rfloor$, the unique exact angular node gives $(-1)^k P_{n,r,d}(-w_k^d)>0$. The dimension threshold is existential. The review uses the repository's exact angular ordering and normalized log-concavity. [Theorem statement](fixed-lower-quota-signs.md) · [Original problem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Angular ordering](../README.md) · [Normalized log-concavity](../../orientation-normalization.md)

Write $\theta=\pi/d$, $\nu=(d-1)/2$, $H(z)=\sum_{s=0}^r\binom ds z^s$, $\widetilde H(z)=\sum_{s=0}^r q_s\binom ds z^s$ with $q_s=s(d-s)/(d(d-1))$. The exact node solves

$$
\Psi(w)=n\arg H(we^{i\theta})-\nu\arg\bigl[\widetilde H(we^{i\theta})/H(we^{i\theta})\bigr]=k\pi .
$$

The ordered-angle theorem applies throughout $n\ge d$. Take the continuous arguments from that theorem, so $\arg(\widetilde H/H)$ along the ray tends to $\theta$ as $w\downarrow0$. Let $T_m=a_{n,m}w_k^{dm}$ be the nonnegative magnitude of the term at quota $m$.

## Finite limiting aspect ratio

Consider a sequence $d\to\infty$ with $n/d\to\lambda\in[1,\infty)$ and, on a subsequence, $r\to R\in\mathbb N\cup\lbrace\infty\rbrace$. Write $E_R(x)=\sum_{s=0}^R x^s/s!$, with $E_\infty=e^x$, $\mu(x)=xE_R'(x)/E_R(x)$ and $v(x)=x\mu'(x)/\mu(x)$. On compact positive $x$ intervals, $H(x/d)$ tends to $E_R(x)$ and $d\widetilde H(x/d)$ tends to $xE_R'(x)$, together with their first two derivatives in $\log x$. For this, coefficients are bounded by $1/s!$ after scaling for $H$, and by $s/s!$ for $d\widetilde H$. The bounds still hold up to the appropriate polynomial factors in $s$ after derivatives, and apply equally at complex angle near zero. Both limits are positive on the real interval. At angle zero the angular derivative of each argument equals the derivative of the logarithm of its positive real value with respect to $\log x$. The angular Taylor expansion has error $O(\theta^2)$ uniformly on the compact interval. Consequently

$$
\frac{\Psi(x/d)}{\pi}\ \longrightarrow\ \lambda\mu(x)-\frac{v(x)}2.
$$

Indeed the logarithmic derivative of the limiting quotient $xE_R'(x)/E_R(x)$ is $v(x)$. The limit of the displayed expression as $x\downarrow0$ is $-1/2$. At $x\to\infty$ it is $\lambda R\ge k+1$ when $R<\infty$, using the internal-quota assumption and the fact that then $r=R$ eventually. For $R=\infty$ the limit is $+\infty$. Select a fixed small and large $x$ giving strict inequalities on either side of $k$. The monotonicity of the exact phases traps $x_d=dw_k$ between them. Every limit point $x$ of $x_d$ thus satisfies $u=\lambda\mu(x)=k+v(x)/2$.

## Counting on the exponential scale

Fix an integer $m\ge1$. For a fixed finite cap $R$, allocate the $dm$ labeled stubs, $m$ of each of $d$ columns, to the rows. For a fixed vector of row occupancies $(s_i)$, all allocations may be sampled by a uniform permutation over $dm$ labeled row slots. The expected number of unordered same-column same-row stub pairs is at most

$$
d\binom m2\thinspace{}\frac{R-1}{dm-1}=O_{R,m}(1).
$$

Choose a fixed integer $K=K(R,m)$ so at least half the permutations have at most $K$ collisions. If row $i$ has a repeated column $C$, choose one repeated stub there and swap with a slot whose row does not contain $C$ and whose column is absent from row $i$. The former restriction excludes at most $mR$ slots and the latter at most $Rm$ slots. Such a slot therefore exists for $dm>2mR$. This swap decreases the collision count and preserves each row occupancy. Use any fixed deterministic repair procedure. Each collision-free output has at most $\sum_{j=0}^K(dm)^{2j}$ input permutations within $K$ swaps. Thus the relative number of collision-free allocations lies between an inverse polynomial in $d$ and one, uniformly in the occupancies. Slot labels give the same multiplicity $\prod_i s_i!$ for every assignment of a fixed occupancy profile, so the relative bound remains valid after summing profiles.

Ignoring collisions gives $(dm)![z^{dm}]E_R(z)^n$ allocations. Every collision-free array has exactly $(m!)^d$ stub labelings. This proves equality of the exponential rates of $a_{n,m}$ and $(dm)![z^{dm}]E_R(z)^n/(m!)^d$. For interior $0<m<\lambda R$ take $y_d>0$ satisfying $\mu(y_d)=dm/n$. These tilts converge to $y_m$ with $\lambda\mu(y_m)=m$. Under the corresponding independent tilted row laws, the probability of total $dm$ is bounded below by an inverse polynomial. To see it, take the integer counts of sizes $2,\ldots,R$ to be the floors of $n$ times their probabilities, and choose counts of sizes one and zero to achieve the prescribed total and exactly $n$ rows. Both adjusted counts differ from their expected values by $O_R(1)$ and are positive for large $d$, since their limiting probabilities are positive. Stirling's estimate for this one multinomial probability gives $\exp[-O_R(\log n)]$. For $R=1$ the same argument uses just sizes zero and one. The upper bound one completes the coefficient rate.

For a possibly varying cap with finite limit $R$, the cap equals $R$ eventually. If the cap tends to infinity, the unrestricted stub calculation with $e^z$ is an upper bound; every fixed cap $M$ is a lower bound for large enough $d$. For $M\to\infty$, the compact convergence of $E_M$ and its derivatives gives convergence of the saddle solving $\lambda\mu_M(y)=m$ to $m/\lambda$, and then convergence of the rate. For $m=\lambda R$ with finite $R$, an upper bound is enough. Apply the coefficient estimate at any fixed $y>0$ and take $y\to\infty$ to get the endpoint contribution $-\lambda\log(R!)$. This applies even if feasible quotas approach that endpoint with varying $n/d$ or only a small gap to full occupancy. At $m=0$ the magnitude is exactly one.

Combining these observations with Stirling on $(dm)!$ and $x_d\to x$ gives, for interior $m$, the limit of $d^{-1}\log T_m$ as

$$
f(m)=m\log m -m-\log(m!)
  +\lambda\log E_R(y_m)-m\log y_m+m\log x .
$$

At $m=\lambda R$ the same expression with its continuous entropy limit is an upper bound on the limsup, and $f(0)=0$. In particular the exact rate at the central index $k$ is interior.

## Strict neighboring rates

For finite $R$, let $S$ have probabilities $p_j$ proportional to $x^j/j!$ on $0\le j\le R$. Its Stein kernel is

$$
\tau_i=\frac{\sum_{j\le i}(\mu-j)p_j}{p_i}
  =x-(x-\mu)\frac{\Pr(S\le i)}{p_i}.
$$

Here the second equality uses $jp_j=xp_{j-1}$. The ratio equals $\sum_{h=0}^i(i)_h/x^h$ and is increasing in $i$, while $\mu\le x$. Thus $\tau_i$ is nonincreasing. Summation by parts gives $V=\mathbb E\tau_S$ and the third cumulant $\kappa_3=V+2\thinspace{}\mathrm{Cov}(S,\tau_S)\le V$. The tilt derivatives $x\mu'(x)=V$ and $xV'(x)=\kappa_3$ therefore imply $\mu''(x)\le0$. The untruncated case has $\mu(x)=x$. In all cases $0<v(x)\le1$.

For real $t$ in the interior of the mean range let $\lambda\mu(y_t)=t$, and put $G(t)=tx/y_t$. Then $G(t)$ is nonincreasing because $\mu(y)/y$ is nonincreasing. The derivative of $\lambda\log E_R(y_t)-t\log y_t$ is $-\log y_t$. For integer neighbors this yields

$$
f(m+1)-f(m)=\int_m^{m+1}\log G(t)\thinspace{}\mathrm{d}t-\log(m+1).
$$

This holds at the two possible continuous extensions. As $t\downarrow0$, $y_t\sim t/\lambda$, the entropy term tends to zero and $G(t)\to\lambda x$. At a finite upper endpoint $t\uparrow\lambda R$, $y_t$ grows on the order of $1/(\lambda R-t)$ by expansion at infinity. The entropy tends to $-\lambda\log(R!)$ and the log singularity in the integral is integrable. For the actual right endpoint term, use only the upper rate bound described above.

We have $G(k)\ge G(u)=u$ since $u>k$. Also concavity gives

$$
\lambda\mu'(x)(x-y_k)\le u-k=\frac{x\mu'(x)}{2\mu(x)}.
$$

This makes $y_k\ge x(1-1/(2u))$ and $G(k)\le 2ku/(2u-1)<k+1$, using $k\ge1$ and $u>k$. The upper limiting bounds for the neighboring ratios, after taking roots of order $d$, are $k/G(k)$ and $G(k)/(k+1)$.

The proposed numerical uniform separation is also valid. For finite $R$, take $T>0$ with density proportional to $e^{-t}(x+t)^R$ and let $S\mid T$ have law $\mathrm{Bin}(R,x/(x+T))$. Integration gives mass proportional to $x^j/j!$ since $\binom Rj(R-j)!=R!/j!$. The variance decomposition gives $V\ge\mu(1-\mu/R)$. As $\lambda R\ge k+1$, this yields $v\ge 1-u/(k+1)$, and $u=k+v/2$ gives $u\ge k+\delta$, where $\delta=1/(2k+3)$. This bound also holds for $R=\infty$ since $v=1$. Together these facts bound the left and right root-ratios above by

$$
\frac{k}{k+\delta},
\qquad
\frac{2k(k+\delta)}{(k+1)(2(k+\delta)-1)}.
$$

Both are strictly below one. For the second bound, $2ku/(2u-1)$ decreases in $u$ and is less than $k+1$ for $u>k$.

## Infinite limiting aspect ratio and uniformity

If $n/d\to\infty$, put $w=W/n$ and $x=dW/n$. At fixed compact positive $W$, $x\to0$. The coefficient bounds as above give $H(we^{i\alpha})=1+x e^{i\alpha}+O(x^2)$ and $d\widetilde H(we^{i\alpha})=x e^{i\alpha}(1+O(x))$, including uniform control of their angular derivatives for $|\alpha|\le\theta$. More precisely the remainder terms and their angular derivatives are $O(x^2)$, by domination of the terms of order at least two. Integrating the argument derivatives from $\alpha=0$ shows $\arg H=\theta x+O(\theta x^2+\theta^2 x)$ and $\arg\widetilde H=\theta+O(\theta x)$. Thus $\Psi(W/n)/\pi\to W-1/2$. Exact monotonicity traps the nodes and gives $W=nw_k\to k+1/2$.

For fixed $m$, the inequality $dm\le n$ holds eventually. The cap-one and unrestricted counts give the lower and upper bounds

$$
\frac{(n)_{dm}}{(m!)^d}\le a_{n,m}\le\binom nm^d.
$$

The log of $(n)_{dm}/n^{dm}$ divided by $d$ lies between $m\log(1-dm/n)$ and zero. Both bounds therefore show $T_m^{1/d}\to (k+1/2)^m/m!$, with $m=0$ immediate. The neighbor root-rates are at most $k/(k+1/2)$ and $(k+1/2)/(k+1)$.

Each sequence of dimensions tending to infinity has a subsequence with finite or infinite limiting aspect ratio. In the finite case refine to a finite or infinite limiting cap and a convergent trapped tilt. The uniform limsup of the maximum of the neighboring ratios, after taking roots of order $d$, is therefore bounded by the maximum of the two displayed finite-aspect constants and $(k+1/2)/(k+1)$, strictly below one. Finally normalized log-concavity gives ordinary log-concavity because $\binom nm^d$ is log-concave. Multiplication by $w_k^{dm}$ preserves it. All supported terms form an interval starting at zero. Starting from either neighbor, the outward sequence then decreases at least geometrically at the respective neighbor ratio. Writing $\rho_d$ for the maximum absolute neighbor ratio $T_{k\pm1}/T_k$, the total competing magnitude is at most $2T_k\rho_d/(1-\rho_d)=o(T_k)$ uniformly in $(n,r)$. Thus the parity sign is strict.

The rightmost possible competitor $k+1=\lambda R$ and the left competitor $k-1=0$ are covered above. No cutoff for growing $k$ or for all $d$ follows from this argument. The proof does not require the transverse Fourier integral.
