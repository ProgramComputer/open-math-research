# Geometric signs at polynomially sublinear dimension

**Theorem.** Let $`\log n\ge10^6`$ and $`d\ge n^{.99}`$ with integer $`n,d`$. For every row cap $`1\le r\le d`$, every internal geometric node $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$ satisfies $`(-1)^kP(-t_k)>0`$. In particular all $`\lfloor nr/d\rfloor`$ zeros are simple and negative. Here $`a_k`$ counts labeled binary arrays with $`n`$ rows, $`d`$ columns, row sums at most $`r`$, and all column sums equal to $`k`$, and $`P(q)=\sum_{k=0}^{\lfloor nr/d\rfloor}a_kq^k`$.

The support is the interval from zero to $`D=\lfloor nr/d\rfloor`$ by the cyclic construction in [the logarithmic bound](README.md). Degrees zero and one follow immediately. At an internal index put $`b_k=\log(a_k^2/(a_{k-1}a_{k+1}))`$. For $`d\ge n`$ the orientation inequality gives $`b_k\ge4d/(n+2)>\log4`$ at every internal index. At any such index the normalized first neighbors at $`-t_k`$ have total magnitude $`2e^{-b_k/2}<1`$, and the two subsequent alternating tails begin with positive terms and decrease in magnitude. This gives the required sign. Otherwise set $`s=d/n`$. At a difficult index with $`b_k=\log(a_k^2/(a_{k-1}a_{k+1}))\ge100/\log n`$, the [finite-window argument](angular-overlap.md) gives the geometric sign. If $`b_k<100/\log n`$, at the tilt giving $`\mu=dk/n`$ it gives $`nV/d^2>u/110`$ and $`nx(1-x)/d>u/200`$, where $`x=k/n`$, $`u=\log n`$. At the geometric tilt $`v=t_k^{1/d}`$ these imply

$$
nV_v/d^2>u/111,\qquad n a_v/d>u/111,\qquad
a_v=\mathbb E_v[S(d-S)/(d(d-1))].
$$

For this transfer let $`w_k`$ be the real tilt of mean $`dk/n`$. The [phase calculation](angular-phase-calibration.md) gives $`|\log(v/w_k)|<3/d`$. On the tilt segment the likelihood ratio at any size is between $`e^{-3}`$ and $`e^3`$, so the variance remains above $`e^{-3}V_k`$ by its characterization as the minimum mean squared distance to a constant. The uniform third-moment estimate applies on the segment and bounds $`|(\log V)'|`$ in log tilt by $`10^9\sqrt d/2`$. Thus $`nV_v/d^2>u/111`$. The tilted capped-binomial variance bound gives $`V_v\le d a_v`$, which suffices for the second inequality. [Transfer proof](angular-phase-review.md)

For that real tilt the coefficient definition and Fourier orthogonality give the exact identity

$$
P(-v^d)/H(v)^n=\int_{\prod z_j=-1}
\big(\mathbb E_v\prod_{j\in I_S} z_j\big)^n\thinspace{}dz ,
$$

where $`H(v)=\sum_{j\le r}\binom dj v^j`$ and $`dz`$ is normalized Haar probability on the translated codimension-one torus. Each monomial in the expansion integrates to zero unless the column sums agree, and its surviving power of $`\prod z_j`$ is $`(-1)^k`$. The principal angular terms are conjugates. Their common complex Gaussian leading term at $`t=\pi/d`$ has phase $`n\arg H(ve^{it})-\frac{d-1}{2}\arg a_v(t)`$ with the numerator $`a_v(t)=\mathbb E_v[a_S e^{itS}]/\mathbb E_v e^{itS}`$. By [the calibration](angular-phase-calibration.md), this differs from $`k\pi`$ by less than $`n^{-1/10}`$. In particular the signed sum of these two Gaussian terms exceeds $`1.9|G_t|`$.

The [principal-chart estimate on the ball of radius two fifths](angular-principal-lower.md) costs less than $`0.02|G_t|`$ on each of the two principal charts. On the remaining near charts, on the remote charts, and outside all charts the [large-radius integral bounds](angular-mass-dominance.md#larger-radius-global-version-at-the-original-row-cutoff) each cost less than $`0.01|G_t|`$. Thus the signed integral is greater than $`(1.9-0.07)|G_t|>0`$ after multiplication by $`(-1)^k`$.

All internal curvatures are positive by the orientation inequality, hence $`0<t_1<\cdots<t_{D-1}`$. The signs at zero, at the negative geometric nodes, and sufficiently far to the left alternate. They give $`D`$ disjoint negative intervals containing roots. The degree is $`D`$, so each root is simple. $`\square`$

Independent agent-assisted reviews cover [the overlap and phase calibration](angular-phase-review.md) and [the chart estimates and signed sum](angular-chart-review.md). The latter reviewer developed the phase calibration and reviewed the integration estimates independently. The former reviewer independently checked the phase and [the principal estimates at the stated row threshold](angular-lower-review.md). The formal status of this all-cap partial theorem is ⬜ None.
