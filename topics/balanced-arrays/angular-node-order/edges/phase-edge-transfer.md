# True angular test points at the two ends of a fixed-dimension row

Fix $d\ge2$, $1\le r<d$ and $\theta=\pi/d$. Write $D=\lfloor nr/d\rfloor$, and let $w_k$ be the unique positive tilt at which the principal phase equals $k\pi$, so the test radius is $w_k^d$. These are the ordered nodes of the finite monotonicity theorem, which applies once $n\ge d$. [Angular node ordering](https://github.com/ProgramComputer/open-math-research/blob/b37c6be08b892ba4d2bd8a58fb6b2c491438d37a/topics/balanced-arrays/angular-node-order/README.md)

For each fixed positive integer $j$, the upper node $k=D-j$ has $(-1)^kP(-w_k^d)>0$ for all sufficiently large $n$. This uses the exact sign lemma for the root-of-unity section all the way down to $j=1$, at the actual phase node. At every fixed positive lower quota $k$ the corresponding limiting sign question reduces to the explicit hyper-Bessel value in the lower-edge section.

## Upper edge

Pass to a residue class $nr=dD+s$, $0\le s<d$, and let $w=w_{D-j}$. Put $c_m=\binom dm$, $\rho=c_{r-1}/c_r$, $\nu=(d-1)/2$, and $a_r=r(d-r)/(d(d-1))>0$. For any fixed positive tilt the argument of $H(we^{i\theta})$ is strictly below $r\theta$, because the coefficients include smaller powers and $r\theta<\pi$. At that tilt the phase divided by $n$ converges to the same argument. Monotonicity thus gives $w\to\infty$. At large $w$, the radial argument equals $r\theta-\rho\sin\theta/w+O(w^{-2})$, while the argument of the transverse coefficient tends to zero with error $O(1/w)$, since its leading term is the positive $a_r$. The phase equation becomes

$$
\pi(j+s/d)=\frac{n\rho\sin\theta}{w}\bigl(1+O(w^{-1})+O(n^{-1})\bigr).
$$

In particular $n\rho/w\to\lambda=\pi(j+s/d)/\sin\theta$.

On the torus $\prod z_i=-1$, divide the row polynomial by $c_rw^r$, and call the result $R_w(z)=\sum_{h=0}^r w^{h-r}e_h(z)/c_r$. Its limit in uniform norm is $e_r(z)/c_r$. This has modulus one only when all the coordinates coincide: equality in the triangle inequality makes every $r$-fold product equal, and two subsets differing in precisely one label then show equality of any two coordinates. Consequently the $n$-th power contributes exponentially little outside fixed disjoint neighborhoods of the $d$ common angles $t$ satisfying $dt=\pi$ modulo $2\pi$.

Use coordinates $z_i=e^{it+iy_i}$ with $\sum y_i=0$, and normalize $K_h(y)=e_h(e^{iy_1},\ldots,e^{iy_d})/c_h$. The row response after removal of $e^{irt}$ is $K_r(y)+(\rho/w)e^{-it}K_{r-1}(y)+O(w^{-2})$ uniformly. A uniform $r$-subset gives zero linear term and second moment $a_r\sum y_i^2$ in $K_r$, so $K_r(y)=1-a_r\sum y_i^2/2+O(\|y\|^3)$. On a sufficiently small fixed neighborhood its modulus is at most $1-c\|y\|^2$ for a positive $c$. The correction is $O(1/w)$ and $n/w$ is bounded. This dominates the absolute integrand after scaling $y=Y/\sqrt{n a_r}$ by a constant times $e^{-c'\|Y\|^2}$, and its pointwise limit after removing $e^{inrt}$ is $e^{-\|Y\|^2/2+\lambda e^{-it}}$.

Haar density on the chart is $1/[\sqrt d(2\pi)^{d-1}]$ in Euclidean hyperplane measure. Set $I_n=(2\pi n a_r)^{-\nu}/\sqrt d$. Dominated convergence on the finitely many charts and the row Fourier identity therefore give

$$
\frac{(-1)^k P(-w^d)}{(c_rw^r)^n d I_n}
\longrightarrow
\frac{(-1)^j}{d}\sum_{dt=\pi\pmod{2\pi}}e^{ist+\lambda e^{-it}}
=(-1)^j\sum_{h\ge0}\frac{(-1)^h\lambda^{s+dh}}{(s+dh)!}.
$$

The final equality follows by expanding the exponential and summing the $d$ roots. The limit is strictly positive by the [upper-edge sign lemma](angular-upper-edge-sign.md). Every attainable residue gives the same strict sign, so the conclusion holds for all sufficiently large heights at the fixed $d,r,j$.

## Lower edge

At any fixed positive tilt the radial argument lies strictly above zero. Thus for $k$ fixed, monotonicity gives $w_k\to0$. Now $H(we^{i\theta})=1+dwe^{i\theta}+O(w^2)$ and the normalized transverse phase approaches $\theta$ with error $O(w)$. Solving the phase equation yields

$$
nw_k\longrightarrow U_{d,k}=\frac{\pi k+\nu\theta}{d\sin\theta}.
$$

At each fixed quota $m$, under the uncapped model a specified row has binomial load with parameters $d,m/n$. The union bound over rows excludes at most $O(n^{-r})$ of the arrays. Hence $a_m/\binom nm^d\to1$. The terms at $-w_k^d$ are bounded by $((nw_k)^m/m!)^d$, which has a summable majorant since $nw_k$ is bounded. Dominated convergence gives

$$
(-1)^k P(-w_k^d)\longrightarrow
(-1)^k\sum_{m\ge0}\frac{(-1)^m U_{d,k}^{dm}}{(m!)^d}.
$$

A positive limit would prove the required lower sign at that $(d,k)$. This formula alone leaves the sign open.
