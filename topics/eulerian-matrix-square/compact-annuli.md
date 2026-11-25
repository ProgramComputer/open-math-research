# Simple negative zeros and interlacing in every fixed annulus

Let $A$ be the shifted Eulerian matrix in Mao and Wang's conjecture, and let $xH_n(x)$ be row $n$ of its ordinary square. Fix $0<R_0<R_1<\infty$. For all sufficiently large $n$, **every complex zero of $H_n$ with $R_0\le |x|\le R_1$ is simple and negative**. Between consecutive zeros of row $n$ in this annulus there is exactly one zero of row $n+1$, and the same holds with the two rows interchanged. In particular any sequence of nonreal or multiple zeros at unbounded row indices eventually leaves each fixed annulus. The cutoffs may depend on both radii. [Conjecture](https://arxiv.org/abs/2607.01572) · [Uniform factorial saddle estimate used below](bulk-asymptotics.md)

## Pole selection off the negative axis

Use the factorial-weighted polynomial $F_n(w)=\sum_{k=1}^n A(n,k)k!w^k$ and $N=n+1$, $L=\log N$. On any compact subset of the slit plane $\mathbb C\setminus(-\infty,0]$, the pole expansion of the Eulerian polynomial has a single largest factor $w(x)=(x-1)/\operatorname{Log}x$, extended by $w(1)=1$. All other factors $(x-1)/(\operatorname{Log}x+2\pi i m)$ have moduli at most $\delta |w(x)|$ for a fixed $\delta<1$. Their squared ratios have uniformly bounded sum. At $x=1$ the nonleading factors vanish. Consequently
$$
 xH_n(x)=w(x) F_n(w(x))+O\big(|w(x)|F_n(\delta |w(x)|)\big).
$$
Indeed each exponent $k+1$ is at least two, permitting extraction of $\delta^{k-1}$ from the pole sum in the error. The logarithmic mean $w(x)=\int_0^1 e^{v\operatorname{Log}x}\,dv$ is nonzero and lies in the sector between $1$ and $x$. On the compact set its values stay in a closed annular sector avoiding the negative real axis. The uniform factorial saddle estimate therefore gives $F_n(\delta |w|)/|F_n(w)|\le\delta^N\exp(O(N/L))$. All sufficiently large rows have no zero on this compact set. [Eulerian pole expansion and saddle estimate](bulk-asymptotics.md#eulerian-poles-and-a-factorial-weighted-row)

## An analytic phase across the cut

Write $x=-e^z$ and enlarge $[\log R_0,\log R_1]$ by a fixed positive margin at both ends. On a sufficiently thin complex strip about that enlarged real segment put
$$
 w_-(z)=-\frac{1+e^z}{z-i\pi},\qquad w_+(z)=-\frac{1+e^z}{z+i\pi},\qquad T_\pm(z)=w_\pm(z)F_n(w_\pm(z)).
$$
The two factors are conjugate on the real segment, with $\Im w_-<0$. The remaining pole factors have moduli at most $\delta\max(|w_+|,|w_-|)$ uniformly on the strip for some $\delta<1$, and the squared ratios are uniformly summable. Both $w_\pm$ remain in a fixed annular sector avoiding the cut. Applying the preceding bound using the factor of larger modulus gives
$$
 xH_n(x)=T_-+T_++O\big(e^{-cN}(|T_-|+|T_+|)\big)
$$
with $c>0$. The approximation is between analytic functions and the bound is uniform.

Take analytic logarithms $\ell_{n,\pm}=\log T_\pm$ that are conjugate on the real segment, using the explicit saddle expression. Put
$$
 \Psi_n=\frac{\ell_{n,-}-\ell_{n,+}}{2i},\qquad
 \theta=\frac{\operatorname{Log}w_--\operatorname{Log}w_+}{2i}.
$$
For real $z$, $\theta(z)=-\pi/2-\arctan(z/\pi)$. With an irrelevant common real constant omitted, the logarithm for $T=w F_n(w)$ is
$$
 (N+1)\operatorname{Log}w+N\Phi_{N,w}(u_{N,w})
 -\tfrac12\operatorname{Log}(-\Phi_{N,w}''(u_{N,w}))+o(1).
$$
Here $\Phi_{N,w}$ and its saddle $u_{N,w}$ are the functions in the factorial estimate. The simple saddle depends holomorphically on $w$ by its critical-point equation and uniqueness near $1$. The final $o(1)$ is the analytic logarithm near zero of the relative factor tending uniformly to $1$. Since $\Phi_{N,w}(u_{N,w})=-1-\log L+O(1/L)$ and $-\Phi''=1+O(1/L)$, the common real term cancels, giving $\Psi_n=(N+1)\theta+O(N/L)$ uniformly on the complex strip. Cauchy's derivative estimate gives the corresponding estimate for $\Psi_n'$ on a slightly smaller rectangle. Thinning it further, $\Re\theta'$ is bounded above by a strictly negative constant. Thus throughout this rectangle
$$
 \Re\Psi_n'\le -c_0 N,\qquad |\Psi_n'|\le C_0 N
$$
for fixed $c_0,C_0>0$. Integration along any segment in the rectangle gives $|\Psi_n(z_2)-\Psi_n(z_1)|\ge c_0N|z_2-z_1|$ and in particular injectivity. Integration on a vertical segment from the real axis gives $|\Im\Psi_n(z)|\ge c_0N |\Im z|$.

## Counting all zeros there

Divide the two-pole formula by the nonvanishing analytic factor $\exp((\ell_{n,-}+\ell_{n,+})/2)$. The resulting function is
$$
 2\cos\Psi_n(z)+E_n(z),\qquad
 |E_n(z)|\le C e^{-cN+|\Im\Psi_n(z)|}.
$$
At any zero, $|\cos(a+ib)|^2=\cos^2a+\sinh^2b$ first gives $|\Im\Psi_n|=O(e^{-cN})$ and then distance $O(e^{-cN})$ from a real level $(j+1/2)\pi$. Hence $|\Im z|=O(e^{-cN}/N)$. Since $|\Psi'_n|\le C_0N$, the value of $\Psi_n$ at $\Re z$ is also within $O(e^{-cN})$ of that level. Strict monotonicity on the enlarged real interval supplies its unique real preimage $z_j$, with $|z-z_j|=O(e^{-cN}/N)$.

Around each such $z_j$ in the interior, take a disk of radius $1/(4C_0N)$. On its boundary the phase distance to the level is between $c_0/(4C_0)$ and $1/4$. Thus $|\cos\Psi_n|$ has a positive uniform lower bound there. The cosine has one simple zero in the disk by injectivity and the derivative bound. Rouché's theorem gives exactly one zero counted with multiplicity of the row polynomial there. Complex conjugation fixes the disk, and the row has real coefficients, so that zero is real in $z$ and corresponds to a simple negative $x$. Conversely the preceding localization includes every possible zero over the original radial interval in such a disk. The compact part of the annulus outside the strip was already excluded by the one-pole formula.

## Consecutive rows

Uniformly on the real interval,
$$
 \Psi_{n+1}-\Psi_n=\theta+o(1).
$$
To verify this precision, allow $N$ to vary continuously in its saddle formula. The critical-point equation eliminates the derivative of $u_{N,w}$ from the derivative of the critical value. At $u=u_{N,w}$ one has
$$
 \frac{d}{dN}\big[N\Phi_{N,w}(u_{N,w})\big]
 =\Phi_{N,w}(u)+\frac1{Nwu-1}-\frac1{\log(Nwu)}
 =-1-\log\log N+O(1/\log N).
$$
Logarithms here use the same local branches as in the saddle proof. Integrating for one unit of $N$ shows that the imaginary change is $O(1/\log N)$. The Gaussian logarithm and the logarithmic approximation errors tend uniformly to zero. This proves the phase-increment formula.

The real function $\theta$ stays a positive distance from both $-\pi$ and $0$ on the enlarged interval. At a zero of row $n$, its real phase deviates by $O(e^{-cN})$ from the corresponding half-integer level. For two consecutive roots in the interval these levels are consecutive, since every intervening level has a zero in its disk. Thus the phases of row $n+1$ at these endpoints straddle precisely one half-integer level, a fixed positive phase distance from either endpoint. Its unique zero lies strictly between them by the derivative and localization bounds. The same argument applied in the opposite direction gives the two-sided local alternation.

The unresolved regimes allow $|x|$ to tend to zero or infinity with $n$. The [extreme-zero formulas](endpoint-asymptotics.md) cover each fixed rank within those regimes. They do not yet control all intervening ranks.
