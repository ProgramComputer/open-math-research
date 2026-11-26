# Strict consecutive order in the bounded-radius part of the dense regime

Consider $`n=mj+s`$, $`0\le s<j`$, with $`j,m\to\infty`$ and $`h=o(m)`$. This note treats $`h/j\to\infty`$ and $`hj/m`$ bounded above. It proves simplicity, negativity and the consecutive interlacing comparisons for the root with one-based rank $`k=m-h`$ in *increasing* original modulus, including the degree-increasing step. The parameters imply $`m/j^2\to\infty`$. The conclusion is $`b_k<a_k<b_{k+1}`$ for old and new moduli $`a_k,b_k`$. We allow fixed shifts of $`h`$ throughout. [Independent review](review-dense.md)

## The positive real radius for a complex modulus

Use the renewal notation $`S_j(\rho)=1`$, $`T=(1-S_j(\rho z))^{-1}`$, $`U=\sum_{i\ge0}j!(\rho z)^i/(i+j)!`$, $`V=TU`$. For a complex variable $`q`$ we have

$$
f_n(q)=\rho^n O_{n,j}(-q)/n!
=[z^n]\thinspace \frac{T(z)}{1+Qz^j V(z)},\qquad Q=q\rho^j/j!.
$$

Define $`r`$ by $`|Q|r^j V(r)=1`$. It decreases from one to zero as $`|Q|`$ increases. We work at $`r\le r_*<1`$ for fixed $`r_*`$, with $`m r/j^2\to\infty`$ uniformly over any parameter intervals under consideration. Write $`\mathcal M(z)=zV'(z)/V(z)`$ and $`\mathcal W(z)=z\mathcal M'(z)`$. At a positive real $`r`$, these are the mean and variance of the $`r`$-tilted coefficients of $`V`$. On this compact radius range both are comparable to $`r`$, uniformly in $`j`$. Indeed $`V`$ has nonnegative coefficients bounded above and below on the entire sequence, and tilted probabilities of zero and one are at least $`c`$ and $`cr`$. All positive-order logarithmic derivatives $`(z\partial_z)^a\log V`$ on a slightly larger closed disk are $`O_a(|z|)`$ for each fixed $`a`$. The same bound holds for $`T`$. These facts follow from uniform analytic logarithms on the larger disk, using the zero-free renewal representation. Constants may depend on $`r_*`$.

## The pole circle and its residues

Choose a constant $`D>2`$ large enough that on $`|z|=R=r e^{D/j}`$, $`|Qz^j V(z)|\ge2`$. The same $`D`$ works throughout $`r\le r_*`$ since $`|V|`$ is bounded above and below on the slightly larger disk. Rouché gives $`j`$ zeros of the denominator inside $`R`$. The Cauchy integral on this circle is $`O(R^{-n})`$. To describe all the zeros, put $`z=r\exp(x/j+i\theta)`$. The real modulus equation is

$$
x+\log|V(r e^{x/j+i\theta})|-\log V(r)=0 .
$$

For every $`\theta`$ there is a unique solution $`x=x(\theta)`$ in $`|x|\le C r`$. Indeed the left side has derivative $`1+\Re\mathcal M(z)/j=1+O(r/j)`$ and opposite signs at $`\pm C r`$ by the logarithm bounds. All functions of $`\theta`$ here are periodic, except the unwrapped phase. The solution is even, $`x(0)=0`$, and the phase $`b(\theta)=j\theta+\Im\log V(z)`$ is odd with derivative $`j+O(r)>0`$. Over a full circle its increment is $`2\pi j`$. Selecting $`b=(2v+1)\pi-\arg q`$ gives exactly the $`j`$ simple poles, taking representatives modulo $`2\pi j`$. Equivalently their logarithmic denominator derivatives are $`-(j+\mathcal M(z))`$, which never vanish. Each has residue contribution $`K(z)z^{-n}`$ with $`K(z)=T(z)/(j+\mathcal M(z))`$, of modulus comparable to $`1/j`$.

There is a fixed small $`\delta_0>0`$ such that for $`0\le\theta\le\delta_0`$,

$$
x'(\theta)=\frac{\Im\mathcal M(z)}{1+\Re\mathcal M(z)/j}\asymp r\theta.
$$

Indeed at radius $`|z|`$ the imaginary part is $`\mathcal W(|z|)\theta+O(r\theta^2)`$ and $`\mathcal W(|z|)\ge cr`$. This gives, for $`0\le |b_1|\le |b_2|`$ on that arc,

$$
x_{b_2}-x_{b_1}\asymp\frac r{j^2}(b_2^2-b_1^2).
$$

For $`\delta_0\le|\theta|\le\pi`$ one has $`x\ge c_{\delta_0}r`$. To see this, compare the tilted characteristic function at $`t=|z|`$: $`1-|V(t e^{i\theta})/V(t)|^2\ge 2p_0p_1(1-\cos\theta)\ge c_{\delta_0}r`$. Also $`|\log V(t)-\log V(r)|\le C r |x|/j`$. Substitution into the modulus equation gives the assertion. The principal poles with bounded $`|b|`$ have $`x=O(r/j^2)`$.

Write $`M=n/j`$ and $`\mu=Mr/j^2`$. On positive real $`q`$ the closest poles are the conjugate pair for $`b=\pm\pi`$. Relative to either principal residue, the sum beyond the pair is $`O(e^{-c\mu})`$. On the small arc, sum $`C\exp(-c\mu(b^2-\pi^2))`$ over the remaining odd targets. Off that arc the bound is $`Cj e^{-cMr}`$. For the consecutive difference at real $`q`$ normalize each row with the common principal radius $`r_0=|z_\pi|`$, thus replacing each remaining residue by its product with $`r_0/z_b-1`$. This factor is $`O(|b|/j)`$ in the small arc, since $`\theta=O(|b|/j)`$ and $`|x_b-x_\pi|\le Cr`$. Elsewhere it is bounded. As $`Mr=\mu j^2`$, the whole normalized difference of nonprincipal residues is $`O(e^{-c'\mu}/j)`$. The circle errors in the individual normalized rows are at most $`Cj\exp(-M(D-x_\pi))`$. They too are $`O(e^{-c'\mu}/j)`$ since $`m/j^2\to\infty`$ and $`x_\pi=O(r/j^2)`$.

## Reality, multiplicities and row comparison

For complex $`q`$ outside $`|\arg q|<\delta/2`$ with fixed small $`\delta>0`$, one closest pole dominates by $`O(e^{-c\delta\mu})`$ relative error. The squared gap between the smallest two absolute targets is $`4\pi|\arg q|`$, and the preceding far-arc and circle bounds still apply. Thus the polynomial does not vanish there.

In $`L=\log q`$ near positive real $`q`$, select analytic conjugate pole branches $`z_\pm`$ with $`z_+`$ upper on the real axis. The implicit derivative $`d\log z_\pm/dL=-1/(j+\mathcal M(z_\pm))`$ continues them throughout fixed small disks around each real $`L`$. For example the map $`j\log(z/z_0)+\log(V(z)/V(z_0))`$ is univalent and covers a fixed parameter disk on a log-radius disk of radius $`C/j`$ about each starting pole, by comparison with its linear first term. Let $`\Phi`$ be the analytic continuation of $`n\arg z_+-\arg K(z_+)`$, using half the difference of conjugate logs. Normalize by the geometric mean of the two principal absolute continuations as in the moving pole proof. The two main terms sum to $`\cos\Phi`$ in this normalization. The analytic error and its first derivative on smaller disks are $`O(e^{-c\mu})`$: throughout a small complex disk all other pole targets have size at least $`3\pi-\delta`$, while the two principal ones have size at most $`\pi+\delta`$, and the horizontal bounded changes of $`L`$ alter $`r`$ by a relative $`O(1/j)`$. Cauchy's derivative estimate applies to the error written as the analytic normalized polynomial minus the cosine.

On the real axis,

$$
\Phi'=n\thinspace \frac{\Im\mathcal M(z_+)}{|j+\mathcal M(z_+)|^2}+O(r/j)\asymp \mu>0 .
$$

Here the principal angle is comparable to $`1/j`$, and $`\Im\mathcal M(z_+)\asymp r/j`$. The derivative error follows from the analytic logarithmic derivative of $`K`$. On the small disks $`|d^2\log z_\pm/dL^2|=O(r/j^3)`$ and $`|d^2\log K/dL^2|=O(r/j^2)`$, so $`|\Phi''|=O(\mu)`$. Choose $`\delta`$ small to retain $`\Re\Phi'\ge c\mu`$. If a complex zero occurs, its phase is within $`O(e^{-c\mu})`$ of a real cosine zero, using the identity for $`|\cos(a+ib)|^2`$. The phase is injective on the padded disk by integration of its derivative on line segments, and its image contains a disk of radius $`1/4`$ about that real cosine zero by the argument principle on the boundary. In this image disk Rouché gives just one simple preimage zero of the perturbed cosine, real by conjugation. Hence all polynomial zeros in these modulus windows are real and simple. Each full band of width $`\pi/6`$ on either side of a half-integer cosine level has one real root and the intervening gaps have none, by the real derivative estimate and signs.

The adjacent row phase is $`\Phi+\arg z_+`$, with $`\arg z_+\asymp 1/j`$. At an old root, the next normalized value has sign $`-\mathrm{sgn}(\sin\Phi)`$ by subtracting the old value, using the consecutive error $`O(e^{-c\mu}/j)`$. This agrees with the sign of the derivative of the next row in that band. Consequently its root in the same band comes strictly before the old one as $`q`$ increases, and the root in the next band lies strictly after it.

## Joining to genuine ranks

Start at the compact scaled-modulus root theorem and continue with the moving pole argument up to $`u\le\epsilon j`$ for fixed sufficiently small $`\epsilon>0`$. Under $`m/j^2\to\infty`$ its required infimum of $`M/u^2`$ tends to infinity along this entire continuation. In a fixed interval of radii near $`r=e^{-\epsilon/2}`$ the two constructions coexist. Indeed $`q=(j!/\rho^j)r^{-j}/V(r)`$, whereas the moving pole scale uses $`\log((1+q)j V_j(1))=u+\log u`$, with $`V_j(1)`$ comparable to $`(\log2)^j/j!`$. Thus $`u/j=-\log r+o(1)`$ there. The positive rescalings of the spatial coordinate take poles of one denominator to the very same physical poles of the original ordered-block generating function. Both continuations select its nearest conjugate pair. The physical Cauchy residue divided by the pole itself fixes the phase, up to a positive real normalization and the choice of conjugate branch. Choosing the upper physical pole in the present formula corresponds to conjugation of the positive-$`\Im w`$ branch in the moving formula. Their real phases therefore agree modulo $`2\pi`$, with an integer shift independent of the row size on this overlap. One can choose the residue arguments near zero in both formulas, since both residue factors have positive real part there for large $`j`$. The angle terms are both $`n`$ times the physical upper-pole angle. This identifies the bands of the two adjacent rows *exactly*. The compact start fixes their absolute ranks and the continuing bands preserve them. Angular exclusion here covers an annulus in $`|q|`$ itself; the earlier exclusion in $`|1+q|`$ covers all smaller $`|q|`$ up to the overlap by $`|1+q|\le1+|q|`$. All counted moduli are genuine complex-root ranks.

The two descriptions have an interval of overlap containing many consecutive full bands: $`d\log q/d\log r=-(j+\mathcal M(r))`$, while the real phase derivative in $`\log q`$ is comparable to $`m/j^2`$ there. Thus a fixed open interval of matching radii has phase length comparable to $`m/j`$, tending to infinity. The count of all roots up to real $`q`$ in the continued range differs by $`O(1)`$ from $`\Phi/\pi`$ by the compact start and band exhaustion. The constant is bounded uniformly in $`j,m`$ because the argument branches stay bounded.

At the bounded target $`b=\pi`$ let $`v=j\arg z_+`$. From $`v+\Im\log V(z_+)=\pi`$ one gets

$$
\pi-v=\frac{\pi\mathcal M(r)}j+O(r/j^2).
$$

Indeed $`|z_+|/r=1+O(r/j^3)`$, and the imaginary log on the small arc is $`\mathcal M(|z_+|)\arg z_++O(r(\arg z_+)^2)`$. The count $`K`$ consequently satisfies $`m-K=m\mathcal M(r)/j+O(mr/j^2+1)`$. The mean $`\mathcal M`$ is continuous strictly increasing from zero to infinity. Choose two radii by $`\mathcal M(r)=hj/(2m)`$ and $`\mathcal M(r)=2hj/m`$. Both are uniformly below one since $`hj/m`$ stays bounded and the single-variable tilted mean is uniformly comparable to $`r/(1-r)`$. At either radius $`mr/j^2\asymp h/j\to\infty`$. If necessary enlarge the bounded-radius range from the overlap to reach the larger of these endpoints, keeping some fixed $`r_*<1`$ and padding the interval by using target multipliers $`1/3,3`$ instead of $`1/2,2`$. The intervals connect continuously to the overlap while preserving the uniform lower bound on $`\mu`$. The two counts have defects $`h/2+o(h)`$ and $`2h+o(h)`$. Thus the requested rank and its comparator lie strictly inside the established range. This proves the bounded-radius assertion.
