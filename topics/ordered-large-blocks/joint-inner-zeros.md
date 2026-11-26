# The first real zeros when the threshold and the degree both grow

Let $`O_{n,j}(t)`$ enumerate ordered set partitions by the number of blocks of size at least $`j`$, with degree $`\lfloor n/j\rfloor`$. Let $`q_{n,j,k}`$ be the $`k`$th positive real zero of $`q\mapsto O_{n,j}(-q)`$, whenever it exists. The [sharp lower-edge theorem](lower-spectral-edge.md) gives a parameter $`q_j^*>0`$ below which every row is positive, including at $`q_j^*`$. Its generating-function denominator has a double zero at $`\rho_j>0`$ at that parameter.

**Theorem.** There are constants $`J,M,c,\eta>0`$ such that whenever $`j\ge J`$ and $`m=n/j\ge M`$, each row has at least $`cm`$ simple negative real zeros with moduli in

$$
q_j^{\ast}<q<q_j^{\ast}+(1+q_j^{\ast})\eta^2.
$$

Every zero of the row whose complex modulus is at most $`q_j^*+4(1+q_j^*)\eta^2`$ is simple and negative. The zeros in the smaller interval therefore include a positive fraction of the smallest-modulus complex zeros. At each such zero of rank $`k`$,

$$
q_{n+1,j,k}<q_{n,j,k}<q_{n+1,j,k+1}.
$$

For every fixed $`k\ge1`$, as $`j\to\infty`$ and $`n/j\to\infty`$ with arbitrary relative growth,

$$
\frac{(n/j)^2}{1+q_j^{\ast}}(q_{n,j,k}-q_j^{\ast})\longrightarrow\frac{\pi^2 k^2}{2}.
$$

In particular, for every fixed $`K`$ the first $`K`$ complex roots by modulus, or all available ranks if the degree is smaller, are simple negative and have the stated consecutive order outside a finite set of pairs $`(j,n)`$. The upper comparison is omitted at the last available rank if the next row has the same degree. The existing [fixed-threshold theorem](all-fixed-thresholds.md) applies for each bounded $`j`$ as $`n`$ grows. For large $`j`$ and bounded $`n/j`$ use the [proportional-range theorem](proportional-window.md), with a bound slightly larger than $`M`$ to include both rows. For the remaining pairs use the joint theorem with $`M`$ large enough to include the first $`K`$ ranks. This argument yields a finite exception set without specifying its size.

## Rescaling the double pole

Write $`T_j(z)=\sum_{a\ge j}z^a/a!`$, $`b_j(z)=j!z^{-j}T_j(z)`$ including the removable value at zero, and $`B(z)=2-e^z`$. The coefficient formula is

$$
f_{n,j}(q):=\frac{O_{n,j}(-q)}{n!}=[z^n]\frac{1}{B(z)+(1+q)T_j(z)}.
$$

Put $`\lambda=\log 2`$, $`\rho=\rho_j`$, $`Q=1+q_j^*`$, and $`q=q_j^*+Qt^2`$. The double-zero equations give $`QT_j(\rho)=e^\rho-2`$ and $`QT_j'(\rho)=e^\rho`$. Subtracting gives $`Q\rho^{j-1}/(j-1)!=2`$. Hence $`e^{\rho-\lambda}=1+T_j(\rho)/[\rho^{j-1}/(j-1)!]=1+\rho/j+O(j^{-2})`$, so $`\rho=\lambda(1+j^{-1})+O(j^{-2})`$ and $`j(e^\rho-2)/(2\rho)\to1`$. Rescale $`z=\rho e^{u/j}`$ and denote the denominator by $`D_j(z,t)`$. On compact sets of complex $`u,t`$,

$$
\mathcal D_j(u,t):=\frac{j}{2\rho}D_j(\rho e^{u/j},t)
\longrightarrow (1+t^2)e^u-1-u .
$$

Indeed the coefficient bound $`j!/(j+a)!\le(j+1)^{-a}`$ gives $`b_j=1+O(1/j)`$ and $`b_j'=O(1/j)`$ on any fixed disk of radius less than two. On the scaled compact sets, $`T_j(\rho e^{u/j})/T_j(\rho)=e^u(1+O(j^{-2}))`$. Taylor expansion of $`e^{\rho e^{u/j}}`$ and the critical equation give the claimed limit. All derivatives converge locally uniformly by holomorphy.

At $`t=0`$ the double zero of $`\mathcal D_j`$ is exactly $`u=0`$. Solve $`\mathcal D_j(u,t)=0`$ for $`t^2=P_j(u)`$ near zero. The functions $`-P_j(u)/u^2`$ extend analytically across zero and converge locally uniformly to a function with value $`1/2`$ at zero. On a fixed small disk, their positive-at-zero square roots give $`v_j(u)=u\sqrt{-P_j(u)/u^2}`$ with derivative uniformly close to $`1/\sqrt2`$. These functions are injective there, since the integral of their derivative on the segment between any two points differs from $`(u_1-u_2)/\sqrt2`$ by a smaller term. Their images contain a common disk about zero by Rouché's theorem on the boundary. Inverting $`v_j(u)=it`$ gives the upper branch $`u_j(t)=i\kappa_j t+O(t^2)`$, where $`\kappa_j\to\sqrt2`$. All branches and expansions hold on a fixed complex $`t`$ disk with uniform constants. Conjugation gives $`u_j(-t)=\overline{u_j(t)}`$ for real $`t`$.

Set

$$
a_j(t)=\frac{u_j(t)+u_j(-t)}2,\qquad b_j^{\ast}(t)=\frac{u_j(t)-u_j(-t)}{2i},\qquad
r_j(t)=\rho e^{a_j(t)/j},\qquad \varphi_j(t)=b_j^{\ast}(t)/j.
$$

The two poles are $`z_\pm(t)=r_j(t)e^{\pm i\varphi_j(t)}`$. Here $`a_j(t)=O(t^2)`$ is even, $`b_j^*(t)=\kappa_j t+O(t^3)`$ is odd, and for small real $`t>0`$ the angle satisfies $`\varphi_j(t)\asymp t/j`$. The notation $`\asymp`$ denotes upper and lower bounds by fixed positive multiples.

## A contour uniform in the threshold

There is a fixed $`d>0`$ such that $`e^u-1-u`$ has no zero with $`\Re u\le2d`$ except the double zero at zero. Indeed a root satisfies $`e^x\sin y=y`$ for $`u=x+iy`$. If $`x\le0`$ and $`y\ne0`$, the strict inequality $`|\sin y|<|y|`$ is a contradiction. On the real line $`e^x>1+x`$ for $`x\ne0`$. For $`x\le1`$, the same equation bounds $`|y|\le e`$ at a root and its real part bounds $`x\ge-1-e`$. Discreteness now gives $`d`$.

Use $`R_j=\rho e^{d/j}`$. For all sufficiently large $`j`$ and all $`t`$ in a fixed small complex disk, there are just the two small continuations inside this circle, counted with multiplicity. To check this globally, the term $`(1+t^2)QT_j(z)`$ is $`O(1/j)`$ throughout $`|z|\le R_j`$, by the coefficient bound on $`b_j`$, the ratio $`(R_j/\rho)^j=e^d`$, and the critical equation. Also $`|B(z)|\ge c_0|z-\lambda|`$ on a fixed disk containing these circles, since the other zeros of $`B`$ are $`\lambda+2\pi i k`$ for nonzero integers $`k`$. Hence every zero inside the circle lies $`O(1/j)`$ from $`\lambda`$, and so has $`|u|=|j\log(z/\rho)|`$ bounded and $`\Re u\le d`$. Outside a small disk at $`u=0`$, the limiting denominator $`e^u-1-u`$ has a positive minimum on this compact set. By shrinking the $`t`$ disk and increasing $`J`$, uniform convergence excludes every zero there. Rouché's theorem in the small disk counts the two local branches from the preceding section. Shrink the $`t`$ disk again so that $`|u_j(\pm t)|<d/2`$, which gives $`|r_j(t)|/R_j\le e^{-d/(2j)}`$.

Write $`z=R_j e^{i\theta}`$, $`-\pi\le\theta\le\pi`$, and $`\Delta_j(\theta)=j^{-1}+|\theta|`$. Uniformly on the circle one has

$$
|B(z)|,\ |D_j(z,t)|\ \ge c_1\Delta_j(\theta),\qquad
|\partial_\theta B(z)|,\ |\partial_\theta D_j(z,t)|\ \le c_2.
$$

For $`B`$, use $`|z-\lambda|^2=(R_j-\lambda)^2+2R_j\lambda(1-\cos\theta)`$ with $`R_j-\lambda\ge \lambda d/j`$. The bound on the long-block term then gives the same lower bound for $`D_j`$ when $`|\theta|\ge A/j`$ with a fixed sufficiently large $`A`$. When $`|\theta|\le A/j`$, use $`u=d+ij\theta`$ and the uniform lower bound for $`\mathcal D_j`$ on this compact vertical segment. The derivative estimates follow from the form $`T_j(z)=z^jb_j(z)/j!`$, the coefficient bounds on $`b_j,b_j'`$, and $`QT_j(R_j)=O(1/j)`$.

Let $`J_{n,j}(t)`$ be the coefficient contour integral on $`|z|=R_j`$ after enlarging from the origin. It is analytic and even in $`t`$. In the angular integral, integration by parts at frequency $`n`$ gives

$$
|J_{n,j}(t)|\le C R_j^{-n}\frac{1}{n}\int_{-\pi}^{\pi}\Delta_j(\theta)^{-2}\thinspace d\theta
\le C R_j^{-n}\frac{j}{n}.
$$

Periodicity removes the boundary term. The important stronger consecutive-row estimate is

$$
|r_j(t)J_{n+1,j}(t)-J_{n,j}(t)|\le C\frac{R_j^{-n}}{n-j}\qquad(n>j).
$$

The difference inserts $`s(z)=r_j(t)/z-1`$ in the angular integrand. On the circle $`|s|=O(\Delta_j)`$ and $`|\partial_\theta s|=O(1)`$. Write $`C_j(z,t)=(1+t^2)QT_j(z)`$ and decompose

$$
\frac{s}{D_j}=\frac{s}{B}-\frac{sC_j}{B D_j}.
$$

For the first term move the contour to a fixed radius $`R_0>1`$ smaller than $`|\lambda+2\pi i|`$. No zero of $`B`$ lies between the circles, so this term is $`O(R_0^{-n})`$. For the second term factor $`C_j=e^{ij\theta} c_j(\theta,t)`$, with $`|c_j|=O(1/j)`$ and $`|\partial_\theta c_j|=O(1/j^2)`$ by the derivative bound for $`b_j`$. The angular derivative of $`s c_j/(B D_j)`$ has absolute value at most

$$
C\left(\frac{1}{j\Delta_j^2}+\frac{1}{j^2\Delta_j}\right),
$$

whose integral is bounded uniformly. Integration by parts at frequency $`n-j`$ gives $`O(R_j^{-n}/(n-j))`$. The fixed-radius term is absorbed in this bound since $`R_j/R_0`$ is bounded away from one.

## Residues and strict order

On a fixed smaller $`t`$ disk there is a uniform analytic representation

$$
\partial_zD_j(z_+(t),t)=it\thinspace  d_j(t),qquad d_j(0)>0,
$$

with $`d_j,d_j^{-1}`$ uniformly bounded. In fact $`\partial_zD_j=(2\rho/z)\partial_u\mathcal D_j`$ and its first nonzero term at the pole is $`2i\kappa_j t`$ in the limit as $`j\to\infty`$. Define $`A_j(t)`$ and $`B_j(t)`$ from the even and odd parts of the analytic logarithm of $`d_j`$:

$$
A_j(t)=\exp\left(\frac{\log d_j(t)+\log d_j(-t)}2\right),\qquad
B_j(t)=\frac{\log d_j(t)-\log d_j(-t)}{2i}.
$$

For real $`t`$, $`A_j>0`$, $`B_j`$ is real, and $`B_j(t)=O(t)`$ with uniformly bounded derivative. Subtracting the two pole residues in the contour enlargement gives

$$
\begin{aligned}
C_{n,j}(t)&:=\frac{t A_j(t)r_j(t)^{n+1}}{2}\thinspace f_{n,j}(q_j^{\ast}+Qt^2) \\
&=\sin U_{n,j}(t)+E_{n,j}(t),\qquad
U_{n,j}(t)=\frac{n+1}{j} b_j^{\ast}(t)+B_j(t),\\
E_{n,j}(t)&=\frac{t A_j(t)r_j(t)^{n+1}}2 J_{n,j}(t).
\end{aligned}
$$

These identities extend across zero by analyticity. The contour bounds give, with $`m=n/j`$,

$$
|E_{n,j}(t)|\le C|t|e^{-dm/2}/m,
\qquad
|E_{n+1,j}(t)-E_{n,j}(t)|\le C|t|e^{-dm/2}/(n-j).
$$

On a smaller disk $`|\partial_t E_{n,j}|=O(e^{-dm/2}/m)`$ by Cauchy's inequality.

Choose a small $`\eta>0`$ with $`[0,2\eta]`$ inside that disk. Uniformly there for all large $`j,m`$, $`U_{n,j}`$ is increasing, starts at zero, and has derivative bounded above and below by positive multiples of $`m`$, since $`(b_j^*)'(t)`$ stays uniformly close to $`\sqrt2`$. Full phase bands of width $`\pi/6`$ on either side of $`k\pi`$ each contain one simple real zero, from opposite signs at the endpoints and a monotone normalized function inside. The gaps contain none. The initial half-band has only its zero at the origin from the normalizer. Positivity for $`q\le q_j^*`$ identifies the ranks of the real zeros starting at $`k=1`$. Counting full bands in $`0<t<\eta`$ gives at least $`cm`$ for an absolute $`c>0`$.

At an old positive $`t`$ zero, use $`\Phi=\pi/2+U_{n,j}`$ and $`\varphi=\varphi_j(t)`$. Then the next normalized value, after subtracting the old normalized value zero, is

$$
\sin\Phi\sin\varphi+\cos\Phi(1-\cos\varphi)+(E_{n+1,j}-E_{n,j}).
$$

In the $`k`$th band $`\sin\Phi`$ has sign $`(-1)^k`$ and absolute value at least $`\sqrt3/2`$. Since $`\varphi\asymp t/j`$, the error difference divided by $`\sin\varphi`$ is $`O(e^{-dm/2}/(m-1))`$, uniformly even when $`j`$ grows arbitrarily faster than $`m`$. The cosine term costs at most $`1-\cos\varphi=O(\varphi^2)`$. Thus the sign is $`(-1)^k`$ for all sufficiently large $`j,m`$. The next phase differs by $`\varphi`$, so it lies within $`\pi/3`$ of the same $`k\pi`$ at the old zero. The band signs and uniqueness place that point just after the next $`k`$th crossing and before the next $`(k+1)`$st crossing. The larger interval $`0<t<2\eta`$ supplies the comparison for the final old root below $`\eta`$.

## Excluding other complex zeros of smaller modulus

Use the complex parameter $`\tau=(1+q)/Q`$. The rescaled denominator converges on compact sets of $`u,\tau`$ to $`\tau e^u-1-u`$. First fix $`|\tau_0|\le1`$, $`\tau_0\ne1`$. The limit pole equation in $`w=1+u`$ is $`we^{-w}=\tau_0/e`$. On $`|w|=1`$ the left side has modulus $`e^{-\Re w}\ge1/e`$, with equality only at $`w=1`$. Under the homotopy replacing $`\tau_0`$ by $`s\tau_0`$, $`0\le s\le1`$, no zero crosses this circle. There is therefore a unique root inside it, and it is simple since the only critical point of $`we^{-w}`$ is $`w=1`$. If $`\tau_0\ne0`$, all other roots have strictly larger real part by

$$
\Re w=1+\log |w|-\log|\tau_0|.
$$

If $`\tau_0=0`$, the only root is $`w=0`$.

Choose a real $`d_0`$ strictly between the real part of this principal $`u`$ root and all the others, with a positive margin at the principal root. On a small neighborhood of $`\tau_0`$ the contour $`|z|=\rho e^{d_0/j}`$ has exactly one pole inside it, and this pole satisfies $`|z_\star|\le\rho e^{(d_0-\epsilon)/j}`$ for some $`\epsilon>0`$. Here are the details of the transfer. Every candidate pole in the disk has $`|z-\lambda|=O(1/j)`$, by the same long-block bound as before. Thus the $`u`$ variable lies in a fixed compact set with $`\Re u\le d_0`$. The limiting denominator at $`\tau_0`$ is nonzero there outside a small disk around the principal root. Uniformity on this compact set and Rouché's theorem on the small disk yield the claim after shrinking the neighborhood. The proof of the contour estimate $`|J_{n,j}|=O(R_j^{-n}/m)`$ also applies here with $`R_j=\rho e^{d_0/j}`$. For $`|\theta|\ge A/j`$ use $`|2-e^z|\ge c|\theta|`$ and the long-block bound. For $`|\theta|\le A/j`$ use the lower bound on the scaled compact vertical segment $`\Re u=d_0`$. In both regions these give $`|D_j|\gtrsim j^{-1}+|\theta|`$ and the same uniform angular derivative bound. The derivative at the single pole is nonzero and bounded above, by the scaled simple-root equation and its convergent derivatives. The contour term is exponentially smaller in $`m`$ than the single residue $`-1/(z_\star^{n+1}D'_j(z_\star))`$. Thus there are no row zeros in this neighborhood of $`\tau_0`$ once $`j`$ and $`m`$ are large enough.

It remains to treat a fixed small neighborhood of $`\tau=1`$. Choose a radius $`T>0`$ whose closed complex $`t`$ disk lies inside the analytic region used for the sine estimate. Shrink $`T`$ so that $`\Re (b_j^*)'(t)`$ is bounded below by a fixed positive constant throughout. For all sufficiently large $`j,m`$, $`\Re U'_{n,j}(t)\ge c m`$ throughout this disk. In particular $`U=U_{n,j}`$ is univalent there, and integration along straight segments gives

$$
|U(t_1)-U(t_2)|\ge c m|t_1-t_2|.
$$

Suppose $`|t|\le T/2`$ is a zero of the normalized row. Then $`|\sin U(t)|`$ is at most the uniform error, which tends to zero. Since $`|\sin(x+iy)|^2=\sin^2 x+\sinh^2 y`$, the value $`U(t)`$ is within $`o(1)`$ of a point $`k\pi`$ for some integer $`k`$. The entire disk $`|w-k\pi|\le1/4`$ belongs to the image of the larger open $`t`$ disk for large $`m`$. Indeed $`|U(\zeta)-U(t)|\ge c m T/2`$ for $`|\zeta|=T`$, so Rouché's theorem applied to $`U(\zeta)-w`$ transfers the single solution at $`w=U(t)`$ to every such $`w`$. On that image disk the normalized equation is $`\sin w+E_{n,j}(U^{-1}(w))=0`$. The second term is uniformly small and the sine has a fixed positive minimum in modulus on the boundary because it is periodic up to sign. There is exactly one zero, which is real by conjugation and simple by the count. Consequently $`t`$ is real, since the inverse branch commutes with conjugation. The zero with $`k=0`$ is the forced zero $`t=0`$ of the normalizer, while a real nonzero $`t`$ gives a simple real row zero at $`q=q_j^*+Qt^2>q_j^*`$.

Apply the one-pole argument on a finite cover of $`\{|\tau|\le1,\ |\tau-1|\ge T^2/8\}`$. This yields a fixed neighborhood of the compact set on which there are no zeros. Hence some $`\delta>0`$ suffices to cover all $`|\tau|\le1+\delta`$ with $`|\tau-1|\ge T^2/4`$, by projecting radially to the closed unit disk and taking $`\delta`$ small enough. The remaining points satisfy $`|t|=|\tau-1|^{1/2}<T/2`$ and are covered by the sine argument. Shrink $`\eta`$ so that $`4\eta^2\le\delta`$. Every $`|q|\le q_j^*+4Q\eta^2`$ then satisfies $`|\tau|\le1+4\eta^2`$, so every row zero of such modulus is simple and real in the $`q`$ variable. It is positive there, hence negative for $`O_{n,j}`$. This also identifies the initial real orders already proved with complex-modulus orders, including the comparisons in the window $`0<t<2\eta`$.

## Microscopic limit and prior scope

With $`x=y^2`$ and $`t=y/m`$, uniformly on each compact complex $`y`$ disk we have $`U_{n,j}(y/m)\to\sqrt2 y`$ and $`r_j(y/m)^{n+1}/\rho^{n+1}\to1`$. The latter uses evenness and $`a_j(t)=O(t^2)`$. The analytic expression $`\sin U_{n,j}(t)/t`$ extends at zero, where its value is $`(n+1)\kappa_j/j+B_j'(0)\sim\sqrt2 m`$. The remainder divided by $`t`$ tends to zero uniformly, so the normalized limit becomes

$$
\frac{O_{n,j}(-q_j^{\ast}-Qx/m^2)}{O_{n,j}(-q_j^{\ast})}
\longrightarrow \frac{\sin\sqrt{2x}}{\sqrt{2x}}.
$$

Both sides are even in $`y`$, which gives local uniform convergence in $`x`$. The limit has simple positive zeros $`\pi^2k^2/2`$. Rouché's theorem on small disjoint disks around the first fixed number and uniform convergence on the intervening real compact segments give the stated limits for the first real zeros.

The original statement requires real-rootedness and consecutive interlacing throughout every row. The simultaneous-growth result here controls a positive fraction of the smallest-modulus ranks. Targeted searches and the public investigation located coefficient and Newton-inequality checks for the full-parameter problem, and the earlier project notes supply the fixed-threshold and bounded-$`n/j`$ regimes. The cited public material gives no simultaneous-growth result for these initial ranks. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Public investigation](https://github.com/1337isnot1337/solved-conjectures/issues/108)
