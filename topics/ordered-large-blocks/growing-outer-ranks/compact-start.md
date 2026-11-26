# Starting the modulus count on compact parameter intervals

This argument supplies the starting bands for the [moving pole proof](moving-poles.md). Let $`Q_j=1+q_j^*`$ for the [sharp lower edge](../lower-spectral-edge.md), and let $`m=n/j`$. For each fixed $`T>1`$, the zeros of $`O_{n,j}`$ with modulus at most $`Q_jT-1`$ are simple and negative for large $`j`$ and $`m`$. They lie in consecutive principal-pole phase bands with common old and new rank labels, as described below. In particular their count differs by $`O(1)`$ from the phase at $`T`$ divided by $`\pi`$. The argument extends the tracked [joint inner-edge proof](../joint-inner-zeros.md) from the fold to fixed compact sets of the scaled parameter. [Independent review](review-moving-poles.md)

## The nearest poles of the limit denominator

Write $`\rho=\rho_j`$, $`\lambda=\log 2`$, $`B(z)=2-e^z`$, and $`D_j(z,\tau)=B(z)+\tau Q_j T_j(z)`$, where $`T_j(z)=\sum_{a\ge j}z^a/a!`$ and $`\tau=(1+q)/Q_j`$. The scaling $`z=\rho e^{u/j}`$ gives $`jD_j/(2\rho)\to \tau e^u-1-u`$ locally uniformly in $`u,\tau`$, as proved in the joint inner-edge theorem. The limiting equation in $`w=1+u`$ is

$$
w e^{-w}=\tau/e.
$$

Least real part of $`u`$ determines least modulus after lifting the poles to $`z`$.

For $`\tau\ne0`$, all roots satisfy $`|w|=|\tau|e^{\Re w-1}`$. Hence roots in any left half-plane lie in a compact set. For nonreal $`\tau`$, at least one root exists by continuing the root from $`w=0`$ along $`s\tau`$, $`0\le s\le1`$. The implicit derivative for $`s>0`$ is $`w/(s(1-w))`$. Once $`|w|\ge2`$ it is bounded on every interval away from $`s=0`$. The branch therefore cannot escape to infinity at a finite parameter. The only critical point is $`w=1`$, and approaching it would force $`s\tau\to1`$, which is excluded on the segment. The derivative stays bounded near any proposed terminal parameter, so the branch has a limit there and continues by the implicit function theorem. If two roots had the same real part, their moduli would coincide, so the two roots would be conjugate. This would force $`\tau`$ real. Thus at nonreal $`\tau`$ there is a unique simple root of least real part, with a strict gap to the others.

For real $`\tau<0`$, the unique negative real $`w_0`$ exists since $`we^{-w}`$ is strictly increasing from $`-\infty`$ to zero on that line. Any root of modulus at most $`|w_0|`$ satisfies $`|we^{-w}|\le |w|e^{|w|}\le |w_0|e^{|w_0|}`$ with equality only at $`w_0`$, proving that it alone has least real part. For $`0<\tau<1`$, homotopy on $`|w|=1`$ keeps exactly one root within the circle, since $`|we^{-w}|\ge1/e`$ there. All other roots have larger real part by the modulus identity. At $`\tau=0`$ the only root is zero. At $`\tau=1`$ the unique least root is double and the [fold analysis](../joint-inner-zeros.md#rescaling-the-double-pole) applies.

For real $`\tau>1`$ there are no real roots, since the maximum of $`we^{-w}`$ on the positive real line is $`1/e`$. An upper root $`w=x+iy`$ satisfies $`\sin y>0`$ and $`x=y\cot y`$. The equation is then

$$
f(y):=y\cot y-\log(y/\sin y)=1-\log\tau.
$$

On $`(0,\pi)`$ the function decreases from $`1`$ to $`-\infty`$, because $`f'(y)=-y-(y\cot y-1)^2/y<0`$. This gives exactly one upper root $`w_1`$ with angle parameter $`y_1`$ in that interval. Any other upper root has $`y_2>2\pi`$. If its real part satisfied $`x_2\le x_1\le0`$, then its modulus would be larger, contrary to the modulus identity. If $`x_2\le x_1`$ and $`x_1>0`$, use $`x_1\le1`$ and $`y_1<\pi/2`$ to get $`|w_1|<2\pi<|w_2|`$, again a contradiction. Therefore the principal conjugate pair has strictly least real part. The parameter $`y(\tau)=y_1`$ increases strictly and analytically from zero to $`\pi`$ on $`\tau>1`$.

## Uniform residue estimates on fixed parameter neighborhoods

Around any fixed $`\tau_0`$ away from the fold, choose a real separator $`d_0`$ between the least real part of the model roots in $`u`$ and all the others, with $`d_0\ne-1`$. In a small complex neighborhood of $`\tau_0`$, the physical contour $`R_j=\rho e^{d_0/j}`$ encloses exactly the continuations of the selected simple roots and no others. Indeed the long-block term is $`O(1/j)`$ on the disk. Any possible zero therefore lies $`O(1/j)`$ from $`\lambda`$, so it is in a fixed compact set in the $`u`$ coordinate. Uniform convergence on that set and Rouché's theorem isolate the selected root or pair. Their moduli are at most $`R_j e^{-\delta/j}`$ for some fixed $`\delta>0`$. The same angular bounds as in the [joint contour estimate](../joint-inner-zeros.md#a-contour-uniform-in-the-threshold) give $`|D_j|\gtrsim j^{-1}+|\theta|`$ and $`|\partial_\theta D_j|=O(1)`$ on $`z=R_j e^{i\theta}`$. For $`|\theta|\ge A/j`$ use $`|B(z)|\gtrsim |\theta|`$ and choose $`A`$ large. On $`|\theta|\le A/j`$ use the scaled vertical segment $`\Re u=d_0`$. Integration by parts gives a contour remainder $`J_{n,j}=O(R_j^{-n}/m)`$.

If the model selected only one pole, its physical residue is nonzero and dominates the contour remainder by a factor exponential in $`m`$. The derivative at that simple pole has fixed positive lower and upper bounds by the local scaled equation. Therefore the row polynomial has no zero throughout this parameter neighborhood for large $`j,m`$.

If $`\tau_0>1`$ is real, let $`u_{j,+},u_{j,-}`$ be the two continuing scaled branches, conjugate on the real axis. Put $`r=\rho\exp((u_{j,+}+u_{j,-})/(2j))`$ and $`\varphi=(u_{j,+}-u_{j,-})/(2ij)`$, so the two poles are $`r e^{\pm i\varphi}`$. From the two analytic logarithms of their nonzero $`z`$ derivatives form a positive real normalizer $`A`$ and phase $`\beta`$ on the real axis, such that the two derivatives are $`Ae^{\pm i\beta}`$. Then, with $`N=n+1`$ and $`f_{n,j}=O_{n,j}(-q)/n!`$, the residue formula is

$$
C_{n,j}:=\frac{A r^N}{2} f_{n,j}=-\cos\Phi_{n,j}+E_{n,j},\qquad
\Phi_{n,j}=N\varphi+\beta,\qquad E_{n,j}=\frac{A r^N}{2}J_{n,j}.
$$

On each smaller complex parameter disk, $`|E_{n,j}|+|\partial_\tau E_{n,j}|=O(e^{-\delta m}/m)`$ after decreasing $`\delta`$ if necessary. This follows from the contour bound and Cauchy's inequality. The simple roots $`u_{j,+},u_{j,-}`$ converge with derivatives to their model branches. On the real interval $`j\varphi\to y(\tau)`$ with derivatives, and $`\beta`$ has bounded derivative. In particular $`\Re\partial_\tau\Phi_{n,j}\ge c m`$ on a sufficiently small complex disk around $`\tau_0`$, since $`y'(\tau_0)>0`$.

The univalence argument in the joint inner-edge theorem now applies to this cosine equation. Explicitly, a complex zero in a disk of half the radius maps under $`\Phi_{n,j}`$ to $`o(1)`$ distance of a real zero of the cosine. The derivative lower bound gives injectivity and ensures that the phase image of the larger disk contains the radius-$`1/4`$ circle about this real center. On that circle the cosine exceeds the uniform error in modulus. Rouché’s theorem gives exactly one simple zero, which is real by conjugation. The inverse phase map preserves conjugation, identifying the original zero as real.

For any fixed $`T>1`$, cover the compact set $`|\tau|\le T+1`$ by finitely many of these single-pole, two-pole, and fold neighborhoods, using smaller disks in the two-pole and fold cases. Consequently every row zero with $`|q|\le Q_j(T+1)-1`$ is real and simple, since such a $`q`$ has $`|\tau|\le T+1`$. The nonnegative coefficients of $`O_{n,j}`$ with positive constant term handle $`q<0`$, and the exact positivity theorem handles $`0\le q\le q_j^*`$. Thus these zeros have $`q>q_j^*`$.

## Sign comparison and rank count

On every compact real interval $`1<\tau_1\le\tau\le T+1`$ the phase and remainder can be assembled from the preceding neighborhoods. The upper physical pole stays in the upper half-plane. The argument of its derivative can be chosen in $`(0,\pi)`$ on this interval, since the scaled derivative converges to $`2u_{+}`$ with positive imaginary part. Its branch agrees with the fold phase by the local derivative expansion, so there is no phase ambiguity. The real phase starts at $`\pi/2`$ at the fold and increases thereafter for all large $`j,m`$. Near the fold this is the preceding estimate in $`t=\sqrt{\tau-1}`$. Away from the fold it follows from $`\partial_\tau\Phi_{n,j}\asymp m`$ on compact intervals. The signs in each full band of width $`\pi/6`$ around $`(k+1/2)\pi`$, $`k\ge1`$, give one simple root, and the gaps contain none, by the derivative error estimate. At the fold the half-band has only its forced zero in the sine normalization. Thus the count at $`q=Q_jT-1`$ differs by $`O(1)`$ from $`\Phi_{n,j}(T)/\pi`$. Dividing by $`\lfloor m\rfloor`$ gives $`y(T)/\pi`$.

For strict consecutive order away from the fold, the contour difference continues to gain a factor $`1/j`$. As before, the difference $`r J_{n+1,j}-J_{n,j}`$ includes $`s(z)=r/z-1`$ on the contour. There $`|s|\lesssim j^{-1}+|\theta|`$. Our choice $`d_0\ne-1`$ implies $`|R_j-\lambda|\gtrsim1/j`$, since $`j\log(\lambda/\rho)\to-1`$. Thus $`B`$ has the same lower angular bound as $`D_j`$. Split

$$
\frac{s}{D_j}=\frac{s}{B}-\frac{s\tau Q_j T_j(z)}{B D_j}.
$$

For the second term, factor out $`e^{ij\theta}`$ and integrate by parts at frequency $`n-j`$ exactly as in the joint inner-edge theorem. Its size is $`O(R_j^{-n}/(n-j))`$. Move the first term to a fixed circle $`R_0>1`$ containing no other pole of $`1/B`$. If $`R_j<\lambda`$, this move crosses $`\lambda`$ and contributes a residue bounded by $`O(j^{-1}\lambda^{-n})`$, because $`|r/\lambda-1|=O(1/j)`$. In this case $`d_0<-1`$, so $`r/\lambda\le e^{-\delta'/j}`$ for some $`\delta'>0`$. After multiplication by the positive normalizer $`A r^N/2`$, the total consecutive error is therefore $`O(e^{-c m}/j)`$ for $`m\ge2`$. Finite covers make these estimates uniform on the compact real interval.

At an old root in rank $`k`$, subtract its normalized zero value from the next normalized value. The principal terms give $`\sin\Phi\sin\varphi+\cos\Phi(1-\cos\varphi)`$. Here $`\sin\Phi`$ has sign $`(-1)^k`$ and absolute value bounded below, and $`\sin\varphi\asymp1/j`$ away from the fold. The second term is $`O(1/j^2)`$ and the consecutive contour error is $`O(e^{-c m}/j)`$, proving the sign $`(-1)^k`$. Near the fold use the earlier consecutive bound of order $`t e^{-c m}/(n-j)`$ against the principal sign of order $`t/j`$. The next phase is $`\Phi+\varphi`$, with $`\varphi=O(1/j)`$ in the full range. As in the inner proof, the next sign and monotonicity within each band place the next $`k`$th root strictly before the old root and the next $`(k+1)`$st root strictly after it. The interval up to $`T+1`$ includes this last comparison for every old rank up to $`T`$: the phase gap to $`T+1`$ grows linearly in $`m`$. Complex exclusion on that larger disk makes these comparisons genuine modulus ranks.
