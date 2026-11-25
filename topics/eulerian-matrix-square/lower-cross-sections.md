# Absolute counts from fixed to growing large moduli

There is a fixed $Y_0>0$ such that, for all sufficiently large $n$, every zero of the Eulerian-square row $P_n=xH_n$ in
$$
 Y_0+1\le\log|x|\le3(n+1)^{1/4}
$$
is simple and negative. The estimate supplements the [fixed-annulus theorem](compact-annuli.md) and overlaps the [larger moving cross-sections](left-cross-sections.md). Within this interval the winding at each phase cross-section gives the absolute number of roots inside its circle, including the root at zero.

## The four central integrals

Use $N=n+1$ and $L=\log N$. On the upper semicircle $|x|=e^y$ write $x=-e^\xi$ with $\xi=y-it$, $0\le t\le\pi$, and let $Y_0\le y\le4N^{1/4}$. Use the four terms and branches from the larger moving cross-sections:
$$
 w_\sigma=-\frac{1+e^\xi}{\xi+i\sigma\pi},\qquad
 \tau_{\sigma\eta}=\xi+\log(1+e^{-\xi})-\log(\xi+i\sigma\pi)+i\eta\pi ,
 \qquad \sigma,\eta\in\{+1,-1\}.
$$
Thus $e^{\tau_{\sigma\eta}}=w_\sigma$. Set $R=|w_+|$, $\lambda=\log(NR)$, and keep the exact factor $1-1/(Nw_\sigma u)$ in the outer Eulerian numerator:
$$
 \begin{aligned}
 \mathcal G_N(\omega)
 &=\int_{1/2}^2
 \exp(-Nu)u^N(1-e^{-\omega}/u)^N(\omega+\log u)^{-N}\,du,\\
 W_{\sigma\eta}
 &=n!N^{N+1}w_\sigma^{N+1}\mathcal G_N(L+\tau_{\sigma\eta}).
 \end{aligned}
 \tag{1}
$$
Uniformly over the semicircles, $R\asymp e^y/y$, $|w_-|\le R$ and $\lambda\ge y$, $\lambda\asymp L+y$. In fact, writing $\phi=\pi-t$, the two denominator magnitudes are $\sqrt{y^2+\phi^2}$ and $\sqrt{y^2+(2\pi-\phi)^2}$. The logarithmic radii differ by $O(y^{-2})$, and $\log R=y-\tfrac12\log(y^2+\phi^2)+O(e^{-y})$, which gives $\lambda\ge y$ for all large $N$.

The saddle estimate for (1) gives an analytic logarithm $J_N=\log\mathcal G_N$ with
$$
 J_N(\omega)=c_N-N\log\omega+B_N(\omega),\qquad
 B_N^{(j)}(\omega)=O(N/\lambda^{2+j}),\quad 0\le j\le3,
 \tag{2}
$$
on neighborhoods of the four arguments in (1), with $c_N=-N+\frac12\log(2\pi/N)$ real and $J_N$ real for positive real arguments. Here and below the bounds hold also on horizontal and vertical segments joining those arguments. To verify (2), use the phase
$$
 -u+\log u+\log(1-e^{-\omega}/u)-\log(\omega+\log u)
$$
on a fixed small complex neighborhood of $[1/2,2]$. On disks of radius a small fixed multiple of $\lambda$ about the required $\omega$, the last logarithm has argument with positive real part, and $\log(1-e^{-\omega}/u)$ and its first three $u$ derivatives are $O(e^{-\lambda/2})$. The first three $u$ derivatives of the whole phase differ from those of $\log u-u$ by $O(1/\lambda)$. The unique critical point near $1$ is $1+O(1/\lambda)$. Its critical value is $-1-\log\omega+O(\lambda^{-2})$ by expanding $\log u-u$ to second order at $1$ and using $\log u=O(\lambda^{-1})$ there. Shift the contour horizontally to the imaginary height of the critical point. The connecting endpoints have a fixed negative real phase gap from the saddle. The shifted contour has uniformly negative real second derivative, and the Gaussian and cubic-error estimates from the [factorial saddle](bulk-asymptotics.md#uniform-estimates-for-the-factorial-weighted-row) give relative error $O(N^{-1/5})$. Thus the analytic logarithm is defined by the saddle expression, including its relative error near $1$. The critical value and Gaussian logarithm give $B_N=O(N/\lambda^2)$, and Cauchy's estimate on smaller disks gives (2).

For bounded $\Im\omega$ we also use
$$
 \frac{\int_{1/2}^2
 |e^{-Nu}u^N(1-e^{-\omega}/u)^N(\omega+\log u)^{-N}|\,du}
 {|\mathcal G_N(\omega)|}
 \le C\exp(CN/\lambda^4).
 \tag{3}
$$
Indeed, the critical point moves by $O(\lambda^{-2})$ when $\omega$ moves vertically a bounded distance from the positive axis. This follows by differentiating the phase's first $u$ derivative in $\omega$, with bound $O(\lambda^{-2})$, and using its second $u$ derivative bounded away from zero near the saddle. The real modulus maximum and complex critical value differ in real part by at most $O(\lambda^{-4})$ by the same concavity and Taylor comparison as for the factorial saddle. The real and complex Gaussian factors are of comparable size. This gives (3).

## Ratios on a semicircle

Write
$$
 A=W_{--}/W_{++},\quad B=W_{+-}/W_{++},\quad C=W_{-+}/W_{++},
 \quad \omega=L+\tau_{++},\quad D=\log(\xi+i\pi)-\log(\xi-i\pi).
$$
The four arguments of $J_N$ are $\omega,\omega-2\pi i,\omega+D,\omega+D-2\pi i$. Multiplication gives the exact identity
$$
 A=BCe^{\mathcal K},\qquad
 \mathcal K=J_N(\omega+D-2\pi i)-J_N(\omega-2\pi i)-J_N(\omega+D)+J_N(\omega).
$$
By (2), $J_N''=N/\omega^2+O(N/\lambda^4)$. The mixed difference is $-2\pi iD$ times an average of $J_N''$ over the two straight shifts. Since $D=(2\pi i/y)(1+O(1/y))$, it satisfies
$$
 \Re\mathcal K\ge c\frac{N}{y\lambda^2}.
 \tag{4}
$$
The small $O(1/y)$ terms can be made uniformly small by fixing $Y_0$ sufficiently large. At $t=0$ conjugation gives $|A|=1$, $|B|=|C|=e^{-\Re\mathcal K/2}$. In the stated range the right-hand side of (4) is bounded below by a positive constant times $N^{1/4}$.

Differentiate using $\partial_t=-i\partial_\xi$, $D'=-2\pi i/(\xi^2+\pi^2)$, and $\omega'=1+O(1/y)$, with primes in $\xi$. The identity $\log B=J_N(\omega-2\pi i)-J_N(\omega)$ gives
$$
 \partial_t\log|B|\le -c N/\lambda^2.
$$
Indeed its derivative in $\xi$ is $-2\pi iN/\lambda^2$ up to relative $O(1/y)+O(1/\lambda)$ in complex modulus, by (2). The derivative of $\log C=(N+1)D+J_N(\omega+D)-J_N(\omega)$ in $\xi$ is $(N+1)D'$ plus
$$
 O\!\left(\frac{N}{y\lambda^2}+\frac{N}{y^2\lambda}\right)=O(N/y^3),
$$
using $\lambda\ge y$. Thus $\partial_t\log|C|\le-cN/y^2$. For $\log A=(N+1)D+J_N(\omega+D-2\pi i)-J_N(\omega)$ the derivative in $\xi$ equals
$$
 -2\pi i(N+1)/y^2-2\pi iN/\lambda^2
 +O\!\left((1/y+1/\lambda)(N/y^2+N/\lambda^2)\right).
$$
In fact the shift of $J_N'$ is given by integration of $J_N''$ along $D-2\pi i$, and the additional term $J_N'(\omega+D-2\pi i)D'$ is $O(N/(y^2\lambda))$. Therefore $\partial_t\log|A|\le-cN/y^2$. Also $(\log A)''=O(N/y^3)$. To see the latter, use $D''=O(y^{-3})$, $\omega''=O(y^{-2})$, and $J_N'''=O(N/\lambda^3)$ on the shifts. Consequently all four central terms are bounded by $|W_{++}|$, with
$$
 |B|+|C|\le 2e^{-cN/(y\lambda^2)},\qquad
 |A|\le e^{-ctN/y^2}.
 \tag{5}
$$

## Pole errors and integral tails

We verify uniformly along the semicircles that
$$
 \frac{P_n(x)}{W_{++}}=1+A+B+C
      +O(e^{-cN/\lambda^2}+e^{-cN/y^2}).
 \tag{6}
$$
The exact Eulerian pole formula, followed by the factorial integral on $s=Nu$ for $1/2\le u\le2$, gives the four terms (1) after one retains the two nearest inner poles $w_+,w_-$ and the two indicated outer branches for each. No Eulerian numerator is dropped in (1).

For the inner poles use $\phi=\pi-t$. The omitted squared imaginary denominators exceed $\phi^2$ by at least $4\pi^2$ and grow quadratically with the index. The sum of squared ratios to the largest inner pole is $O(y)$. Thus for $k\ge3n/4$, extracting the $N/2$th power of the largest omitted ratio gives a total ratio for exponent $k+1$ at most
$$
 Cy\left(1+\frac{4\pi^2}{y^2+\pi^2}\right)^{-N/4}
 \le Cy \exp\big(-(\pi^2+O(y^{-2}))N/y^2\big).
$$
This is then multiplied by $R F_n(R)$ after summing the outer row. From (2) and the positive-radius principal-pole estimate justified below,
$$
 \frac{R F_n(R)}{|W_{++}|}
 \le C\exp\big((\pi^2/2+o(1))N/\lambda^2\big).
$$
Indeed the principal term in $R F_n(R)$ is the expression in (1) at radius $R$ and with $\omega=\lambda$. On the upper arc the principal angle $\theta=\Im\tau_{++}$ lies in $[0,\pi]$. Its formula is
$$
 \theta=\phi-\arctan(\phi/y)+\Im\log(1+e^{-\xi}).
$$
Here the last imaginary part is nonnegative and bounded by $C e^{-y}\min(t,\pi-t)$. In particular the angle remains between $0$ and $\pi$, with the latter inequality following from $\pi-\phi=t$ and the bound by $Ce^{-y}t$. The real part cost of changing $\lambda$ to $\lambda+i\theta$ in $-N\log\omega$ is at most $N\theta^2/(2\lambda^2)$. In $B_N$ the first imaginary variation is purely imaginary by reality on the positive axis, and its real cost is $O(N\theta^2/\lambda^4)$ by (2). This proves the angular bound. Since $\lambda\ge y$, fixing $Y_0$ large preserves a positive fraction of the inner gap. The factor $y$ is absorbed since $N/y^2\gg\log N$. For $k<3n/4$, using the sum of squared ratios gives an error bounded by $CyR n!(nR)^{3n/4}$, and (2) bounds its ratio to $|W_{++}|$ by $\exp(-cN\lambda)$. This accounts for the inner error.

For each retained inner pole use the central part of the outer integral. The two branches in (1) contain one of smallest absolute angle. For $w_+$ this is the angle $\theta$ above. For $w_-$ the upper angle is
$$
 \phi+\arctan((2\pi-\phi)/y)+\Im\log(1+e^{-\xi}),
$$
which belongs to $[0,\pi+O(1/y)]$, and the lower angle is this quantity minus $2\pi$. In both cases all omitted branches have absolute angles at least $2\pi-O(1/y)$. Compare the omitted factors pointwise to the retained branch of smallest absolute angle for each fixed $\sigma$. The real part of the logarithmic denominator is the same for this comparison and equals $\lambda+O(1)$ when $u\in[1/2,2]$. The squared-angle gap is bounded below by a positive constant and grows quadratically with the index. Extracting that gap factor for exponent $(N-2)/2$ and summing the remaining reciprocal quadratics gives a ratio bounded by $C\lambda e^{-cN/\lambda^2}$. The ratio between the integral of the modulus of the comparison term and its complex integral is bounded by (3). By (5) its modulus after integration is at most $|W_{++}|$. The entire outer error on this segment is therefore $O(e^{-c'N/\lambda^2})|W_{++}|$, since $N/\lambda^2\gg \log N$ and $N/\lambda^4=o(N/\lambda^2)$.

For completeness, outside $s\in[N/2,2N]$ use $|A_n(w_\sigma s)|\le A_n(Rs)$. For $s\le\sqrt N$ the bound by $n!(R\sqrt N)^n$ after normalization by $n!(NR)^N$ is $O(N^{-n/2})$, which is exponentially smaller than $e^{-N}\lambda^{-N}$ since $\lambda=O(N^{1/4})$. For $s\ge\sqrt N$ and $u=s/N$, the positive-radius Eulerian pole estimate bounds the normalized integrand by
$$
 C(1+\lambda+\log u)e^{N(-1-\log\lambda)}
 \left(u e^{1-u}\frac{\lambda}{\lambda+\log u}\right)^N.
$$
This follows by bounding the nonprincipal ratios by the reciprocal quadratics, with sum $O(1+\lambda+\log u)$. Since $R>1$ for large fixed $Y_0$, $\lambda\ge\log N$ and the logarithmic ratio is at most $2$ for $N^{-1/2}\le u\le1/10$. The bracket there is at most $(2/10)e^{9/10}<1$. On $[1/10,1/2]$ the ratio is $1+O(1/\lambda)$ and the other factor is at most $e^{1/2}/2$. On $[2,\infty)$ the ratio is at most one and $u e^{1-u}\le(2/e)e^{-(u-2)/2}$. The tails of the normalized integral are exponentially small. The comparison with $|W_{++}|$ introduces only $\exp(O(N/\lambda^2))$ by (2). This argument also applies to the positive-radius integral itself, and its central error from the poles other than the real principal term is exponentially small in $N/\lambda^2$ by the same pointwise denominator comparison. This establishes the positive-radius estimate used above and completes (6).

## Winding and coverage

Define $\Xi_n(y)$ as the continuous argument of $W_{++}$ at the negative endpoint of the upper arc, taken from the positive endpoint, where $W_{++}$ is positive real. Its value is
$$
 \Xi_n(y)=\Im\big((N+1)\tau_{++}(y)+J_N(L+\tau_{++}(y))\big).
$$
This is the correct branch of the continuous argument since $\tau_{++}$ and $J_N$ are real at the positive endpoint. When $\Xi_n(y)=k\pi$, conjugation at $t=0$ gives $A=1$. The logarithmic derivative of $A$ in $\xi$ on the real axis is purely imaginary, because $|A|=1$ there. In the motion $\xi=y-it$ its first derivative in $t$ is therefore real at zero. With the second derivative estimate from the ratio analysis this yields
$$
 |\arg A|\le C N t^2/y^3
$$
for the continuous argument starting at zero. If $|A|>1/4$, (5) gives $t=O(y^2/N)$, leading to $|\arg A|=O(y/N)=o(1)$ and hence $\Re A\ge0$. Otherwise $\Re A\ge-1/4$. Equations (5) and (6) now imply $\Re(P_n/W_{++})>0$ on the entire semicircle for all large $n$.

At the positive endpoint $P_n$ is positive from its coefficients. At the negative endpoint the quotient is real and positive, so the principal argument of the quotient starts and ends at zero along the arc. Thus the continuous argument of $P_n$ rises by exactly $k\pi$ along the upper arc from positive to negative real. Reflection using the real coefficients gives a change of $2k\pi$ on the full circle. No root lies on it, and the argument principle counts exactly $k$ roots inside with multiplicity. This count is absolute since the branch is fixed at the positive endpoint of every circle.

On the real $y$ line set $\theta=\pi-\arctan(\pi/y)$. Differentiation gives $\Im\tau_{++}'=\pi/(y^2+\pi^2)$ exactly and $\Re\tau_{++}'=1+O(1/y)$. With $\omega=\lambda+i\theta$ and $\lambda\ge y$, the contribution of $-N\log\omega$ to the phase derivative equals
$$
 N\frac{\theta\,\Re\tau_{++}'-\lambda\,\Im\tau_{++}'}{\lambda^2+\theta^2}
 \ \ge\ -O\!\left(\frac{N}{\lambda y^2}\right).
$$
The $B_N$ derivative contributes only $O(N/\lambda^3)=o(N/y^2)$. Hence $\Xi_n'(y)\ge cN/y^2$ and is also $O(N/y^2)$. Consecutive phase cross-sections are separated by $O(N^{-1/2})$ throughout the interval $Y_0\le y\le4N^{1/4}$, so every root with $Y_0+1\le y\le3N^{1/4}$ is between two consecutive zero-free cross-section circles. Their absolute counts differ by one. Conjugation puts the single root on the real axis, positivity puts it on the negative axis, and the count proves its simplicity.
