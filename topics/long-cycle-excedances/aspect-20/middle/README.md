# Middle-root signs at sizes 251 through 9,999

Fix integers $251\le n<10000$, $4\le k$ and $n/k\ge20$. Let $E_{N,k}$ be the excedance enumerator of permutations whose minimum cycle length is at least $k$. Put $t=-e^{-s}$, $r^2=s^2+\pi^2$, $\theta=\arg(s+i\pi)$ and $S=\sin\theta=\pi/r$. The following sign comparison holds throughout the continuous interval $nS^2\ge1$ on the half-axis $s\ge0$. With the common positive normalization $Y_N$ and phase $\Psi=(n+1)\theta-\Im G_s(s+i\pi)$ from the [coefficient formula](../../fixed-threshold.md),

$$
|Y_n-\cos\Psi|<0.05,\qquad
|Y_{n+1}-\cos\theta\thinspace Y_n+S\sin\Psi|<0.12 S .
$$

It follows that the actual next row has the strict principal sign at each old root between consecutive phase levels. At $\theta_{\ast}=(\lfloor7\sqrt n/20\rfloor+5/6)\pi/n$ we have $n\sin^2\theta_{\ast}>1$ and $\Psi<(\lfloor7\sqrt n/20\rfloor+1)\pi$. Thus the usual first-hit and degree argument gives the full consecutive interlacing theorem for any pair in this range once its exterior root signs and count before $\theta_{\ast}$ are certified. Formal coverage is ⬜ None. [Amplitude review and replays](amplitude-review/review.md) · [Vertical estimate review](phase/review.md). [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

## Two bounds for each Taylor coefficient

Use $G_s(w)=\sum_{j=1}^{k-1}g_j(s)w^j$, the Taylor polynomial of the logarithm $\log((1+e^{w-s})/(1+e^{-s}))$. On a height interval $u\le s\le v$, set $r_v=\sqrt{v^2+\pi^2}$. We seek upper bounds $c_j$ for $|g_j(s)|r^j$. The linear coefficient gives $c_1=r_v/(1+e^u)$. For $j\ge2$ the logarithmic derivative has the simple-pole expansion, whence

$$
|g_j(s)|r^j\le\frac{2}{j}\sum_{p=1,3,\ldots}
\left(\frac{v^2+\pi^2}{v^2+p^2\pi^2}\right)^{j/2}.
$$

Indeed the ratio before taking the power increases with $s$. Keep $p\le31$; in the remaining sum keep $j-2$ powers at $p=31$ and bound the two remaining powers by $r_v^2/(p^2\pi^2)$. The monotone half-integral bounds $\sum_{p>31,\ p\text{ odd}}p^{-2}$ by $1/62$.

On $u\ge2$ we have a second bound by expanding the logarithm in powers of $e^{-s}e^w$ at zero and taking absolute coefficients,

$$
|g_j(s)|r^j\le\sum_{a\ge1}e^{-au}(ar_v)^j/(a\thinspace j!).
$$

At frequency $a$ the ratio of the next term to the current term is at most $\exp((j-1)/a-u)$. For $au\ge2j$ bound the whole remaining series by its first term divided by $1-e^{-u/2}$. Take the smaller of the two upper bounds for each degree. Estimates that separately bound the entire series need not attain their maxima at the same height.

## A circle for both adjacent rows

A threshold group $K\le k\le L$ has $A=1+3/K$. On every circle of radius $R\le(1+3/k)r$ the quotient of the numerator magnitudes satisfies

$$
\log\frac{\max_{|w|=R}|e^{G_s(w)}|}{|e^{G_s(s+i\pi)}|}
\le \sum_{j=1}^{L-1}c_j(A^j+1).
$$

All poles have the form $w_p=s+ip\pi$, $p$ odd. If $1+8\pi^2/r_v^2>(1+4/K)^2$, take $R=(1+3/k)r$. Its distance to each pole is at least $r/k$ since the nearest nonprincipal radius exceeds $(1+4/k)r$.

Otherwise select a radius in $[r(1+2.7/k),r(1+3/k)]$. Subdivide this interval at every distinct enclosed pole radius in its interior. There are at most $D=2+(1+3/K)r_v/(2\pi)$ resulting intervals, since the positive pole imaginary parts are $\pi,3\pi,\ldots$. The midpoint of the widest interval is at distance at least $0.15 r/(kD)$ from every pole, including exterior poles. Choose this circle for both adjacent coefficients.

If a circle has distance at least $\delta\le1/2$ from the poles, then $|1+e^{w-s}|^{-1}\le4/\delta$. For $|\Re(w-s)|\ge\delta/2$ use $1-e^{-\delta/2}\ge\delta/4$. Otherwise the distance of the imaginary part from an odd multiple of $\pi$ is at least $\sqrt3\delta/2$, and the squared modulus is $(1-e^x)^2+4e^x\sin^2(y/2)$ for $x=\Re(w-s)$ and the nearest imaginary displacement $|y|\le\pi$. The chord bound for the sine gives the claim. Cap the chosen physical distance at $1/2$.

In the normalized coefficient formula the circle error at $N=n$ or $n+1$ is at most $r(r/R)^n/(2|e^{G_s(w_1)}|)$ times the maximum modulus of $e^{G_s(w)}/(1+e^{w-s})$. After division by $S$, the prefactor $2r/(S\delta)$ is at most the larger of $4r_v^2/\pi$ and $2Lr_v/\pi$ on the first circle. On the second use the larger of $4r_v^2/\pi$ and $(40/3) Lr_vD/\pi$. For $b=3$ or $2.7$ respectively, the exponent $n\log(R/r)$ is bounded below by

$$
\max\left(\max(251,1+u^2/\pi^2)\log(1+b/L),\quad 20K\log(1+b/K)\right).
$$

This uses monotonicity of $k\log(1+b/k)$. The [interval checker](check_amplitude.py) verifies the resulting error is less than $S/100$ for both rows. Its 61 integer threshold groups cover $4$ through $499$. Its 630 real height intervals cover $0$ through $315$, since $nS^2\ge1$ implies $s\le\pi\sqrt{9998}<315$.

## Adding the enclosed poles

The [vertical estimate](phase/README.md) bounds the summed nonprincipal residues weighted by $p$ by $0.1$ (a finer replay gives $0.08$). Thus the old value error is below $0.01+0.1/3<0.05$. Subtracting $\cos\theta$ times the old row from the true next row multiplies a common residue by $z_p-\cos\theta$, where $z_p=r/w_p$ and $|z_p-\cos\theta|\le pS$. Its nonprincipal cost is below $0.1S$, and the two circle errors cost less than $0.02S$. At an old zero, $|\sin\Psi|\ge\sqrt{1-0.05^2}>0.12$, yielding the actual sign throughout each open integer phase gap. The entrance and the central phase allow the first-hit argument in the [original uniform comparison](../../effective-uniform.md).

The programs use python-flint 0.9.0 with FLINT 3.6.0 for rigorous real ball arithmetic. The reported decimal maximum in the amplitude output is informational. Every pass is decided by a strict interval comparison.

~~~sh
python -I -B check_amplitude.py --x 20
python -I -B phase/check.py
python -I -B phase/check-independent.py
~~~
