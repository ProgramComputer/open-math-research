# An effective right edge for the Catalan strict-peak polynomials

Let $C_n(t)=\sum_w t^{\mathrm{pk}(w)}$ count Catalan words by their strict peaks, and write $\tau=-11/16$. Then $C_n(t)>0$ for every $n\ge0$ and real $t\ge\tau$. For every $n\ge3$, $C_n$ has a largest real zero, that zero is simple, and the largest real zero of $C_{n+1}$ is strictly larger. The proof below is analytic for the first statement when $n\ge9$ and for the second statement when $n\ge80$. The exact prefix closes these two claims in all sizes. Real-rootedness and interlacing of the remaining zeros across all sizes are not established here. [Alexandersson's full conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjCatalanWordPeaks)

We use the branch-point parametrization and the two slit deformations in the public eventual theorem. The new parts are an explicit exterior coefficient bound, a uniform sign comparison by the pointwise multiplier $c/z$ on the vertical slit, and a derivative bound ensuring simplicity in the same window. These estimates yield a cutoff within the checked prefix. [Prior eventual theorem, §§1 and 4](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/alexandersson-catalan-peaks/EVENTUAL-ZEROS.md)

## The generating function and the outer bound

For $0<c\le1$, let $t=1-c^{-2}$ and $v_n(c)=c^n C_n(t)$. The short-peak enumerator gives
$$
G_c(z)=\sum_{n\ge0}v_n(c)z^n
 =\frac{1-z^2-\sqrt{D_c(z)}}{2z(c-z)},\qquad
D_c(z)=(1+z^2)^2-4cz,
$$
with the square root equal to one at the origin. [Baril et al., Theorem 5.1 specialized to short peaks](https://arxiv.org/html/2404.05672v1#S5.Thmtheorem1)

In both regimes below the first two branch points lie inside $|z|=3/2$, the remaining pair lies outside, and the interior slit joins the first two points. On the circle the rationalized formula gives
$$
|G_c(z)|\le
\frac{1+(3/2)^2+\sqrt{(1+(3/2)^2)^2+6}}{2(3/2)(3/2-1)}
<5.
\tag{1}
$$
Thus its circle integral in coefficient extraction is $E_n(c)$ with $|E_n(c)|\le5(2/3)^n$. At $z=c$ the branch on the other side of the slit has value $-(1-c^2)$, so its pole term is $P(c)c^{-n}$, where $P(c)=(1-c^2)/c^2$. This follows by factoring $D_c$ into its two quadratic factors and continuing the square root around one endpoint of the slit. The cut term is read from the two boundary values in the formulas below.

## Excluding real zeros at and above $\tau$

Let $c_*=4/(3\sqrt3)$. At $c=c_*$, $D_c$ has its double positive root at $1/\sqrt3$. For $c_*<c<1$, its two positive roots $\alpha<\beta$ satisfy
$$
0<\alpha<1/\sqrt3<\beta<c.
$$
Indeed, $(1+z^2)^2/(4z)$ has its unique minimum at $1/\sqrt3$, and $D_c(c)>0$ with $c>1/\sqrt3$. There are no negative real roots. If $p=\alpha\beta$ and $s=\alpha+\beta$, the remaining quadratic is $z^2+s z+1/p$. The coefficient of $z^2$ gives $s^2=(1-p)^2/p$, hence $p\le1/3$ since $s^2\ge4p$ and $p<1$. The remaining conjugate pair thus has modulus at least $\sqrt3>3/2$.

On the horizontal slit $[\alpha,\beta]$, the upper and lower square roots are $-\mathrm i\sqrt{-D_c}$ and $+\mathrm i\sqrt{-D_c}$ respectively. Subtracting its counterclockwise contour when moving the coefficient contour to the outer circle gives
$$
v_n(c)=P(c)c^{-n}+E_n(c)
 +\frac1{2\pi}\int_\alpha^\beta
      \frac{\sqrt{-D_c(z)}}{z^{n+2}(c-z)}\,dz.
\tag{2}
$$
At $c=c_*$ the slit degenerates and the pole term is unchanged. If $c_*\le c\le9/10$, the pole term is at least $19/100$ and the integral is nonnegative. If $9/10\le c<1$, the interval $[9/20,1/2]$ is inside the slit because $D_c\le D_{9/10}<-1/8$ there. Convexity reduces the second inequality to the two rational endpoints. The integral over this interval exceeds $2^n/120$: its length is $1/20$, the square root exceeds $1/3$, the factor $(c-z)^{-1}$ exceeds one, and $z^{-n-2}\ge2^{n+2}$. The resulting terms dominate $5(2/3)^n$ for $n\ge9$. At $c=1$ and all $t\ge0$, positivity follows directly from the defining nonnegative coefficients and the all-zero word. For $n<9$, the exact expansion of $C_n(\tau+u)$ has positive coefficients. Thus $C_n(t)>0$ throughout $t\ge\tau$ in every row.

## Uniform control of the first root

Put $d=\cos\theta$ and take $0\le\theta\le1/(4n)$, $n\ge80$. Use
$$
a=(1+2d)^{-1/2},\qquad x=ad,\qquad b=a\sin\theta,\qquad
c=2a^3d^2(1+d),\qquad Q(z)=z^2+2xz+a^{-2}.
$$
The positive-real-part pair of branch points is $x\pm \mathrm i b$, the remaining pair has modulus $a^{-1}$, and $D_c(z)=((z-x)^2+b^2)Q(z)$. These formulas follow by substituting $z=a e^{\mathrm i\theta}$ in $z^3+2z+1/z=4c$ and using the product and sum of all four roots. The vertical chord joins the first pair and lies to the left of $c$. On the west side of the chord the square root is $+\sqrt{Q(z)}\sqrt{b^2-(\Im z)^2}$, and on the east side it is its negative. This gives
$$
v_n(c)=P(c)c^{-n}+E_n(c)-I_n,\qquad
I_n=\frac{b^2}{2\pi}\int_{-1}^{1}
 \frac{\sqrt{Q(z)}\sqrt{1-y^2}}{z^{n+2}(c-z)}\,dy,\quad z=x+\mathrm i by.
\tag{3}
$$
The integral is real by conjugation. As $\theta$ increases, $c$ decreases strictly and so does $t=1-c^{-2}$.

Here and below the elementary parameter bounds hold on $0\le\theta\le1/20$, which contains the required range. From $d\ge799/800$ one obtains
$$
\frac{57}{100}<x\le |z|\le a<\frac35,\qquad
\frac{19}{25}<c<\frac{39}{50},\qquad
c-x\ge\frac4{25},\qquad
|c-z|\le1.
\tag{4}
$$
For the last inequality use $|c-z|\le c-x+b$, with $b\le(3/5)\theta$. The second pair has modulus $a^{-1}>5/3$, so (1) applies.

On the chord $\Re Q(z)>29/10$ and $|\Im Q(z)|=4x|by|\le(36/25)\theta$. Therefore $|\arg\sqrt{Q(z)}|<\theta/4$. Also $|\arg z|\le\theta$ and $|\arg(c-z)|\le4\theta$. For each of the integrands for $I_n$ and $I_{n+1}$, its argument has absolute value at most $(n+29/4)\theta<2/5$ when the numerator is nonzero. Thus the real part is at least $9/10$ times the modulus. In particular $I_n>0$ for $\theta>0$. Multiplying the integrand for $I_n$ by $c/z$ gives the integrand for $c I_{n+1}$. By (4) and the real-part estimate, its real part is at least $(19/15)(9/10)>11/10$ times the modulus of the old integrand, which dominates its real part. Consequently
$$
c I_{n+1}\ \ge\ \frac{11}{10}I_n.
\tag{5}
$$

At $\theta=1/(4n)$, we have $b\ge\theta/4$, using $a>1/2$ and $\sin\theta\ge\theta/2$. From the real-part estimate and $\int_{-1}^1\sqrt{1-y^2}\,dy=\pi/2$,
$$
I_n\ge\frac9{40}b^2(5/3)^n>\frac{(5/3)^n}{1200n^2}.
$$
Here $|\sqrt{Q(z)}|>1$ and $|c-z|\le1$. The pole term is at most $2(25/19)^n$. For $n\ge80$ we have $(19/15)^n/n^2>3600$ and $5(2/3)^n<(25/19)^n$. Both bounds hold at $n=80$ by rational arithmetic and improve as $n$ increases. Thus $v_n$ is negative at $\theta=1/(4n)$ and positive at $\theta=0$. It has at least one root in this interval.

For uniqueness and simplicity we use $\widetilde I_n=c^n I_n$ and $\widetilde E_n=c^n E_n$. The positively rescaled function in (3) is $P(c)+\widetilde E_n-\widetilde I_n$. On $0<\theta\le1/(4n)$ the following derivative bounds hold:
$$
|c'|\le3\theta,\quad |a'|\le\theta/4,\quad |x'|\le\theta,\quad
|z'|\le2/3,\quad |Q'(z)|\le2.
$$
Primes here denote differentiation in $\theta$ at fixed chord parameter $y$. For $c'$, differentiate $\log c$ with respect to $d$ and use (4). For $a',x',z'$ differentiate their displayed formulas, using $|b'|\le61/100$. For $Q'$ bound the sum of the two $z'$ terms by $2(|z|+x)|z'|\le4(3/5)(2/3)$, then bound the other terms by $2|x'z|+2\sin\theta$. In particular
$$
|c'/c|\le1/5,\quad |z'/z|\le6/5,\quad
|Q'/(2Q)|\le1/2,\quad |(c'-z')/(c-z)|\le6.
$$
The integrand for $\widetilde I_n$ without the prefactor $b^2/(2\pi)$ therefore has derivative of modulus at most $2n$ times its modulus. Its real part is at least $9/10$ times its modulus, so the logarithmic derivative of the integrated real part has absolute value at most $20n/9$. The prefactor contributes $2b'/b\ge2\cot\theta\ge(99/50)/\theta\ge(198/25)n$. Hence
$$
\widetilde I_n'\ \ge\ 5n\,\widetilde I_n.
\tag{6}
$$

On the fixed circle $|z|=3/2$, factorization bounds $|\sqrt{D_c(z)}|\ge(3/2-3/5)(5/3-3/2)=3/20$. From the rationalized expression for $G_c$,
$$
|\partial_\theta G_c(z)|
\le \frac{|c'|}{|c-z|}
    \left(\frac1{|\sqrt{D_c(z)}|}+|G_c(z)|\right)
\le72\theta.
$$
The branch is analytic in the parameters near the circle, so the differentiated circle integral gives
$$
|\widetilde E_n|\le5(13/25)^n,\qquad
|\widetilde E_n'|\le(n+4)(13/25)^n.
\tag{7}
$$
Also $|\frac{d}{d\theta}P(c)|\le20\theta$. At any root in the window we have $\widetilde I_n=P+\widetilde E_n>1/10$, since $P\ge19/100$. There the derivative of $P+\widetilde E_n-\widetilde I_n$ is strictly negative by (6) and (7). All zeros in the window are therefore simple downward crossings. Since there is at least one crossing and the function is real analytic and nonzero at the endpoints, there can be only one. The exterior positivity above makes this root the largest real zero of $C_n$.

Let $\theta_n$ be this root. Evaluating the next row at the same $c$ and multiplying by $c^{n+1}$, (5) implies that its value is at most
$$
-\tfrac1{10}P(c)+|\widetilde E_{n+1}|+\tfrac{11}{10}|\widetilde E_n|<0
$$
by (7). The next row is positive at $\theta=0$, so it has a real root before $\theta_n$ and its largest real zero is strictly larger than that of the old row. Since $d t/d\theta<0$ at every positive $\theta$ in this window, simplicity in the angle variable is simplicity in $t$.

## Exact finite prefix

For the finite rows the companion checker compares the defining coefficient formula with the direct quadratic generating-function recurrence, checks the positive translates for $0\le n<9$, and certifies strict oriented interlacing and simplicity through row $80$ using primitive signed Euclidean remainders. It uses two exact coefficient constructions and matches the checked rows against the archived vectors. This proves the remaining largest-root comparisons, beginning at $n=3$.
