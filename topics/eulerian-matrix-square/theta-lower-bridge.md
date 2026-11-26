# The lower logarithmic bridge for large Eulerian-square zeros

For any fixed $d>0$, every zero of $H_n$ satisfying
$$
 \log|x|\ge d\sqrt{n/\log n}
$$
is simple and negative for all sufficiently large $n$. Here $H_n$ is the Eulerian-square row after dividing out its zero at the origin. The [square-root and upper logarithmic analysis](theta-transition.md) already gives the assertion when $\log |x|\ge c\sqrt n$ for any fixed $c>0$. We prove the range from $d\sqrt{n/\log n}$ to $c\sqrt n$ for sufficiently small fixed $c$ by making the mixed coefficient expansion relative to the two small one-dimensional factors.

## Frozen factors and their pole estimates

For a real $y_0$ in the new range write $\Lambda=y_0^2/n$ and $h=n/y_0$, and use the notation from the [upper logarithmic extension](theta-transition.md#upper-logarithmic-extension). Thus $z=-e^{-y_0-w}$ and $(a,b)$ is an integer maximizer of $A^nB^{n+1-A}e^{-y_0(A+B-2)}$ over the feasible pairs of the reciprocal row. We retain the associated normalized polynomial $S(w)$ and separated factors $U(w),V(w)$, with $m=n+1-a$. The proof for the upper extension that $a,b=(1+o(1))h$ still applies: the losses at the feasible pair nearest to $(h,h)$ are $O(n/h^2)$ and $O(h\log h)$, both $o(n)$. In particular $a,b\asymp h$, $m\sim n$ and
$$
 d^2/\log n\le\Lambda\le c^2,\qquad
 b\Lambda\asymp y_0,\qquad
 \sqrt b\,\Lambda\longrightarrow\infty .
 \tag{1}
$$
As in the upper extension, each anchor coordinate is within one of its continuous optimum while the other coordinate is held fixed.

We treat $U,V$ together by writing a factor as
$$
 W(w)=\sum_{i\ge1-f}(-1)^i
       \exp\bigl(p\log(1+i/f)-(\sigma+w)i\bigr),
$$
with $(p,\sigma,f)=(n,y_0+\log b,a)$ or $(m,y_0,b)$. Then $p\sim n$, $\sigma\sim y_0$, and $|f-p/\sigma|\le1$. The Eulerian pole identity applied at $-e^{-(\sigma+w)}$ gives the exact formula on $\Re(\sigma+w)>0$
$$
 W(w)=(-1)^f\frac{p!\,e^{(\sigma+w)f}}{f^p}
       \sum_{k\in\mathbb Z}(\sigma+w+(2k+1)i\pi)^{-p-1}.
 \tag{2}
$$
Indeed, the same power sum for $A=f+i$ is $A_p(t)/(1-t)^{p+1}$ at $t=-e^{-(\sigma+w)}$, by the Eulerian generating identity. The Eulerian pole expansion cancels the factors $(1-t)^{p+1}$. [Eulerian generating and pole identities](bulk-asymptotics.md#eulerian-poles-and-a-factorial-weighted-row)

Set $s=\sigma+w$ and use the logarithms of $s+i\pi,s-i\pi$ with imaginary parts in $(-\pi/2,\pi/2)$. Define
$$
 \begin{aligned}
 M(w)&=(-1)^f\frac{p!\,e^{sf}}{f^p}
        \exp\bigl(-\tfrac{p+1}{2}[\log(s+i\pi)+\log(s-i\pi)]\bigr),\\
 \Psi(w)&=\tfrac{p+1}{2i}[\log(s+i\pi)-\log(s-i\pi)],\\
 E_W(w)&=|M(w)|e^{|\Im\Psi(w)|}.
 \end{aligned}
$$
Here $E_W$ is the larger modulus of the two kept poles including their common prefactor in (2). On $|\Re w|\le 8\Lambda$, $|\Im w|\le\pi+1$, the omitted poles satisfy
$$
 |W(w)-2M(w)\cos\Psi(w)|\le C e^{-c_1/\Lambda} E_W(w).
 \tag{3}
$$
To prove this, let $t=\Im w$. The closer of $t\pm\pi$ has squared magnitude at most $\pi^2$, while every omitted $t\pm(2k+1)\pi$ for $k\ge1$ has magnitude at least $2k\pi-1$. The squared denominator difference is at least $c_2 k^2$. The relative absolute sum is bounded by twice the sum of $(1+c_3 k^2/\sigma^2)^{-(p+1)/2}$. For $k\le\sigma$, use the bound by $\exp(-c_4 p k^2/\sigma^2)$ and sum, giving $O(e^{-c_5/\Lambda})$ as $p/\sigma^2\asymp1/\Lambda$. For $k>\sigma$, extract an $e^{-c_6p}$ factor using exponent $(p-1)/2$, and sum the remaining reciprocal quadratics, whose sum is $O(\sigma)$. These estimates prove (3) with constants uniform for $\Lambda$ in the stated range.

On this rectangle direct differentiation gives
$$
 \Psi'(w)=-\frac{\pi(p+1)}{s^2+\pi^2},\qquad
 -\Re\Psi'(w)\ge c_7/\Lambda,\qquad
 |\Psi'(w)|\le C_7/\Lambda .
 \tag{4}
$$
For the two kept pole terms, the logarithmic derivatives are $f-(p+1)/(s\pm i\pi)=O(\Lambda^{-1})$, using $|f-p/\sigma|\le1$, bounded $w$, and $p/\sigma^2\asymp\Lambda^{-1}$. Hence for any fixed radius multiple $K$, $E_W$ is comparable at points at distance at most $K\Lambda$ in the rectangle, by integrating these derivatives and taking the maximum. Applying Cauchy estimates to (3) and the two kept terms on disks of radius a fixed multiple of $\Lambda$ gives, for each fixed integer $r\ge0$,
$$
 |W^{(r)}(w)|\le C_r E_W(w)\Lambda^{-r}
 \qquad (|\Re w|\le6\Lambda,\ |\Im w|\le\pi).
 \tag{5}
$$
For (5) with larger imaginary part bounded by $\pi+1/2$, the same proof uses disks inside $|\Im w|\le\pi+1$ by taking $c$ small.

We also need an absolute lower bound for $E_W$. Put $r=\Re s$. The value of the geometric mean of $|s+i\pi|,|s-i\pi|$ is at most $r(1+C/r^2)$ on the rectangle. Stirling's formula then gives
$$
 \begin{aligned}
 E_W(w)&\ge |M(w)|
 \ge c_8\frac{\sqrt p}{r}
   \exp\left[p\left(\frac{rf}{p}-1-\log\frac{rf}{p}\right)
                 -C_8\frac{p+1}{r^2}\right]\\
 &\ge n^{-K_d}
 \end{aligned}
 \tag{6}
$$
for a constant $K_d$ depending on $d$. Here $u-1-\log u\ge0$ for $u>0$, $\sqrt p/r\asymp \Lambda^{-1/2}$, and $\Lambda^{-1}\le(\log n)/d^2$.

## Distance from a simple zero of a factor

Let $Z_W$ be the real zeros of $W$ in $[-2\Lambda,2\Lambda]$, and put $d_W(w)=\min(1,\mathrm{dist}(w,Z_W)/\Lambda)$, with the empty-set convention. There are constants $c_9,c_{10}>0$ such that for sufficiently small fixed $c$ and large $n$
$$
 \begin{gathered}
 |W(w)|\ge c_9 E_W(w)d_W(w)
 \qquad (|\Re w|\le\Lambda,\ |\Im w|\le\pi),\\
 |W'(u)|\ge c_9 E_W(u)/\Lambda\quad(u\in Z_W),\qquad
 |u-v|\ge c_{10}\Lambda\quad(u,v\in Z_W,\ u\ne v).
 \tag{7}
 \end{gathered}
$$
Here and below (5) is available on larger rectangles than the evaluation region of (7).

The real phase $\Psi$ is strictly decreasing by (4). Each real preimage of a half-integer level $(j+1/2)\pi$ in $[-3\Lambda,3\Lambda]$ is separated from the others by at least $\pi\Lambda/C_7$. On a disk of radius $2\rho\Lambda$ about such a preimage $w_j$, with a sufficiently small fixed $\rho>0$, integration of (4) bounds $|\Psi(w)-\Psi(w_j)|$ above and below by constants times $|w-w_j|/\Lambda$. The lower bound follows by integrating the negative real part of the derivative along the segment. The upper bound can be made less than $1/4$ on the whole disk by choosing $\rho$ small. Thus $\cos\Psi$ has a unique simple zero on this disk and has modulus bounded below by a constant times $\rho$ on the circle of radius $\rho\Lambda/2$. By (3) the error in $W/M$ is at most $C e^{-c_1/\Lambda}$ on the larger disk, since $|\Im\Psi|$ is bounded there. Taking $c$ small, Rouché gives a unique real simple zero $u$ of $W$ within $\rho\Lambda/2$ of $w_j$. Conjugation gives reality. Cauchy's estimate on the larger disk for the analytic error in $W/M$ bounds its derivative at $u$ by $C e^{-c_1/\Lambda}/\Lambda$. The derivative of $2\cos\Psi$ at $u$ has magnitude bounded below by a constant times $\Lambda^{-1}$ by (4) and the upper phase bound. Since $W(u)=0$, this yields $|W'(u)|\ge c_{11}E_W(u)/\Lambda$. Combining this derivative estimate with (5) and local comparability of $E_W$, Taylor's formula gives
$$
 |W(w)|\ge c_{12}E_W(w)|w-u|/\Lambda
 \qquad\text{if } |w-w_j|\le\rho\Lambda .
$$
Choose $\rho$ small enough for the Taylor estimate as well, using the uniform constants in (4) and (5) on disks of radius at most $\Lambda$.

To see that every small value of $|W|/E_W$ belongs to such a disk, (3) first gives $|\cos\Psi|e^{-|\Im\Psi|}\le \eta$ when the normalized value and the omitted-pole bound are sufficiently small. The inequality $|\cos(\alpha+i\beta)|\ge|\sinh\beta|$ implies $|\Im\Psi|\le C\eta$ since $|\sinh\beta|e^{-|\beta|}=(1-e^{-2|\beta|})/2$. The real part of the phase is then within $C\eta$ of a half-integer level. Integrating (4) on the vertical segment gives $|\Im w|\le C'\eta\Lambda$ and then puts the phase at $\Re w$ within $C''\eta$ of the same level. The monotone real derivative in (4) gives its real preimage within $C'''\eta\Lambda$ of $\Re w$, using the fixed margins of the real interval. Choosing $\eta$ small, this puts $w$ within $\rho\Lambda$ of the preimage. In the first evaluation rectangle of (7), the corresponding zero lies in $[-2\Lambda,2\Lambda]$. Applying the same confinement to any real zero in $[-2\Lambda,2\Lambda]$ uses the preimages in $[-3\Lambda,3\Lambda]$ above. This gives their simplicity and uniform separation. Outside the phase disks, the normalized modulus is bounded below by a fixed positive constant, proving the remaining part of (7).

## Relative approximation of the mixed coefficient term

We claim uniformly for $|\Re w|\le\Lambda$, $|\Im w|\le\pi$ that
$$
 S(w)=U(w)V(w)-\frac{U'(w)V'(w)}b
        +O\!\left(\frac{E_U(w)E_V(w)}{b^2\Lambda^4}\right).
 \tag{8}
$$
The normalization of the exact row and the univariate factors is the same as in the transition proof. In the box $a/2\le A\le2a$, $b/2\le B\le2b$, at $w=0$ their univariate log weights obey
$$
 \log |\text{term of }U|\le -c_{13}\Lambda |i|(|i|-1),\qquad
 \log |\text{term of }V|\le -c_{13}\Lambda |j|(|j|-1).
$$
This follows from the second derivative and maximal-anchor argument from the upper extension. For the present $w$ the modulus gains at most $e^{\Lambda(|i|+|j|)}$. The cross factor gains at most $e^{C|ij|/b}$; by (1), $b\Lambda\to\infty$, so this term is absorbed in the Gaussian bound after reducing the curvature constant. For any fixed moment order, the weights and their moments are thus bounded in total by powers of $\Lambda^{-1}$, from a Gaussian of the form $\exp(C\Lambda(|i|+|j|)-c_{14}\Lambda(i^2+j^2))$.

The arguments outside the box in the upper extension still apply. The two independent continuous maxima at $n/(y_0+\Re w)$ differ from the anchors by $o(h)$, and any point outside the box loses a fixed positive multiple of $n$ in their exponent sum, against a normalization cost $o(n)$. The separate infinite tails from the endpoints of their box intervals start with $O(e^{-c_{15}n})$ and decay geometrically with exponents of order $y_0$. Inside the box, Eulerian coefficients differ from their model values by relative $O(e^{-c_{16}y_0})$ by the alternating formula, because the lengths are comparable to $n$ and the descent indices are $O(h)$. The sum of these errors is smaller than any power of $n^{-1}$. The same is true of the Gaussian tails with $|i|+|j|>n^{1/20}$, since $\Lambda\ge d^2/\log n$.

On the remaining truncation expand the cross factor to some fixed order $J$:
$$
 (1+j/b)^{-i}=
  \sum_{k=0}^J \frac{(-1)^k(i)_k j^k}{k!\,b^k}
  +O_J\left(\frac{(1+|i|)^{J+1}|j|^{J+1}}{b^{J+1}}\right),
$$
where $(i)_k=i(i+1)\cdots(i+k-1)$. This follows from Taylor's formula in $j/b$ because $(|i|+J+1)|j|/b=o(1)$ on the truncation. The absolute total error is $O_J(b^{-J-1}(\log n)^{T_J})$ for a fixed $T_J$ by the Gaussian moment bounds. The first two terms give $UV-U'V'/b$. Each other term of degree $k$ is a linear combination of products $U^{(r)}V^{(k)}$ with $r\le k$, times $b^{-k}$ and fixed coefficients. By (5), its modulus is at most $C_k E_UE_V(b\Lambda^2)^{-k}$ since $\Lambda\le1$. The finite sum for $k\ge2$ is $O(E_UE_V b^{-2}\Lambda^{-4})$, using $b\Lambda^2\to\infty$ from (1). Finally $E_UE_V\ge n^{-2K_d}$ by (6) and $b\gg\sqrt n$. Choosing the fixed order $J>4K_d+3$ makes the absolute remainder $O(E_UE_V b^{-2}\Lambda^{-4})$. This proves (8).

## Localization for the reciprocal row

Given any reciprocal zero in this range, center at $y_0=-\log|z|$ so its parameter $w_0$ is purely imaginary with $|\Im w_0|\le\pi$. At a zero (8) and (5) give $|U(w_0)V(w_0)|/(E_U(w_0)E_V(w_0))=O(1/(b\Lambda^2))$. By (7) one factor has a real zero $u$ within $K/\sqrt b$ of $w_0$, for an absolute $K$ uniform over this range. Exchange the names of the factors if needed.

Fix a large constant $R>2K$. If the other factor has no zero within $2R/\sqrt b$ of $u$, consider the circle of radius $R/\sqrt b$ about $u$. It lies in $|\Re w|\le\Lambda$ for large $n$. Its distances to the two sets of real zeros are at least $R/\sqrt b$ by separation in (7) and the assumption. Thus $|UV|\ge c_{17} E_UE_V R^2/(b\Lambda^2)$ there. By (5) and (8), $|S-UV|\le C E_UE_V/(b\Lambda^2)$ with $C$ independent of $R$. For $R$ sufficiently large, Rouché gives just one simple zero in the disk, since $UV$ has only the zero $u$ there by (7). The disk is invariant under conjugation, so the zero is real. It is the candidate $w_0$.

If the other factor has a zero $v$ within $2R/\sqrt b$ of $u$, use $\tau=(u+v)/2$, $\Delta=\sqrt b(u-v)/2$, and $\xi=\sqrt b(w-\tau)$. At bounded $\xi$ all points under consideration are at distance $O_R(1/\sqrt b)=o(\Lambda)$ from the two univariate zeros. Their envelopes are comparable there, and (5) and (7) give
$$
 U(w)=U'(u)\left((w-u)+O\!\left(\frac{|w-u|^2}{\Lambda}\right)\right),
 \qquad
 U'(w)=U'(u)\left(1+O\!\left(\frac{|w-u|}{\Lambda}\right)\right),
$$
and likewise for $V$. Substitution in (8) yields uniformly at bounded $\xi$
$$
 \frac{b S(\tau+\xi/\sqrt b)}{U'(u)V'(v)}
 =\xi^2-\Delta^2-1
   +O_R\!\left(\frac1{\sqrt b\,\Lambda}\right).
$$
The remainder from (8) in this formula is $O(1/(b\Lambda^2))$. As in the fixed square-root regime, the two roots of the comparison quadratic are real and at distance at least $2$ from each other. Rouché on disks of fixed radius $1/4$ around them gives one simple real zero in each disk. The candidate has bounded $\xi$ and hence must be in one of these disks for large $n$. This proves that every candidate is real and simple in $w$. The exponential substitution and inversion transfer the conclusion to $H_n$.
