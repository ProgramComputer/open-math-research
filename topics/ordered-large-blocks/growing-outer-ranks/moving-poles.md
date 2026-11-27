# Diverging scaled modulus for ordered large-block enumerators

**Theorem.** Let $`O_{n,j}`$ sum over all ordered partitions of $`[n]`$, marking each block of size at least $`j`$. Put $`m=\lfloor n/j\rfloor`$. Suppose $`m,j\to\infty`$, and the integer defect $`h`$ satisfies $`h/m\to0`$, $`h/\sqrt m\to\infty`$, and $`hj/m\to\infty`$. Write $`q_{n,j,k}`$ for the modulus of the $`k`$th root of $`O_{n,j}`$ in increasing modulus, counting multiplicity. The roots at and immediately around $`k=m-h`$ are simple and negative, and

$$
q_{n+1,j,k}<q_{n,j,k}<q_{n+1,j,k+1}.
$$

The argument is uniform in the remainder $`n-mj`$. It handles a whole window of defect indices and leaves the critical scale $`h\asymp\sqrt m`$ to the [theta argument](theta.md). The modulus rank assertion uses the [compact-parameter argument](compact-start.md) to start the count. [Alexandersson’s ordered-partition conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1) · [Fixed outer ranks, PR #223](https://github.com/ProgramComputer/open-math-research/pull/223)

## Denominator and pole coordinate

Set $`\lambda=\log 2`$ and $`U_j(z)=\sum_{b\ge0}j!z^b/(j+b)!`$. For the parameter $`q`$ corresponding to the original variable $`-q`$, let $`Q=1+q`$ and write

$$
B(z)=1-z,\qquad H(z)=\frac{2-e^{\lambda z}}{1-z},\qquad G(z)=H(z)^{-1},\qquad
V_j(z)=\frac{\lambda^j}{j!}U_j(\lambda z)G(z).
$$

The ordered-block generating function gives

$$
f_n(q):=\lambda^n O_{n,j}(-q)/n!=[z^n]\frac{G(z)}{D(z)},\qquad D(z)=B(z)+Qz^j V_j(z).
$$

The functions $`G`$ and $`V_j/V_j(1)`$ are analytic and nonzero on a fixed disk $`|z|<R_f'`$ for some $`R_f'>1`$ and large $`j`$. Their inverses and any fixed number of derivatives are uniformly bounded on a slightly smaller disk. Indeed $`H`$ has removed its zero at 1 and the other zeros of $`2-e^{\lambda z}`$ lie well outside that disk. The series $`U_j(\lambda z)`$ tends to 1 uniformly, with derivatives on smaller disks.

Write $`\log(QjV_j(1))=A+i\psi`$ with $`A`$ real and $`-\pi\le\psi\le\pi`$, and define $`u>0`$ by $`u+\log u=A`$. For $`z=e^{-w/j}`$ put

$$
C_j(w)=\frac{1-e^{-w/j}}{w/j},\qquad
\alpha_j(w)=\log\left(\frac{V_j(e^{-w/j})}{V_j(1)C_j(w)}\right),\qquad F(w)=w+\log w-\alpha_j(w).
$$

The first logarithm is the branch zero at $`w=0`$. On $`|w|\le\epsilon j`$ it obeys $`\alpha_j^{(a)}=O(j^{-a})`$ for each fixed $`a\ge1`$ on a smaller disk. The second logarithm is real on the positive real axis. The equation for a pole in the right half-plane is $`F(w)=A+ib`$, where $`b=\psi+(2\ell+1)\pi`$. More precisely,

$$
jD(e^{-w/j})=wC_j(w)\bigl(1+e^{A+i\psi-F(w)}\bigr).
$$

Write $`M=n/j`$ and $`\mu=M/u^2`$. In the moving windows below $`u`$ is at least a sufficiently large absolute constant and at most $`u_{\max}=o(\sqrt M)`$. We take $`u_{\max}=3m/h`$. Since $`h=o(m)`$, this endpoint tends to infinity. The minimum of $`\mu`$ on the window is of order $`h^2/m`$, which tends to infinity. Also $`u_{\max}/j=3m/(hj)\to0`$. These bounds persist under fixed padding in $`A`$ since $`du/dA=u/(u+1)`$. Constants in the following bounds are absolute after a fixed choice of the compact analytic disk and a fixed lower bound for $`u`$.

## A circle beyond many pole pairs

Choose a fixed large $`K`$ and on $`|v|\le Ku`$ solve $`\Re F(x(v)+iv)=A`$ for $`x(v)`$. The solution is unique in a strip $`x=u+O_K(1)`$. This follows from $`\partial_x\Re F=1+O_K(1/u)`$ and comparison on $`x=u\pm L_K`$ for a large fixed $`L_K`$. It is even in $`v`$, and $`x(0)=u+O(u/j)`$. For $`v\ge0`$, the imaginary part of $`\alpha_j'(x+iv)`$ is $`O(v/j^2)`$ by conjugation and the second derivative bound. Thus implicit differentiation gives

$$
-x'(v)=\frac{-\Im F'(x(v)+iv)}{\Re F'(x(v)+iv)}\asymp_K \frac{v}{u^2},\qquad
\frac{d}{dv}\Im F(x(v)+iv)=\frac{|F'(x(v)+iv)|^2}{\Re F'(x(v)+iv)}\asymp_K1.
$$

Consequently $`v`$ and the positive target $`b=\Im F`$ are comparable. If $`0\le |b_1|\le |b_2|`$ are realized in this interval, then

$$
x_{b_1}-x_{b_2}\asymp_K\frac{b_2^2-b_1^2}{u^2},
\qquad x_b:=\Re w_b.
$$

To choose a zero-free circle, vary $`d`$ over $`[u-2,u-1]`$. The equation $`\Re F(d+iv_*)=A`$ has a unique $`v_*>0`$, with $`v_*\asymp u`$. For example, writing $`d=u-a`$ with $`1\le a\le2`$, the limiting expression for $`\Re F(d+ivu)-A`$ is $`-a+\tfrac12\log(1+v^2)`$, uniformly for bounded $`v`$. Its derivative with respect to the unscaled vertical variable is $`\asymp1/u`$ near $`v_*`$. Implicit differentiation gives $`v_*'(d)\asymp-u`$, and the derivative of $`\Im F(d+iv_*(d))`$ has the same order with negative sign. Its range therefore traverses a full period for large $`u`$. Choose $`d`$ so that this phase stays a fixed distance from both target classes $`\pi+\psi`$ and $`\pi-\psi`$ modulo $`2\pi`$. The midpoint of a larger complementary arc has clearance at least $`\pi/2`$, including coincident classes.

Set $`R=e^{-d/j}`$. For $`|v|\le Ku`$ the circle is the line $`w=d+iv`$ with $`v=-j\theta`$. Within a fixed small distance of $`\pm v_*`$ the phase clearance persists. Elsewhere $`|\Re F(d+iv)-A|\gg 1/u`$ by monotonicity in $`|v|`$ and the derivative lower bound near $`v_*`$. In either case $`|1+e^{A+i\psi-F(w)}|\gg1/u`$. As $`|wC_j(w)|\gg u`$, this gives $`|D(Re^{i\theta})|\gg 1/j`$. For $`|\theta|\ge Ku/j`$, one has $`|1-Re^{i\theta}|\gg|\theta|`$ on $`[-\pi,\pi]`$, while $`|Q|R^j\sup|V_j|\ll u/j`$. Taking $`K`$ large yields an outer bound $`|D(Re^{i\theta})|\gg|\theta|`$. Also $`|D_\theta|\ll u`$ everywhere on the contour.

Every zero inside the circle satisfies $`|1-z|\le |Q|R^j\sup|V_j|\ll u/j`$. Its principal $`w=-j\log z`$ thus obeys $`|w|\le Ku`$ on increasing $`K`$ if necessary. Since $`\Re w\ge d`$, the mean-value bound in $`x`$ places it on the curve above. This lists all enclosed poles and shows that they are simple. The first one or two poles have bounded $`|b|`$, so $`x_b=u+O(u/j+u^{-2})`$ and $`x_b-d\ge1/2`$ for large parameters. The separator can be much farther from the principal poles than the spacing between the closest pole pairs.

## Value error and consecutive error

The residue theorem yields

$$
f_n(q)=\sum_{w_b\ \mathrm{inside}}K_j(w_b)e^{Mw_b}+J_n,
\qquad K_j(w)=\frac{G(e^{-w/j})}{w C_j(w)F'(w)},\qquad
J_n=\frac{R^{-n}}{2\pi}\int_{-\pi}^{\pi}e^{-in\theta}\frac{G(z)}{D(z)}\mathrm{d}\theta .
$$

Here $`z=Re^{i\theta}`$. The sign and power follow from $`D_z'=-w C_j(w)F'(w)/z`$ at the pole and from subtracting the residues when moving the coefficient contour out. Each enclosed $`K_j`$ has modulus between constant multiples of $`1/u`$.

An integration by parts bounds $`J_n=O(R^{-n}u^2/M)`$. On $`|\theta|\le Ku/j`$, the derivative of $`G/D`$ costs $`O(uj^2)`$ on an interval of length $`O(u/j)`$. Outside this interval integrate $`O(u/\theta^2)`$, which costs $`O(j)`$, and then divide by $`n`$. After normalization by a principal residue, the gap $`x_b-d\ge1/2`$ makes the circle error $`O(e^{-cM})`$.

For real positive $`Q`$ let $`w_+=x+iv`$ correspond to $`b=\pi`$, with $`r=e^{-x/j}`$. Use the same contour for $`f_n`$ and $`f_{n+1}`$. Thus $`rJ_{n+1}-J_n`$ has multiplier $`S(z)=r/z-1`$. Estimating this multiplier against the circle directly can introduce a factor $`\log j`$. Instead split exactly

$$
\frac{SG}{D}=\frac{SG}{B}-\frac{SG Qz^j V_j}{BD}.
$$

Move the first term to a fixed radius $`1<R_f<R_f'`$ crossing $`z=1`$. The residue gives $`O(u/j)`$ since $`|S(1)|=|r-1|=O(u/j)`$, and the new circle gives $`O(R_f^{-n})`$. The possible Laurent term of $`S`$ at zero causes no extra contribution when deforming one positive-radius circle to the other. The bound $`R_f^{-n}\ll1/j`$ is uniform in $`j`$.

For the second term factor $`e^{ij\theta}`$ out of $`z^j`$ and integrate the remaining periodic amplitude by parts at frequency $`n-j`$. To check the variation, in the inner interval use $`|B|\gg u/j`$, $`|D|\gg1/j`$, $`|S|\ll u/j`$, $`|Q|R^j|V_j|\ll u/j`$, $`|D_\theta|\ll u`$, and $`S_\theta,B_\theta,G_\theta=O(1)`$. The derivative of the remaining amplitude is $`O(u^2j)`$ and its integral is $`O(u^3)`$. In the outer interval use $`|B|,|D|\gg|\theta|`$, $`|S|\ll|\theta|`$, and a derivative bound $`O(u^2/(j\theta^2))`$. This contributes $`O(u)`$ to the variation. Thus the second term is $`O(R^{-n}u^3/(Mj))`$. Both parts, after the positive principal normalization $`r^n/(2|K_j(w_+)|)`$, are $`O(e^{-cM}/j)`$ after absorbing polynomial factors in $`u,M`$. In the first part use $`r^n=e^{-Mx}`$.

For real $`Q`$, the normalized residue sum beyond the principal pair is $`O(e^{-c\mu})`$. Indeed the $`b`$th term is bounded by $`C\exp[-c\mu(b^2-\pi^2)]`$ and the sum over odd multiples starting at $`3\pi`$ keeps the same scale without a factor depending on the number of enclosed poles. Each term in the normalized consecutive difference gains

$$
|re^{w_b/j}-1|\ll\frac{|b|}{j}.
$$

This uses $`|\Im w_b|\ll|b|`$ and $`|x_b-x|\ll(b^2-\pi^2)/u^2`$; all enclosed $`|b|`$ are $`O(u)`$. The weighted Gaussian sum is still $`O(e^{-c\mu})`$. The consecutive error is therefore $`O(e^{-c\mu}/j)`$, even if $`j`$ is superexponential in $`M`$ or if $`\mu`$ diverges arbitrarily slowly.

## Complex exclusion and simple real roots

For complex $`Q`$ the targets remain $`b=\psi+(2\ell+1)\pi`$ on the same real-level curve. When $`|\psi|\ge\delta/2`$ for a fixed small $`\delta>0`$, precisely one target has least absolute value. The two smallest absolute values are $`\pi-|\psi|`$ and $`\pi+|\psi|`$. Their squared difference is $`4\pi|\psi|`$. The normalized sum of other terms is then $`O(e^{-c\delta\mu})`$ by the same separation and Gaussian summation. The absolute circle bound gives a still smaller error. The principal residue is nonzero, so there is no polynomial zero in this part of the complex parameter annulus.

For $`|\psi|\le\delta`$, keep the two analytic continuations $`w_\pm(L)`$ of the $`\pm\pi`$ poles, where $`L=A+i\psi`$. They solve $`F(w_\pm(L))=L\pm i\pi`$. Their existence on fixed small disks about the real axis is uniform since $`F'=1+O(1/u)`$ near both roots. For instance on a fixed small circle about an old pole, $`F(w)-F(w_\pm(A))`$ differs from $`w-w_\pm(A)`$ by a relative $`O(1/u)`$, and Rouché gives the inverse on the smaller parameter disk. Write

$$
X(L)=\frac{w_+(L)+w_-(L)}2,\qquad K_\pm(L)=K_j(w_\pm(L)),\qquad
\gamma(L)=\frac{\log K_+(L)-\log K_-(L)}{2i},\qquad
\Phi(L)=M\frac{w_+(L)-w_-(L)}{2i}+\gamma(L).
$$

The logarithms are conjugate along the real axis. Their choices can be made continuously along that axis with $`\gamma(A)=O(1)`$, since $`K_j(w_+(A))=(G(1)/u)(1+O(u^{-1}+u/j))`$. Put $`\mathcal K(L)=\exp((\log K_++\log K_-)/2)`$, positive on the real axis. The exact normalized equation is

$$
\frac{f_n(q)}{2\mathcal K(L)e^{MX(L)}}=\cos\Phi(L)+E_n(L),\qquad |E_n(L)|\le C e^{-c\mu}.
$$

In fact both principal targets have modulus at most $`\pi+\delta`$, all later ones have modulus at least $`3\pi-\delta`$, and the real part of $`X`$ is the mean of the two principal real parts. This gives the required suppression of every nonprincipal residue relative to this normalization, even when the two main terms are not balanced in absolute value. The circle bound persists because both principal real parts exceed $`d+1/2`$. The positive-radius circle can vary pointwise with $`L`$ in these bounds. The normalized error is an analytic function of $`L`$ by its definition after subtracting the analytic principal terms. Thus Cauchy's estimate gives the same exponential bound for $`E_n'`$ on fixed smaller log-parameter disks, using comparability of $`\mu`$ across a fixed disk.

On the real axis, $`v=\Im w_+`$ satisfies

$$
v'=\Im(1/F'(w_+))\asymp u^{-2}>0,
\qquad
\Phi'=Mv'+O(u^{-1})\asymp\mu .
$$

The derivative bounds follow from $`w_+'=1/F'(w_+)`$ and $`F''=O(u^{-2})`$. In particular $`\Phi''=O(\mu)`$ on fixed sufficiently small complex disks after using $`w_\pm''=-F''(w_\pm)/(F'(w_\pm))^3`$ and the derivative bounds on $`K_j`$. Shrink $`\delta`$ by an absolute factor to obtain $`\Re\Phi'\ge c\mu`$ on each disk of radius $`\delta`$ centered at a real $`A`$ in the range. These disks may use a fixed padding at the outer edge of the range.

If $`L_0=A+i\psi`$ with $`|\psi|\le\delta/2`$ is a zero, then $`\Phi(L_0)`$ lies within $`O(e^{-c\mu})`$ of a real member of $`\pi/2+\pi\mathbb Z`$, by $`|\cos(a+ib)|^2=\cos^2 a+\sinh^2 b`$. On the log-parameter disk of radius $`\delta`$ about $`A`$, integrating the lower real derivative bound along straight segments gives $`|\Phi(L)-\Phi(L_0)|\ge c\mu|L-L_0|`$. The map is injective there, and its image contains the radius-$`1/4`$ disk about the indicated half-integer multiple of $`\pi`$. The inclusion follows by applying Rouché to $`\Phi(L)-\Phi(L_0)`$ on the disk boundary and shifting the target by less than the boundary minimum. In that image disk, Rouché against the cosine gives exactly one simple zero. The original parameter disk and the target disk are both symmetric under conjugation, and the inverse phase commutes with conjugation. Hence the zero is real and simple. This excludes every nonreal or multiple zero with scaled log modulus $`A`$ in the range. It covers both the near-real strip and the complementary arguments handled by one-pole dominance.

## Consecutive signs and exact ranks

On real $`A`$, set $`r=e^{-\Re w_+/j}`$ and use the positive normalization $`r^n/(2|K_j(w_+)|)`$ for $`f_n`$. In the next row the normalized pole contribution is $`\cos(\Phi+\varphi)`$ with $`\varphi=v/j\asymp1/j`$. Evaluating at an old zero and subtracting its normalized zero value, one obtains the next-row sign from

$$
\cos(\Phi+\varphi)-\cos\Phi+O(e^{-c\mu}/j)
=-\sin\Phi\sin\varphi+\cos\Phi(\cos\varphi-1)+O(e^{-c\mu}/j).
$$

At that point $`|\cos\Phi|\le C e^{-c\mu}`$ and $`|\sin\Phi|`$ is bounded below. The sign is $`-\mathrm{sgn}(\sin\Phi)`$, the sign of the normalized derivative inside the old root's phase band. The same derivative sign holds for the next row in that band, since $`\Phi_{n+1}=\Phi+\varphi`$, the band centers differ by $`O(1/j)`$, and $`E_{n+1}'=O(e^{-c\mu})`$. To use fixed phase bands, one may locate each old and new root within $`O(e^{-c\mu})`$ of its half-integer phase level, then use the derivative on the larger band of width $`\pi/6`$ about that level. Each full band has exactly one root by the endpoint signs and strict derivative sign, and the gaps have none. At the old root the new value has the same sign as the derivative of the new row in the band. Thus the neighboring new root in this band lies at a strictly smaller positive $`q`$, and the one in the following band lies at a strictly larger $`q`$.

The phase labels agree for both rows on overlap with the fixed-scaled-modulus proof. To see this concretely, $`Q_j jV_j(1)\to e^{-1}`$ for the sharp-edge scale $`Q_j=1+q_j^*`$, since $`q_j^*\sim2(j-1)!/(e\lambda^{j-1})`$. Therefore a fixed interval of large $`A`$ corresponds to a fixed compact interval of the parameter $`\tau=Q/Q_j`$ from that proof. The principal physical radii there are the same poles, since the changes of coordinates differ by a real translation and sign. The older residue normalization uses $`-\cos((n+1)\varphi+\beta)`$, where $`\beta`$ is an argument of the original denominator derivative at the upper physical pole. The present formula uses $`+\cos(Mv+\gamma)`$. At the lower physical pole one has $`K_j=-G/(zD_z')`$, so conjugation shows that the phases differ by a constant odd multiple of $`\pi`$ on any connected overlap. This difference is the same in both rows since the change of argument is independent of $`n`$. Hence a band has the same rank in both rows by the fixed-scaled-modulus theorem, and the consecutive band count preserves this correspondence throughout the range. The complex exclusion in the annulus of $`|Q|`$ combines with the compact exclusion below it because $`|1+q|\le1+|q|`$. Thus the ranks are also ranks in modulus among all complex roots. The compact starting argument is given separately. [Compact rank start](compact-start.md)

For clarity on the last rank claim, the bounded-target pole equation gives

$$
\pi-v=\arg(w_+)-\Im\alpha_j(w_+)=\frac{\pi}{u}+O(u^{-2}+j^{-1}).
$$

Here $`x=u+O(u/j+u^{-2})`$, $`v=\pi+O(u^{-1}+j^{-1})`$, and the imaginary part of $`\alpha_j`$ is $`O(1/j)`$ by conjugation. The band count together with its compact starting value gives a cumulative count $`K(A)=\Phi(A)/\pi+O(1)`$, for both rows, and hence

$$
m-K(A)=\frac m u+O(m/u^2+m/j+1).
$$

Choose endpoints with $`u=m/(2h)`$ and $`u=2m/h`$. The first has fewer than $`m-h`$ roots and the second has more, by margins of order $`h`$. The uniform contour proof applies from a fixed large $`u`$ up to a padded endpoint, for instance $`3m/h`$, where the infimum of $`\mu`$ still tends to infinity. This leaves complete bands at and around rank $`m-h`$ for all large parameters, and the comparisons above prove the proposed strict order, including a degree carry in $`n\mapsto n+1`$.

## Uniformity in the threshold growth

The three parameters needed in the moving range are $`u/j=o(1)`$, $`u^2/M=o(1)`$, and a sufficiently large fixed lower bound on $`u`$. In the level-curve derivative, the imaginary perturbation $`O(v/j^2)`$ is of relative order $`O((u/j)^2)`$ compared with $`v/(x^2+v^2)`$. Thus the nearby pairs are compared on a common real-level curve even when the displacement of that curve from the limiting Lambert curve exceeds the gap between two pairs. The circle and residue estimates use $`u/j=o(1)`$ for the local variable change and $`u^2/M=o(1)`$ for summability. The fixed-radius contribution uses $`R_f^{-n}=O(1/j)`$ directly. The compact start needs only joint growth of $`j`$ and $`m`$.

At the two rank-bracketing endpoints, $`m/u^2=O(h^2/m)=o(h)`$ and $`m/j=o(h)`$, so the errors in the defect count are $`o(h)`$. The hypotheses therefore suffice in the full range $`h\gg\max(\sqrt m,m/j)`$, in the sense that both ratios tend to infinity.

The contour and phase estimates also hold on a padded window with $`u\le\varepsilon j`$ for a sufficiently small fixed $`\varepsilon>0`$, provided the infimum of $`M/u^2`$ still tends to infinity. Choose the nonvanishing disk first, the constant $`K`$ in the angular bounds next, and then $`\varepsilon`$ small enough for both the local coordinate and the derivative comparison. On the separator $`d=u-a`$ the scaled crossing comparison is $`-a+\tfrac12\log(1+v^2)+O_K(1/u+\varepsilon)`$ at height $`uv`$. Fixed test heights enclose the crossing. The outer circle and signed residue estimates retain the same bounds. In this larger window the defect error $`O(m/j)`$ can affect integer ranks, so a separate saddle calculation would need an exact overlapping rank count to make a join. [Independent audit of the enlarged window](review-pole-overlap.md)

## Provenance and scope

The generating function and statistic are those of Alexandersson's ordered-partition conjecture rather than its neighboring unordered variant. The use of analytic pole phases, compact-parameter exclusion and the consecutive multiplier $`r/z-1`$ follows the [joint inner-edge proof](../joint-inner-zeros.md) and its [compact extension](compact-start.md). The additional estimates here concern a separator beyond $`O(u)`$ poles, a summable Gaussian bound on those residues, and the factor $`1/j`$ through the new moving annulus. The original proof and its uniformity through the larger parameter endpoint have [independent review](review-moving-poles.md). [Original conjecture and generating function](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)
