# Consecutive interlacing at a fixed minimum cycle length

**Theorem.** Let $E_{n,k}(t)$ count permutations of $[n]$ with all cycles of length at least $k$, by their number of excedances. For $k=3$ and every $n\ge3$, the $n-2$ nonzero zeros of $E_{n,3}$ are simple and negative. They strictly interlace the nonzero zeros of $E_{n+1,3}$, with the next row supplying both outer roots. More generally, for every fixed $k\ge3$ the same assertions hold for all sufficiently large $n$. [A uniform estimate](quadratic-cutoff.md) gives these conclusions for all $n\ge Bk^2$ with one absolute constant $B$. In all these rows zero itself is simple. This treats the first conjectured threshold in Alexandersson’s statement and reduces every other fixed threshold to finitely many rows. The proof gives an explicit analytic cutoff of 400 at $k=3$. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Author’s derivation and computations](https://github.com/PerAlexandersson/RealRooted/issues/2590#issuecomment-7059794955)

## Poles and the two adjacent coefficients

Write $t=-e^{-s}$ for $s\ge0$. The symmetry $E_{n,k}(t)=t^n E_{n,k}(1/t)$ follows by permutation inversion, since a derangement has no fixed points. Its coefficients of $t$ and $t^{n-1}$ are one. We first work on $-1\le t<0$ and then use this symmetry.

Let $A_m(t)$ be the ordinary Eulerian polynomial with $A_0=1$. A cycle of length $l\ge2$ has enumerator $t A_{l-1}(t)$, by writing the largest label first and counting ascents in the cycle. A singleton has weight one. The unrestricted permutation EGF is $(1-t)e^w/(1-te^w)$ in the variable $w=(1-t)z$. For instance this follows by expanding the denominator and using $\sum_{j\ge0}(j+1)^n t^j=A_n(t)/(1-t)^{n+1}$. By the exponential formula, deleting cycles of lengths below $k$ therefore gives
$$
 \frac{E_{n,k}(t)}{n!(1-t)^{n+1}}=[w^n]\frac{T_s(w)}{1+e^{w-s}},\qquad
 T_s(w)=\exp\!\left(a w-\sum_{l=2}^{k-1}
 \frac{t A_{l-1}(t)}{l!(1-t)^l}w^l\right),\quad a=\frac{-t}{1-t}.
$$
The Eulerian power-sum identity used here also follows by applying $1+t\,d/dt$ repeatedly to $(1-t)^{-1}$. At $k=3$, put $b=a(1-a)$. Then $T_s(w)=\exp(aw+bw^2/2)$.

The poles are $w_p=s+i p\pi$ for odd integers $p$. Let $r=|w_1|$, $\theta=\arg w_1$, $S=\sin\theta=\pi/r$ and $z_p=r/w_p=(\cos\theta+i pS)^{-1}$. Let $\gamma(\theta)$ be the imaginary part of the displayed exponent of $T_s(w_1)$. Define $\Psi_n=(n+1)\theta-\gamma(\theta)$ and
$$
 Y_n=\frac{r^{n+1} E_{n,k}(t)}{2|T_s(w_1)|n!(1-t)^{n+1}}.
$$
The pair $p=\pm1$ contributes $\cos\Psi_n$ to $Y_n$. More precisely, take
$$
 v=2\pi\max(1,\lceil s/(4\pi)\rceil),\qquad R=\sqrt{s^2+v^2}.
$$
Deforming the coefficient circle to $|w|=R$ adds $T_s(w_p)/w_p^{n+1}$ for each enclosed pole: the residue of the generating function there is $-T_s(w_p)$. In $Y_n$ this is the sum over positive odd $p$ with $p\pi<v$ of $\mathrm{Re}(T_s(w_p)z_p^{n+1})/|T_s(w_1)|$, plus a circle error $e_n$. The same contour works for $n+1$.

Here $v\ge\max(2\pi,s/2)$, so $(r/R)^2\le17/20$, with the worst bound at $s=4\pi$. Every point of the circle has distance at least $1/2$ from every pole. Indeed, the nearest radii are those with $|p|\pi=v\pm\pi$; their radial distance is at least $v\pi/(2R+\pi)\ge\pi/(2\sqrt5+1/2)>1/2$. The inverse denominator has modulus at most $8$ on the circle. If $|\Re(w)-s|\ge1/4$, use $|1-e^{-1/4}|>1/5$. Otherwise the distance of $\Im(w)$ to the nearest odd multiple of $\pi$ exceeds $2/5$, and $|1+e^{x+iy}|^2=(1-e^x)^2+4e^x\sin^2(\mathrm{dist}(y,(2\mathbb Z+1)\pi)/2)$ with $x=\Re(w)-s$ gives the bound by $\sin u\ge 2u/\pi$ on $[0,\pi/2]$.

For $k=3$, $|T_s(w_1)|\ge e^{-\pi^2/8}>1/4$. On $|w|\le R$ we have $R\le 3s/2+2\pi$, $a\le\min(1/2,e^{-s})$ and $b\le\min(1/4,e^{-s})$. Hence
$$
 \log |T_s(w)|\le aR+bR^2/2
 \le 3/(2e)+\pi+9/(2e^2)+3\pi/e+\pi^2/2<14 .
$$
For $n\ge400$ and $nS^2\ge1$ the circle estimate yields
$$
 |e_n|,|e_{n+1}|\le 16 e^{14} r(17/20)^{n/2}< S/100.
$$
Indeed $16 e^{14}\pi n(17/20)^{n/2}<1/100$ at $400$ and decreases. This inequality can also be checked with the rational upper bounds $e<3$ and $\pi<22/7$.

We bound the other enclosed poles. For $n\ge100$ and $nS^2\ge1$ the monotonicity of $(1+x/n)^n$ gives
$$
 \sum_{p=3,5,\ldots} p|z_p|^{n}\le
 \sum_{p=3,5,\ldots}p(1+(p^2-1)/100)^{-50}
 \le 3(27/25)^{-50}+\tfrac{25}{49}(27/25)^{-49}<1/10.
$$
The summand decreases for $p\ge3$, so after its first term half the integral from $3$ to infinity bounds the rest. If $s\ge10$, $|T_s(w)|/|T_s(w_1)|<2$ for $|w|\le R$. The real part of the exponent in modulus is bounded above in absolute value by $e^{-s}(3s/2+2\pi+(3s/2+2\pi)^2/2)<1/20$, a decreasing bound from $10$. If $s\le10$, then $S^2>2/25$. Apply the preceding weighted-sum bound with exponent $n/2$ in place of $n$ (use $n/2\ge100$ and $(n/2)S^2\ge1$). The remaining exponent supplies a factor at most $(1+16/25)^{-n/4}$. Even after multiplication by $4e^{14}$ the weighted sum is less than $1/5$. Thus in both ranges the sum with the amplitude ratios is below $1/5$.

Crucially, the relative error is small enough for consecutive rows even where $S$ is small. Exactly
$$
 |z_p-\cos\theta|=S\frac{\sqrt{S^2+p^2\cos^2\theta}}{\sqrt{\cos^2\theta+p^2S^2}}\le pS\qquad(p>0).
$$
The difference of the principal contributions is $\cos(\Psi_n+\theta)-\cos\theta\cos\Psi_n=-S\sin\Psi_n$. The other poles have the additional factor just bounded. The circle estimates consequently prove
$$
 |Y_n-\cos\Psi_n|<1/4,\qquad
 |Y_{n+1}-\cos\theta\,Y_n+S\sin\Psi_n|<S/4. \tag{1}
$$
At $k=3$ these hold for every $n\ge400$ and $nS^2\ge1$.

For every fixed $k\ge3$ the same inequalities (1) hold on $nS^2\ge1$ for all sufficiently large $n$. To see this, the exponent of $T_s$ on $|w|\le R$ is $O_k(e^{-s}(1+s)^{k-1})$ as $s\to\infty$. On the complementary compact $s$-interval this exponent is bounded and $|T_s(w_1)|$ is bounded below. Thus the circle errors are $O_k(\sqrt n(17/20)^{n/2})=o(S)$. Above some fixed $s_k$ all amplitude ratios are below 2. Below $s_k$ the positive lower bound for $S$ supplies an exponentially small factor as in the $s\le 10$ argument.

## Phase checkpoints

At $k=3$ the phase correction is $\gamma=\pi(a+s b)$. Its derivative in $\theta$ is $(s^2+\pi^2)s b(1-2a)$, which lies between zero and $27/e^3+\pi^2/e<6$. Its limits at $\theta=0,\pi/2$ are $0,\pi/2$. Thus $\Psi_n$ increases strictly from 0 to $n\pi/2$. For any fixed $k$, the correction still has bounded derivative. At $s\to\infty$ this follows by differentiating its finite polynomial expression and using $ds/d\theta=-(s^2+\pi^2)/\pi$. At $s=0$ all the odd powers of degree $l\ge3$ have coefficient zero because $A_{l-1}$ has odd degree and is reciprocal. The even powers give real terms and the linear term has imaginary part $\pi/2$. Hence the same phase endpoints and eventual strict increase hold at fixed $k$.

Write $H=\lfloor3\sqrt n/8\rfloor$. Let $\theta_j$ be the hit of $j\pi$ by $\Psi_n$ for $H+1\le j\le n/2$. Extend the samples to $j>n/2$ by $\theta_j=\pi-\theta_{n-j}$. In the lower half every such sample and every larger angle up to $\pi/2$ satisfies $nS^2\ge1$. At $k=3$, $\theta_{H+1}\ge(H+1)\pi/(n+1)>3\pi\sqrt n/(8(n+1))$; the sine of the last quantity exceeds $1/\sqrt n$ for $n\ge400$, by $\sin x\ge x-x^3/6$. At fixed $k$ the bounded phase correction gives the same eventually, since $3\pi/8>1$. By (1), the sign at $t_j=-\exp(-\pi\cot\theta_j)$ is $(-1)^j$, extended by reciprocity to the upper half of the angle range.

The [small-rank argument](small-ranks.md) places the $H$ innermost roots and establishes the next-row signs there, uniformly for $n\ge\max(400,25k^2)$. Each rank $h\le H$ lies at modulus $x$ with $7/8<x/u_h<9/8$, where $u_h=(h/(h+1))^n$. In particular all $H$ precede the first checkpoint in increasing modulus. Indeed at $k=3$ its $s$ is at most $(n+1)/(H+1)$. At fixed $k$ it is at most $(n+1)/(H+1)+o(1)$ because $s\asymp\sqrt n$ there and $\gamma=O_k(e^{-s}(1+s)^{k-1})$. Finally
$$
 n\log(1+1/H)-(n+1)/(H+1)\ge n/(2(H+1)^2)-1/(H+1)>\log(9/8),
$$
using $H+1\le(17/40)\sqrt n$ for $n\ge400$ and the positive Taylor series of $-\log(1-1/(H+1))$.

Between the checkpoints $j=H+1,\ldots,n-H-1$ are $n-2H-2$ sign changes. The $H$ inner roots and their $H$ reciprocal partners supply the remaining $2H$. Degree exhausts all the intervals and gives simplicity. At a middle root with $h$th modulus on the lower half, $\Psi_n$ lies strictly between $h\pi$ and $(h+1)\pi$. For odd $n$ the root in the central interval is exactly $-1$ by reciprocity, where $\Psi_n=n\pi/2$ gives the same phase inequality. Equation (1) gives $|\cos\Psi_n|<1/4$ and therefore $Y_{n+1}$ has sign $`-\mathrm{sgn}\,\sin\Psi_n=(-1)^{h+1}`$. On reciprocating a root the rank is $n-1-h$, and $E_{n+1,k}(1/t)=t^{-(n+1)}E_{n+1,k}(t)$ supplies the corresponding sign there. At every old nonzero root the sign of $E_{n+1,k}(t)/t$ is thus $(-1)^h$. Its value at zero is one and the new degree is one higher. The intermediate value theorem gives strict interlacing in all the asserted rows.

## Exact finite join at minimum length three

Let $E_n=E_{n,3}$, with $E_0=1$ and $E_1=E_2=0$. Delete the largest label. If its cycle had length at least four, removal gives a permitted permutation on $n-1$ labels. Conversely insert the largest label in any of the $n-1$ directed edges of that permutation. Inserting into one of its $h$ ascending edges preserves the number of ascents and inserting into any other edge adds one. If its cycle had length three, choosing the two other labels and choosing one of the two cyclic orders gives weights $t$ and $t^2$. This proves
$$
 E_n=(n-1)tE_{n-1}+t(1-t)E'_{n-1}
       +\binom{n-1}{2}(t+t^2)E_{n-3}.
$$
An independent coefficient reconstruction begins with all permutations, uses inclusion-exclusion on fixed points to obtain $D_n=\sum_{j=0}^n(-1)^j\binom nj A_{n-j}$, and then uses inclusion-exclusion on transpositions:
$$
 E_n=\sum_{j=0}^{\lfloor n/2\rfloor}(-1)^j
       \frac{n!}{(n-2j)!2^j j!}\,t^j D_{n-2j}.
$$
Deleting the chosen fixed points or transpositions preserves the relative order on the other labels and their excedance statistic. A transposition contributes exactly one excedance. The second computation uses the ordinary Eulerian recurrence.

The archived records give the full vector for every $3\le n\le401$, together with two dyadic numbers in $(0,1)$ bracketing each root modulus below one. To evaluate $E_n(-x)/(-x)$ at such an endpoint the verifier uses integer Horner evaluation at fixed binary precision. Each rounded step introduces absolute error less than one scaled unit, and multiplication by $x<1$ contracts prior errors. A magnitude greater than the number of coefficients certifies the exact sign. The checker validates opposite signs, disjoint intervals within each row, and strict alternation of the intervals from consecutive rows. Reciprocity gives the partners above one and, in odd degree, the zero at $-1$. The number of distinct roots obtained equals the degree. These checks cover 399 rows, 398 consecutive pairs and 39,800 dyadic brackets. The analytic proof covers every pair beginning at $n\ge400$. [Exact sign checker](verify_threshold_three.py) · [Independent coefficient reconstruction](verify_cycle_deletions.py) · [Certificate](threshold-three-prefix.jsonl.gz)
