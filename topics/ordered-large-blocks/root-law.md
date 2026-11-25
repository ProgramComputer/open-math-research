# The limiting zeros at ordered threshold two

Let $q_{n,j}$ denote the positive moduli of the zeros of $O_{n,2}$, listed in increasing order, and let $m=\lfloor n/2\rfloor$. The phase and both edges below use the principal upper pole from the [proof of interlacing](threshold-two.md). This gives a probability law for all the zeros as well as different scales for the smallest and largest ones.

Let $v_*\in(1/2,1)$ solve $-2v_*-\log(1-v_*)=0$ and set $q_*=1/v_*-1$. For $q>q_*$ put $v=1/(1+q)$, $a=1-2v$. Let $0<\theta<1$ be the unique solution of
$$
 \theta\cot\theta-\log(\theta/\sin\theta)=1-2v-\log(1-v).
$$
Define $u=\theta\cot\theta+i\theta$, $z=u-a$, $\varphi=\arg z$ and $\beta=\arg(u-1)$.

**Theorem.** All zero moduli are strictly greater than $q_*$. Their empirical distribution functions converge uniformly to
$$
 F(q)=
 \begin{cases}
 0 & q\le q_*,\\
 2\varphi(q)/\pi & q>q_* .
 \end{cases}
$$
This distribution is continuous, strictly increasing on $(q_*,\infty)$, and real analytic there. For every fixed $j\ge1$,
$$
 \lim_{n\to\infty} n^2(q_{n,j}-q_*)
 =\frac{2(1-v_*)}{2v_*-1}\pi^2j^2.
$$
For every fixed $l\ge0$, the opposite edge satisfies
$$
 \lim_{m\to\infty}\frac{q_{2m,m-l}}{(2m)^2}
  =\frac8{9\pi^2(l+1/2)^2},
 \qquad
 \lim_{m\to\infty}\frac{q_{2m+1,m-l}}{(2m+1)^2}
  =\frac8{9\pi^2(l+1)^2}.
$$

**Proof.** Set $\Phi=(n+1)\varphi+\beta$. The phase proof locates the $j$th root in the band $|\Phi-(j+1/2)\pi|\le\pi/6$. At a root the uniform relative residue estimate and the mean-value theorem therefore give
$$
 |\Phi(q_{n,j})-(j+1/2)\pi|\le (2/\sqrt3)\theta(q_{n,j})(3/8)^{n+2}.
 \tag{1}
$$
For a fixed $q>q_*$, each band whose upper end is strictly below $\Phi(q)$ has already been crossed completely in traveling to $q$ from $q_*$. Each band whose lower end is strictly above $\Phi(q)$ must still be crossed completely in traveling from $q$ to infinity. In each such crossing the two endpoint signs are opposite, and the crossings can be chosen disjoint in order as in the interlacing proof. Thus the number of roots up to $q$ is bounded below by the number of the former bands and above by $m$ minus the number of the latter bands. These counts differ from $\Phi(q)/\pi$ by a bounded absolute constant, uniformly in $q,n$, since $0<\varphi<\pi/2$ and $\pi/2<\beta<\pi$. Dividing by $m$ proves uniform convergence. All roots are in $(q_*,\infty)$ by the same band count. The limit is nondecreasing, and the implicit function theorem and the strict derivative of the equation for $\theta$ give analyticity on the open interval (also at $v=1/2$). Its endpoint limits are zero and one. An analytic nondecreasing function with these distinct limits is strictly increasing.

For fixed $j$, equation (1) gives $\varphi(q_{n,j})\to0$, hence $q_{n,j}\to q_*$. As $q\downarrow q_*$, the defining equation gives
$$
 \theta^2\sim 2\lambda(q-q_*),\qquad
 \lambda=\frac{(2v_*-1)v_*^2}{1-v_*},\qquad
 \varphi\sim\theta/(2v_*),\qquad \beta\to\pi/2.
$$
Indeed the left side defining $\theta$ is $1-\theta^2/2+O(\theta^4)$, and the derivative of its right side with respect to $q$ at $q_*$ is $-\lambda$. Equation (1) now gives $(n+1)\varphi\to j\pi$, proving the lower-edge limit.

For fixed $l$, take $j=m-l$. Then (1) gives $\varphi(q_{n,m-l})\to\pi/2$, hence $q_{n,m-l}\to\infty$. Here $\theta^2\sim2v$, and $\Re z=2v-\theta^2/3+O(\theta^4)\sim4v/3$. Consequently $\pi/2-\varphi\sim(4/(3\sqrt2))q^{-1/2}$ and $\beta\to\pi/2$. Subtracting (1) from the limiting phase value $(n+2)\pi/2$ gives
$$
 (n+1)(\pi/2-\varphi)\longrightarrow
 \begin{cases}(l+1/2)\pi & n\text{ even},\\(l+1)\pi & n\text{ odd}.\end{cases}
$$
Squaring yields the stated limits. $\square$
