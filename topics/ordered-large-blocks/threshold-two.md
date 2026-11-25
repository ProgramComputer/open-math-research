# Ordered set partitions counted by nonsingleton blocks

Let $O_n(t)=\sum_\pi t^{b(\pi)}$, where $\pi$ runs over ordered set partitions of $[n]$ and $b(\pi)$ is the number of blocks of size at least two. This is $O_{n,2}$ in Alexandersson's ordered large-block conjecture. Its constant term is $n!$, its degree is $\lfloor n/2\rfloor$, and its leading coefficient is positive. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

**Theorem.** For every $n\ge0$, all zeros of $O_n$ are simple and negative. For $m=\lfloor n/2\rfloor\ge1$, write them as $-q_{n,1},\ldots,-q_{n,m}$ with $0<q_{n,1}<\cdots<q_{n,m}$. Then

$$
0<q_{n+1,1}<q_{n,1}<q_{n+1,2}<q_{n,2}<\cdots<q_{n+1,m}<q_{n,m},
$$

and if $n$ is odd, the extra modulus $q_{n+1,m+1}$ is strictly larger than $q_{n,m}$. The initial constant rows have the vacuous interlacing property.

## Poles of the generating function

The ordered sequence construction gives

$$
\sum_{n\ge0}O_n(t)\frac{z^n}{n!}=\frac1{1-z-t(e^z-1-z)}.
$$

At $t=-q$ with $q>0$, put $v=1/(1+q)$ and $a=1-2v$. The denominator is

$$
D_q(z)=(1+q)\big((1-v)e^z-z-a\big).
$$

With $u=z+a$, its zeros satisfy

$$
e^u=p u,\qquad p=\frac{e^{1-2v}}{1-v}.
\tag{1}
$$

The function $\log p=1-2v-\log(1-v)$ decreases from $1$ to $\log 2$ on $0<v\le1/2$ and then increases to infinity as $v\to1$. Let $v_*$ be its unique solution of $\log p=1$ in $(1/2,1)$ and put $q_*=1/v_*-1$. We use $q>q_*$, so that $0<v<v_*$ and $2\le p<e$. In this range there are no real solutions of (1). A nonpositive $u$ cannot occur, and $e^u/u\ge e$ for positive real $u$.

For a solution $u=s+i\theta$ in the upper half-plane, imaginary and real parts of (1) give $\sin\theta>0$, $s=\theta\cot\theta$, and

$$
f(\theta):=\theta\cot\theta-\log\left(\frac\theta{\sin\theta}\right)=\log p.
\tag{2}
$$

On each interval $(2\pi k,(2k+1)\pi)$, $k\ge0$,

$$
f'(\theta)=-\theta-\frac{(\theta\cot\theta-1)^2}{\theta}<0.
$$

The limits of $f$ at the left and right endpoints are $1,-\infty$ when $k=0$, and $+\infty,-\infty$ when $k\ge1$. Thus there is exactly one upper pole $z_k=u_k-a$ per interval, together with its conjugate. Each is simple since $D'_q(z_k)=(1+q)(u_k-1)$ and $u_k$ is nonreal. We call $z=z_0$ the principal upper pole and write $u=u_0$, $\theta=\Im z$.

Integrating $f'\le-\theta$ gives $f(\theta)\le 1-\theta^2/2$. Since $\log 2>1/2$, it follows that $0<\theta<1$. Also $1-\theta^2/2\le\theta\cot\theta\le1$, using $\sin\theta\le\theta$, $\cos\theta\ge1-\theta^2/2>0$ and $\tan\theta\ge\theta$. Consequently $|u-1|\le(\sqrt5/2)\theta$. Equation (2) yields

$$
0<\Re z=\log\left(\frac{\theta/\sin\theta}{1-v}\right)
=\theta\cot\theta-1+2v\le2v<2.
$$

In particular, $|z|<\sqrt5$, whereas $|z_k|,|u_k-1|>2\pi k$ for $k\ge1$. Put

$$
\varphi(q)=\arg z\in(0,\pi/2),\qquad \beta(q)=\arg(u-1)\in(\pi/2,\pi).
$$

Both are continuous for $q>q_*$. At $q\downarrow q_*$ we have $\theta\to0$, $\Re z\to2v_*>0$, so $(\varphi,\beta)\to(0,\pi/2)$. At $q\to\infty$ we again have $\theta\to0$, and

$$
f(\theta)=1-\theta^2/2+O(\theta^4),\qquad
\log p=1-v+O(v^2),
$$

so $\theta^2\sim2v$. Since $\Re z\le2v$, this gives $(\varphi,\beta)\to(\pi/2,\pi/2)$.

## A uniform relative residue estimate

For $N=n+1$, the coefficient is given exactly by

$$
\frac{O_n(-q)}{n!}=-\frac2{1+q}\Re\sum_{k\ge0}\frac1{(u_k-1)z_k^{N}}.
\tag{3}
$$

To derive (3), integrate $1/(z^N D_q(z))$ on squares whose sides have real or imaginary part $\pm 2\pi M$. On a horizontal side, $e^z$ is real, so $|D_q(z)|\ge(1+q)2\pi M$. On the right vertical side the exponential term dominates the linear term for large $M$, and on the left the linear term dominates. Thus the integrals tend to zero as $M\to\infty$. The pole at zero records the coefficient, and the remaining residues are absolutely summable by the bound $|u_k-1|,|z_k|>2\pi k$. Pairing their conjugates proves (3).

Define the positive normalizer $M_n(q)=2/((1+q)|u-1||z|^N)$ and the real phase $\Phi_n(q)=N\varphi(q)+\beta(q)$. Equation (3) gives

$$
\frac{O_n(-q)}{n!M_n(q)}=-\cos\Phi_n(q)+E_n(q),
\qquad |E_n(q)|\le\theta\,(3/8)^{N+1}.
\tag{4}
$$

Indeed, divide the other terms of (3) by $M_n(q)$ and use $\sqrt5<9/4$, $2\pi>6$, and $\sum_{k\ge1} k^{-N-1}\le2$ to bound their total relative magnitude by

$$
\sum_{k\ge1}\frac{(9/8)\theta}{2\pi k}
 \left(\frac{9/4}{2\pi k}\right)^N
\le\theta\,(3/8)^{N+1}.
$$

The relative error vanishes with $\theta$ at either endpoint. This is needed for a consecutive-row comparison when the principal phase shift is small.

## Counting the roots and comparing consecutive rows

For $n\ge2$, the phase $\Phi_n$ starts at $\pi/2$ and tends to $(n+2)\pi/2$. For $j=1,\ldots,m=\lfloor n/2\rfloor$, both levels

$$
(j+1/2)\pi-\pi/6,\qquad (j+1/2)\pi+\pi/6
$$

are strictly inside this endpoint range, and the bands they bound are disjoint and ordered. Choose a compact $q$ interval on which the starting phase is below all the bands and the final phase is above them. For each band take the first hit of its upper level and the last hit of its lower level before that upper hit. These give ordered disjoint intervals in $q$, and the phase stays within the indicated band on each interval. Their two endpoints have opposite signs in (4), since $|\cos\Phi_n|=1/2$ there and $|E_n|<1/2$. Thus each interval has a negative root of $O_n$ under $x=-q$. There are $m$ intervals, which exhaust the degree. In particular every root is simple, and at $q=q_{n,j}$ the phase belongs to the $j$th band. This argument uses only continuity of the phase.

At $q=q_{n,j}$ we have $|\cos\Phi_n|\le |E_n|$ by (4), and $\sin\Phi_n$ has sign $(-1)^j$ and modulus at least $\sqrt3/2$ by the band. The next row uses $\Phi_{n+1}=\Phi_n+\varphi$. Its normalized value at $q$ is therefore

$$
\sin\Phi_n\sin\varphi-\cos\Phi_n\cos\varphi+E_{n+1}.
$$

The final two terms in absolute value are at most $\theta(3/8)^{N+1}(1+3/8)$, whereas $\sin\varphi=\theta/|z|>4\theta/9$. For $N\ge3$,

$$
\frac94 (3/8)^{N+1}(1+3/8)<\frac14.
$$

Thus the main sine product dominates and $O_{n+1}(-q_{n,j})$ has sign $(-1)^j$. Its value at $q=0$ is positive, so it has one root before the first $q_{n,j}$ and one between each pair of successive $q_{n,j}$. If its degree is $m+1$, its leading sign as $q\to\infty$ gives a further root after $q_{n,m}$. These roots exhaust its degree and prove the required strict order. The constant cases $n=0,1$ follow directly.

## Reproducing the checks

Let $H(z,t)$ be the row exponential generating function. Its derivatives satisfy $(1-z)H_z=(2+(t-1)z)t H_t+(1+t z)H$, by substitution of the denominator and differentiation. Hence

$$
O_{n+1}=(n+1)O_n+2tO'_n+nt\big(O_{n-1}+(t-1)O'_{n-1}\big),\qquad n\ge1.
$$

The [checker](code/threshold_two_check.py) compares this recurrence with the independent first-block recurrence through $n=104$. It also verifies the rational interlacing margin and uses Arb interval arithmetic to compare the exact coefficients and principal residues at 24 pairs of rational $q$ and integer $n$. These are reproducible algebra and numerical checks alongside the uniform proof. Run from the repository root with `python-flint` installed:

~~~sh
python -I -O topics/ordered-large-blocks/code/threshold_two_check.py
~~~

## Scope and prior work

The proof treats the ordered threshold $j=2$ and applies for unbounded $n$ without finite checks. The ordinary unordered threshold $j=2$ and the restricted family that orders only the large blocks have different generating functions and have prior results. For example, at $n=3$ the present polynomial is $6+7t$, whereas ordering only the nonsingleton blocks gives $1+4t$. The original ordered conjecture and the public investigation #108 were checked on 25 November 2026. Targeted web and Firecrawl searches for ordered partitions counted by nonsingleton blocks, including “Lambert W,” “real-rooted,” “Fubini” and “interlacing,” did not locate a prior proof for this exact ordered threshold. A related published theorem of Bóna and Mező treats ordinary partitions with all blocks of size at least two. [Author's status page](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Public investigation #108](https://github.com/1337isnot1337/solved-conjectures/issues/108) · [Related restricted cases](https://www.symmetricfunctions.com/realRootedSetPartitions.htm#bigBlockSetPartitions) · [Bóna–Mező](https://arxiv.org/abs/0705.2734)
