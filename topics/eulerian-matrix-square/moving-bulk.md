# A quantitative count of negative zeros of the Eulerian matrix square

Let $H_n(x)$ be the degree-$n-1$ polynomial obtained by dividing the $n$th row of the ordinary Eulerian matrix square by $x$. We use the notation and pole formulas of the [bulk distribution proof](bulk-asymptotics.md).

**Theorem.** There are absolute constants $c,C>0$ such that, for all sufficiently large $n$, at least $n-Cn^{2/3}$ simple negative zeros of $H_n$ satisfy

$$
|\log(-x)|\le c n^{1/3}.
$$

## The outer pole estimate on a growing interval

Take $N=n+1$, $L=\log N$, $Y=\varepsilon N^{1/3}$, where $\varepsilon\in(0,1]$ will be fixed small enough. For $|y|\le Y$ put

$$
w(y)=\frac{1+e^y}{-y+i\pi},\qquad
R(y)=|w(y)|,\qquad \theta(y)=\arg w(y),\qquad
\delta(y)=\left(\frac{y^2+\pi^2}{y^2+9\pi^2}\right)^{1/2}.
$$

We will estimate the factorial-weighted polynomial $F_n$ at these $w(y)$ and at the positive radii between $\delta(y)R(y)$ and $R(y)$. Write $\lambda=\log(N|w|)$ and $\Delta=\pi-|\arg w|$ for each such argument. Uniformly in these ranges, $\lambda$ is bounded above and below by positive constant multiples of $L+\max(y,0)$, $\lambda\ge (2/3)L-O(1)$, and $\Delta\ge c_0/(1+\max(y,0))$ for an absolute $c_0>0$. These bounds follow from $R(y)=(1+e^y)/\sqrt{y^2+\pi^2}$, $\delta\ge1/3$, and $\theta(y)=-\pi/2-\arctan(y/\pi)$. All constants in the estimates below can be taken independently of $\varepsilon\in(0,1]$.

Use the same $\Phi_w$ and critical point $u_w$ as in the bulk proof. In the notation here the final logarithm in $\Phi_w$ has argument $\lambda+i\arg w+\log u$. The bounds for the first three derivatives, the location $u_w=1+O(1/\lambda)$, and the Gaussian approximation of the integral of $e^{N\Phi_w}$ over $[1/2,2]$ hold with $\lambda$ in place of $L$. The argument comparing $\Phi_w'$ with the derivative at the positive radius $R=|w|$ sharpens to

$$
u_w-u_R=O(|\arg w|/\lambda^2),
$$

since the angular derivative of $\Phi_w'$ is $O(\lambda^{-2}+e^{-\lambda})$, directly from its formula. As in the fixed-interval proof, strong concavity of $\Re\Phi_w$ on $[1/2,2]$ gives

$$
\sup_{1/2\le u\le2}\Re\Phi_w(u)
\le\Re\Phi_w(u_w)+O((\arg w)^2/\lambda^4).
\tag{1}
$$

It also bounds the integral of the modulus by $C N^{-1/2}\exp(N\sup\Re\Phi_w)$, by integrating the real Gaussian bound around the real maximizer. That maximizer is interior since the first derivative at the endpoints has opposite signs. The cost $O(N(\arg w)^2/\lambda^4)$ in the exponential is smaller than $N\Delta/\lambda^2$ by a uniform factor $O(1/L)$, because $(\arg w)^2/(\Delta\lambda^2)\le C(1+\max(y,0))/(L+\max(y,0))^2$.

In the normalized outer integral over $s\in[N/2,2N]$, separate the $m=0$ term of the Eulerian pole sum. The two terms with $|m|=1$ have respective magnitude ratios to the $m=0$ term at most $\exp(-c_1N\Delta/\lambda^2)$. In fact $(\arg w+2\pi m)^2-(\arg w)^2\ge4\pi\Delta$ for them. For $|m|\ge2$, the difference is at least a constant times $m^2$. Their summed magnitude ratio is $O(\lambda e^{-c_2 N/\lambda^2})$, by extracting the exponential factor and summing the reciprocal quadratics as before. In both estimates $\log(|w|s)=\lambda+O(1)$ on the integration interval. Multiply by the Gaussian modulus bound and use (1). The relative error compared with the complex Gaussian main term is then bounded by

$$
C\left(e^{-c_3 N\Delta/\lambda^2}+\lambda e^{-c_4N/\lambda^2}\right)
$$

for absolute positive constants. The second term tends to zero since $\lambda\le C N^{1/3}$. For any fixed $\varepsilon>0$ the first term is bounded by $C\exp(-c_5/\varepsilon^3)$ for all sufficiently large $N$, since $N\Delta/\lambda^2\ge c_6 N/((1+Y)(L+Y)^2)$. This can be made smaller than $1/16$ by choosing $\varepsilon$ sufficiently small.

The tails outside $[N/2,2N]$ still give a uniform relative $o(1)$ error. Here are the bounds with growing $R=|w|$. For $s\le\sqrt N$ use $A_n(Rs)/n!\le\max(1,R\sqrt N)^n=(R\sqrt N)^n$ for large $N$ since $R\ge c_7N^{-1/3}$. After dividing by $(NR)^N$ this is bounded by $C N^{-n/2}$, which is exponentially smaller than $e^{-N}\lambda^{-N}$ even at $\lambda=O(N^{1/3})$. For $s\ge\sqrt N$ and $s=Nu$, the integrand bound of the bulk proof gives a factor $(u e^{1-u}\lambda/(\lambda+\log u))^N$ times $C(1+\lambda+\log u)e^{N(-1-\log\lambda)}$. For $N^{-1/2}\le u\le1/20$, the ratio $\lambda/(\lambda+\log u)$ is at most $5$ for large $N$, since $\lambda\ge (2/3)L-O(1)$. Thus the quantity in parentheses is at most $e^{19/20}/4<1$. For $u\in[1/20,1/2]$ the ratio is $1+O(1/L)$ and $u e^{1-u}\le e^{1/2}/2<1$. For $u\ge2$, the ratio is at most one and $u e^{1-u}\le (2/e)e^{-(u-2)/2}$. These bounds give an exponential loss from the tails, whereas $\Re\Phi_w(u_w)=-1-\log\lambda+O(1/\lambda)$.

It follows, taking $\varepsilon$ small and then $N$ large, that

$$
F_n(w)=n!N(Nw)^N e^{N\Phi_w(u_w)}
\left(\frac{2\pi}{-N\Phi_w''(u_w)}\right)^{1/2}(1+E_n(w)),
\qquad |E_n(w)|\le\frac18.
\tag{2}
$$

The Gaussian evaluation itself has uniform relative $o(1)$ error, since its contour displacement is $O(1/\lambda^2)$ and the real part of the second derivative remains bounded above by a negative constant. The bound in (2) is sufficient to define a continuous phase. It also guarantees comparable magnitudes with the stated main term.

## The inner pole error and the phase range

The absolute error from omitting the inner poles other than the first conjugate pair in $-e^y H_n(-e^y)$ is at most $C(1+Y)R F_n(\delta R)$. Indeed, each remaining pole ratio is at most $\delta$, and the sum of squared ratios is $O(1+|y|)$ by integral comparison with $(y^2+\pi^2)/(y^2+(2m+1)^2\pi^2)$. The inner powers are $k+1\ge2$, giving a factor $\delta^{k-1}$ after extracting the squared ratios, and $\delta\ge1/3$ absorbs the index shift.

To compare the error with the complex leading term, first compare $F_n(\delta R)$ with $F_n(R)$ by varying the positive radius. The derivative with respect to $\log R$ of $\log(NR)+\Phi_R(u_R)$ is

$$
1+\frac{1/(NRu_R)}{1-1/(NRu_R)}-\frac{1}{\lambda+\log u_R}
\ge 1-O(1/L),
$$

using $\Phi_R'(u_R)=0$. Integration and (2) give $F_n(\delta R)/F_n(R)\le C\exp(N(1-O(1/L))\log\delta)$.

At the same radius, the angular penalty from the other leading term satisfies

$$
\Phi_R(u_R)-\Re\Phi_w(u_w)
\le (1/2+o(1))\theta^2/\lambda^2.
\tag{3}
$$

At $u_R$, the change in the first argument-dependent logarithm in $\Phi_w$ improves the real part, since $|1-e^{-i\theta}/(NRu_R)|\ge 1-1/(NRu_R)$. The cost of the last logarithm is $\frac12\log(1+\theta^2/(\lambda+\log u_R)^2)$. Replacing $u_R$ by $u_w$ costs $O(\theta^2/\lambda^4)$ by the saddle displacement and critical point equation, which proves (3). Thus (2) gives

$$
\frac{F_n(\delta R)}{|F_n(w)|}
\le C \exp\left(N\{(1-O(1/L))\log\delta+(1/2+o(1))\theta^2/\lambda^2\}\right).
$$

The exponent in braces is at most $-c_8/(1+y^2)$ uniformly for $|y|\le Y$. For bounded $y$, this follows from $\delta<1$ and $\lambda\to\infty$. For negative large $y$, $|\theta|\le\pi/|y|$, so the angular term is a uniformly vanishing fraction of $-\log\delta\sim 4\pi^2/y^2$. For positive large $y$ we have $\lambda\ge y$ for all sufficiently large $N$ in the stated range, and $|\theta|\le\pi$. The cost is at most $(1/2+o(1))\pi^2/y^2$ and the radial gain is again asymptotic to $4\pi^2/y^2$. Consequently the inner error is uniformly $o(|wF_n(w)|)$, since $(1+Y)e^{-c_8N/(1+Y^2)}\to0$.

We may now count alternating signs using the continuous phase $\Theta_n(y)$ of $w(y)F_n(w(y))$ from (2). As in the fixed-interval proof, it is the sum of $(N+1)\theta(y)$, $N\Im\Phi_w(u_w)$, the Gaussian argument and the argument of $1+E_n(w)$. The last two are uniformly bounded. Directly from the imaginary parts at $u_R$ and the saddle displacement, $\Im\Phi_w(u_w)=O(|\theta|/\lambda)$. At $y=-Y$, $|\theta|=O(1/Y)$, so $\Theta_n(-Y)=O(N/Y)$. At $y=Y$, $\theta=-\pi+O(1/Y)$ and $\lambda\ge Y$, giving $\Theta_n(Y)=-(N+1)\pi+O(N/Y)$. The difference yields at least $N-O(N/Y)$ sign changes at successive phase levels in $\pi\mathbb Z$. They occur at distinct values of $y$ with $|y|\le Y$, and each pair of successive opposite signs forces a negative real zero of $H_n$. Thus there are $n-O(n^{2/3})$ distinct negative zeros in this interval. The excess multiplicity is at most $O(n^{2/3})$ by the degree, giving the same simple-zero count.

## Transition beyond this range

At the left end, meaning $y\to+\infty$, $\arg w$ approaches the negative-axis cut with gap of order $1/y$, and $\lambda$ is of order $y+\log N$. The two closest outer pole terms can therefore have comparable magnitudes once $y$ reaches order $N^{1/3}$. Treating only the first outer pole with a uniformly small relative error does not extend the argument past this transition. Near $|y|$ of order $\sqrt N$, the extra inner poles also become comparable. The [fixed-endpoint theorem](endpoint-asymptotics.md) applies at scales of order $N$ in $|y|$ for fixed root ranks. It leaves these transitions uncontrolled.
