# Simple negative zeros at the square-root transition

Let $L_n$ be the reciprocal of the Eulerian-square row $H_n$ after removing the zero at the origin. For any fixed $0<c<C<\infty$, every zero of $H_n$ with
$$
 c\sqrt n\le \log |x|\le C\sqrt n
$$
is simple and negative for all sufficiently large $n$. The cutoff in $n$ can depend on $c,C$. The argument resolves collisions between the two zero families of the product of Jacobi theta functions. A mixed term in the coefficient expansion splits each collision into two real simple zeros.

## Local expansion of the coefficients

The exact reciprocal row is
$$
 L_n(z)=\sum_{\substack{A,B\ge1\\ A+B\le n+1}}
 e_{n,A-1}\,e_{n+1-A,B-1}\,z^{A+B-2}.
$$
Here $e_{k,j}$ counts permutations of $k$ with $j$ descents. Its [alternating formula](endpoint-asymptotics.md#coefficient-estimates-and-root-localization) and nonnegativity give
$$
 0\le e_{k,j}\le(j+1)^k,\qquad
 0\le 1-\frac{e_{k,j}}{(j+1)^k}
 \le (1+e^{-k/(j+1)})^{k+1}-1.
$$
The last inequality follows by taking absolute values of all terms after the first and using $(1-h/(j+1))^k\le e^{-kh/(j+1)}$ for $1\le h\le j$.

Choose a real $y_0\in[c\sqrt n,C\sqrt n]$. Let $b$ and $a$ be the nearest integers to $n/y_0$ and $n/(y_0+\log b)$, respectively, and let $m=n+1-a$. For large $n$, both $a$ and $b$ are comparable to $\sqrt n$, $m\sim n$, and
$$
 \nu_U=n/a-y_0-\log b=O(1),\qquad
 \nu_V=m/b-y_0=O(1).
$$
The first bound follows from the rounding error for $a$ and $n/a^2=O(1)$. The second follows from the rounding error for $b$ and $a/b=O(1)$. All bounds below are uniform in $y_0$ in the displayed range.

Put $z=-e^{-(y_0+w)}$ and normalize by the nonvanishing monomial term at $(a,b)$ in the coefficient model:
$$
 S(w)=\frac{L_n(z)}{a^n b^m z^{a+b-2}}.
$$
Define two real analytic functions for bounded complex $w$ by
$$
 \begin{aligned}
 U(w)&=\sum_{i\ge 1-a}(-1)^i
 \exp\!\big(n\log(1+i/a)-(y_0+\log b+w)i\big),\\
 V(w)&=\sum_{j\ge 1-b}(-1)^j
 \exp\!\big(m\log(1+j/b)-(y_0+w)j\big).
 \end{aligned}
$$
The series converge locally uniformly on any fixed bounded set for sufficiently large $n$. The model term $A^nB^{n+1-A}z^{A+B-2}$, after normalization and with $A=a+i$, $B=b+j$, is the product of the indicated $i,j$ terms of $U,V$ times $\exp[-i\log(1+j/b)]$. Consequently
$$
 S(w)=U(w)V(w)-b^{-1}U'(w)V'(w)+O(b^{-2})
 \tag{1}
$$
uniformly on any fixed bounded rectangle of complex $w$. Here primes are derivatives with respect to $w$.

To verify the uniform error, first consider the box $a/2\le A\le2a$, $b/2\le B\le2b$. The logarithm of the modulus of the model, as a function of positive real $A,B$, has Hessian
$$
 -\begin{pmatrix} n/A^2 & 1/B\\[2pt] 1/B &(n+1-A)/B^2\end{pmatrix}.
$$
The diagonal magnitudes have fixed positive lower bounds and the off-diagonal magnitude is $O(b^{-1})$, so the Hessian is bounded above by a negative constant times the identity throughout the box. Its gradient at the anchor $(a,b)$ is $(\nu_U-\Re w,\nu_V-\Re w)=O(1)$. Thus the normalized absolute weight is bounded by $\exp(C_1(|i|+|j|)-c_1(i^2+j^2))$. The separate unsigned $U,V$ terms satisfy the same type of bound there by the single-variable second derivatives of their exponents.

Outside the box, bound the model by $A^nB^n|z|^{A+B-2}$ since $B^{1-A}\le1$. Put $t=y_0+\Re w$ and $h=n/t$. Each of the exponents $n\log A-tA$ and $n\log B-tB$ has maximum at $h$. Its difference from that maximum at $T>0$ is $n(\log(T/h)-T/h+1)$. At least one of $A/h,B/h$ lies outside $[3/5,9/5]$ outside the box for large $n$, since $a/h,b/h\to1$. It then loses at least a fixed positive multiple of $n$. At the anchors $a=h+O(\log n)$, $b=h+O(1)$, the independent exponents differ from their maxima by $O((\log n)^2)$. Restoring the actual normalization costs at most the additional $(a-1)\log b=O(\sqrt n\log n)$ in the exponent. Summing over the at most $n^2$ feasible pairs outside the box gives an exponentially small error. For the separate $U,V$ series outside their anchor intervals, concavity gives geometric tails from the endpoints of $[a/2,2a]$ and $[b/2,2b]$, with slopes of magnitude bounded below by a positive constant times $\sqrt n$ directed into the intervals. The bounds at those endpoints are $O(e^{-c_2 n})$. These same estimates bound the tails when terms are multiplied by fixed powers of $i,j$ for derivatives.

In the box, the terms with $|i|+|j|>n^{1/20}$ are smaller in total than any power of $n^{-1}$ by the Gaussian bound. For the remaining terms,
$$
 \exp[-i\log(1+j/b)]
  =1-\frac{ij}{b}
   +O\!\left(\frac{(|i|+i^2)j^2}{b^2}\right).
$$
Both Eulerian numbers in the box have relative model error $O(e^{-c_3\sqrt n})$ by the alternating formula, since the lengths are comparable to $n$ and the descent indices are $O(\sqrt n)$. The Gaussian bounds allow the errors to be summed in absolute value, and replacing the truncated sums by the full separate series has negligible cost. The factor $ij$ gives $U'V'$ because each derivative contributes one minus sign. This proves (1).

## Limits of the separate factors

Let
$$
 \Theta_\lambda(t)=\sum_{j\in\mathbb Z}(-1)^j e^{-\lambda j^2+tj},\qquad
 \lambda_U=\frac{n}{2a^2},\quad \lambda_V=\frac{m}{2b^2}.
$$
Both $\lambda_U,\lambda_V$ lie in a fixed compact subinterval of $(0,\infty)$. Taylor expansion with the preceding Gaussian bounds gives
$$
 U(w)=\Theta_{\lambda_U}(\nu_U-w)+O(b^{-1}),\qquad
 V(w)=\Theta_{\lambda_V}(\nu_V-w)+O(b^{-1}).
 \tag{2}
$$
Indeed, on $|i|\le n^{1/20}$ the cubic remainder in the logarithm of the $U$ weight is $O(|i|^3/b)$ and analogous for $V$. On this truncation the remainders tend uniformly to zero, and the Gaussian bounds sum the errors to $O(b^{-1})$. The tails of both the original and model series are smaller than any fixed power of $n^{-1}$. The same argument holds with derivatives through order two, by weighting the series with the corresponding powers of $i$ or $j$.

For $q=e^{-2\lambda}$ and $p=e^{t-\lambda}$, Jacobi's product gives $\Theta_\lambda(t)=(q,p,q/p;q)_\infty$. The zero set consists of the simple zeros $t=(2j+1)\lambda+2\pi i k$, $j,k\in\mathbb Z$. [Jacobi's triple product](https://dlmf.nist.gov/17.8.E1)

We record the uniform consequences needed below. For either $W=U$ or $V$, let $Z_W$ be its real zeros in $[-1,1]$, and on $|\Re w|\le1/2$, $|\Im w|\le\pi$ write $d_W(w)=\min(1,\operatorname{dist}(w,Z_W))$, taking the distance to the empty set to be $+\infty$. There are constants $d_0,c_0,M>0$ independent of the anchor and $n$ such that for large $n$
$$
 \begin{gathered}
 |W(w)|\ge c_0 d_W(w),\qquad
 |W'(u)|\ge c_0\quad (u\in Z_W),\\
 |u-v|\ge d_0\quad\text{for distinct }u,v\in Z_W,\qquad
 |W^{(j)}(w)|\le M\quad(j=0,1,2)
 \tag{3}
 \end{gathered}
$$
where the derivative upper bounds hold on any fixed rectangle by increasing $M$. To see this, take a small fixed disk radius $\delta<1/8$, also less than one quarter the uniform theta zero spacing. The moduli of the theta derivatives at real zeros in $[-2,2]$ have a positive minimum by compactness of the parameters. The second derivatives are uniformly bounded there. Shrink $\delta$ so the linear term gives a fixed positive lower bound on the disk boundaries. By (2) and Rouché, each disk contains exactly one zero of $W$, simple and real by conjugation. For any real zero of $W$ in $[-1,1]$ there must be a theta zero within such a disk, since compactness gives a uniform positive lower bound for the theta modulus away from its zeros. The same compactness bound applies to all $w$ in the evaluation rectangle outside those disks about theta zeros. Each disk meeting that rectangle has center within $[-1/2-\delta,1/2+\delta]$ and its zero of $W$ belongs to $Z_W$. Inside the disks, uniform lower derivative and upper second derivative bounds give $|W(w)|\ge c_0|w-u|$ about the unique zero $u$, by the Taylor estimate and further shrinking $\delta$ if needed. This proves (3).

## Localization and splitting

Let $z$ be any reciprocal zero in the stated modulus range. Choose $y_0=-\log|z|$ and $w_0$ purely imaginary with $|\Im w_0|\le\pi$ such that $z=-e^{-(y_0+w_0)}$. By (1) and (3), $|U(w_0)V(w_0)|=O(b^{-1})$. Therefore one of the factors has a real zero $u$ with $|w_0-u|\le Kb^{-1/2}$ for a uniform constant $K$. Exchange the factor names for this argument if needed, so $u$ is a zero of $U$.

Fix a sufficiently large constant $R>2K$. If $V$ has no zero in distance $2Rb^{-1/2}$ of $u$, consider the circle of radius $Rb^{-1/2}$ about $u$. Both distances in (3) on the circle are at least $Rb^{-1/2}$ for all large $n$, since the other zeros of $U$ are uniformly separated. Thus $|UV|\ge c_0^2R^2/b$. The error $S-UV$ is $O(b^{-1})$ with a uniform constant independent of $R$, by (1). With $R$ sufficiently large, Rouché gives exactly one zero with multiplicity of $S$ in the disk, where $UV$ has just the single simple zero $u$. The same estimates (3) ensure that $U,V$ have no other complex zeros there. The disk contains $w_0$, and conjugation gives that this zero is real and simple.

Otherwise there is one zero $v$ of $V$ within $2Rb^{-1/2}$ of $u$. Set
$$
 \tau=\tfrac12(u+v),\qquad
 \Delta=\tfrac12\sqrt b\,(u-v),\qquad
 \xi=\sqrt b\,(w-\tau).
$$
Then $\Delta$ is real and $|\Delta|\le R$. For bounded $\xi$, the derivative bounds (3) and the expansion (1) give
$$
 \frac{b\,S(\tau+\xi/\sqrt b)}{U'(u)V'(v)}
   =\xi^2-\Delta^2-1+O_R(b^{-1/2}).
 \tag{4}
$$
The product term gives $(\xi-\Delta)(\xi+\Delta)$ up to the stated error by Taylor expansion at $u,v$. The mixed term gives $-1+O_R(b^{-1/2})$, and the residual in (1) contributes $O(b^{-1})$. The limiting quadratic for this comparison has the two real zeros $\pm\sqrt{1+\Delta^2}$, separated by at least $2$. Use disks of radius $1/4$ about them. The quadratic has a uniform positive lower bound in modulus on both boundaries, so Rouché gives exactly one root with multiplicity in each disk. These roots are simple and real by conjugation. The candidate $w_0$ has $|\sqrt b(w_0-\tau)|\le K+R$, so (4) places it in one of the two disks for large $n$. It is therefore real and simple as well.

In either case $z=-e^{-(y_0+w_0)}$ is negative. The exponential substitution has nonzero derivative, and the normalizing factor is nonzero, so the multiplicity is unchanged. Inversion transfers the result to $H_n$.

## Upper logarithmic extension

For every fixed $c>0$, the conclusion extends to **all** $\log|x|\ge c\sqrt n$. By the [growing extreme-rank theorem](growing-large-roots.md), it suffices to prove (1) and (3) with uniform constants for $c\sqrt n\le y_0\le C\sqrt{n\log n}$, for any fixed $C>0$. We use the same definitions of $S,U,V$ but take $(a,b)$ to maximize the positive coefficient model $A^nB^{n+1-A}e^{-y_0(A+B-2)}$ over feasible integer pairs.

Write $h=n/y_0$ and $\Lambda=y_0^2/n$. Uniformly, $a/h,b/h\to1$. In fact, temporarily dropping $B^{1-A}\le1$ leaves two independent continuous maxima at $h$. Departure by a fixed fraction of $h$ in either coordinate loses a fixed positive multiple of $n$, by the function $\log(T/h)-T/h+1$. Testing the feasible pair with each coordinate nearest to $h$ loses only $O(n/h^2)=O(\log n)$ from rounding and $O(h\log h)=o(n)$ from the mixed factor. Holding each coordinate at its maximizing value, the other coordinate's continuous optimum is $n/(y_0+\log b)$ or $m/y_0$, respectively. Both are strictly inside the feasible intervals. Strict concavity puts the respective integer maximizers at a floor or ceiling, giving $\nu_U,\nu_V=O(\Lambda)$.

In the box $[a/2,2a]\times[b/2,2b]$ the separate unsigned terms at $w=0$ are at most one by anchor maximality. Their exponents have second derivatives at most $-c_6\Lambda$, so consecutive log-weight differences decrease by at least $c_6\Lambda$ at each step away from the anchor. The first step costs a nonpositive log-weight difference. The separate unsigned terms are therefore bounded by $\exp(-c_7\Lambda |i|(|i|-1))$ and $\exp(-c_7\Lambda |j|(|j|-1))$. Bounded $w$ costs at most $\exp(O(|i|+|j|))$, while the cross factor costs at most $\exp(O(|ij|/b))$. Since $\Lambda\ge c^2$ and $b\to\infty$, the uniform Gaussian majorants still apply. The estimates outside the box follow by the same independent-exponent argument as before. At $n/(y_0+\Re w)=(1+o(1))h$ the independent exponents attain their maxima, the loss at $a,b$ is $o(n)$, and the discarded normalization factor costs $O(h\log h)=o(n)$. The separate tails decay geometrically from the interval endpoints, where their weights are $O(e^{-c_8n})$ by $\Lambda a^2,\Lambda b^2\asymp n$. The endpoint derivatives have magnitudes at least a fixed multiple of $y_0$, directed into the intervals. Thus the same truncation and Taylor argument proves (1) with absolute error $O(b^{-2})$ uniformly.

To prove (3), split according to the size of $\Lambda$. For bounded $\Lambda$, the parameters in (2) remain in compact sets with $\lambda_U,\lambda_V$ bounded away from zero. This proves (3) with constants that can depend on the chosen upper bound for $\Lambda$. For large $\Lambda$, only the indices $-1,0,1$ in each factor contribute up to $O(e^{-c_9\Lambda})$, including derivatives through order two on any fixed rectangle by the new separate-term majorants. The unsigned coefficients at $-1,1$ belong to $[0,1]$, and their product is at most $e^{-c_6\Lambda}$ by the second difference at zero. Keep the larger coefficient. The approximating function for each factor is now $1-\alpha e^{w}$ or $1-\alpha e^{-w}$ with $\alpha\in[0,1]$, with error $O(e^{-c_{10}\Lambda})$ up through two derivatives. These functions form a compact family on a fixed rectangle. They have only simple real zeros in $|\Im w|\le\pi$, with derivative modulus one there. The disk and compactness argument used for (3) applies to this family, with constants independent of $\Lambda$, once $\Lambda$ exceeds a fixed threshold. Treat $\Lambda$ below this threshold by (2). This proves (3) on the entire enlarged range.

The localization and splitting argument uses only (1) and (3), so it applies without further changes. Taking $C$ larger than the constant in the growing extreme-rank theorem proves the asserted upper extension. The [lower logarithmic bridge](theta-lower-bridge.md) extends the result to smaller values of $\Lambda$.
