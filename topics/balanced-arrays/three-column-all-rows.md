# Three balanced columns of row cap two

**Theorem.** For every integer $n\geq 0$, let
$$
P_n(q)=\sum_k [x_1^k x_2^k x_3^k](1+e_1(x_1,x_2,x_3)+e_2(x_1,x_2,x_3))^n\,q^k.
$$
Then $P_n$ has $\lfloor 2n/3\rfloor$ distinct negative zeros. This is the $U(2,3)$ case of Alexandersson's balanced-array conjecture. The proof establishes the same conclusion after one binomial normalization. It uses exact inequalities for $n\geq20$ and exact Sturm counts for $0\leq n\leq19$. Refs #2. [Original conjecture](https://github.com/PerAlexandersson/RealRooted/issues/2005)

## 1. Normalized generating function

Write $a_{n,k}=[q^k]P_n$, $g_{n,k}=a_{n,k}/\binom nk$ for $0\le k\le n$, and $G_n(q)=\sum_k g_{n,k}q^k$. Fixing the third column to a particular $k$-subset and excluding rows containing three ones by inclusion-exclusion gives
$$
g_{n,k}=\sum_{j=0}^k(-1)^j\binom kj\binom{n-j}{k-j}^2.
\tag{1}
$$
The degree of both polynomials is $D_n=\lfloor2n/3\rfloor$. The bound follows by counting ones. For $n>0$ and $3k\leq2n$, list the $3k$ positions $0,1,\ldots,3k-1$ modulo $n$ and give successive groups of $k$ to the three columns. Each column has distinct row labels, and each row occurs at most twice.

The normalization and the algebraic generating function below come from the repository's earlier three-column reduction. For completeness, put $u=n-k$ in (1) and sum the binomial transform to obtain
$$
\sum_{k\ge0}g_{u+k,k}t^k
 =\frac1{1+t}\sum_{\ell\ge0}\binom{u+\ell}{u}^2
   \left(\frac{t}{1+t}\right)^\ell
 =(1+t)^u L_u(1+2t),
$$
where $L_u$ is the Legendre polynomial. The last step uses the Euler transformation
$\sum_{\ell\ge0}\binom{u+\ell}{u}^2z^\ell=(1-z)^{-2u-1}\sum_i\binom ui^2z^i$
and $\sum_i\binom ui^2z^i=(1-z)^uL_u((1+z)/(1-z))$. Set $t=xq$, multiply by $x^u$, and sum over $u$ by the Legendre generating function. This gives
$$
\sum_{n\ge0}G_n(q)x^n=D(x,q)^{-1/2},\qquad
D(x,q)=1-2x+(1-6q)x^2+(2q-4q^2)x^3+q^2x^4.
\tag{2}
$$
The branch equals $1$ at $x=0$. [Euler transformation](https://dlmf.nist.gov/15.8.E1) · [Legendre coefficient formula](https://dlmf.nist.gov/18.5.E8) · [Legendre generating function](https://dlmf.nist.gov/18.12.E11)

## 2. Reciprocal branch points and their phase

Throughout the proof let $q=-a<0$. The factorization
$$
D(s^2,q)=\big((1+s)^2+qs^3(s+2)\big)\big((1-s)^2+qs^3(s-2)\big)
$$
shows that $\lambda=(v-1)^2/4$ is a reciprocal branch point whenever
$(v^2-1)^2-16av=0$. Indeed take $s=2/(v-1)$ in the first factor. For each $a>0$ there is a unique $t\in(0,1)$ such that
$$
a=\frac{(t+t^{-1})(t^{-2}-t^2)}{16},\qquad
S=t+t^{-1}.
$$
Both factors in the numerator are positive and strictly decreasing on $(0,1)$, and their product decreases from $+\infty$ to $0$. For this $t$ the polynomial in $v$ factors as
$$
(v^2-Sv+t^2)(v^2+Sv+t^{-2}).
$$
The first quadratic has distinct positive roots $r<1<R$, since it is negative at $1$, positive at $0$, and positive for large positive $v$. The second has a nonreal conjugate pair $w,\bar w$, since $4t^{-2}-S^2=t^{-2}(1-t^2)(3+t^2)>0$. Take $w$ in the lower half-plane. Define
$$
\lambda_1=(R-1)^2/4,\quad \lambda_2=(1-r)^2/4,\quad
\lambda_+=(w-1)^2/4=\rho e^{i\phi},\quad
\lambda_-=\bar\lambda_+,\qquad \tau=\lambda_1/\rho,\quad \sigma=\lambda_2/\rho.
$$
Here $\rho=(1+S+t^{-2})/4>1$ because $\Re w=-S/2$ and $|w|^2=t^{-2}$. We have $\lambda_1>\lambda_2>0$ since $R+r=S>2$. Also
$$
4(\rho-\lambda_1-\lambda_2)=t^2+3S-3>0,\qquad 0<\sigma<1/4.
\tag{3}
$$
For the first identity, use $R^2+r^2=S^2-2t^2$ and $S^2=t^2+t^{-2}+2$. For the second inequality, $\lambda_2<1/4$. The argument of $\lambda_+$ is $2\arctan(|\Im w|/(1-\Re w))$. More explicitly, with $m=(1-t)/(1+t)$,
$$
\tan^2(\phi/2)=\frac{(1-t)(3+t^2)}{(1+t)^3}=m+m^2+m^3,\qquad
\rho=\frac{1+m^2}{(1+m)(1-m)^2}.
\tag{4}
$$
In particular $\phi$ increases strictly from $0$ to $2\pi/3$ as $a$ increases from $0$ to $+\infty$. These four reciprocal branch points are distinct, so
$D(x,-a)=\prod_{\nu\in\{+,-,1,2\}}(1-\lambda_\nu x)$.
The following two facts about the ratios will be useful:
$$
\tau+\sigma=\frac2{\rho}-2\cos\phi
  =\frac{2m(1-m+m^2+m^3)}{(1+m)(1+m^2)}\leq 2m,
\qquad
\lim_{\phi\to 2\pi/3}(\tau,\sigma)=(1,0).
\tag{5}
$$
The sum formula uses the coefficient of $x$ in (2). At the upper endpoint $t\to0$, one has $tr\to0$, $tR=1+t^2-tr\to1$, and $4t^2\rho\to1$, proving the ratio limit.

Use principal square roots in the amplitude
$$
A=\prod_{\nu\ne+}(1-\lambda_\nu/\lambda_+)^{-1/2}.
$$
Set
$$
\eta=\tfrac12\big(\arg(1-\tau e^{-i\phi})+\arg(1-\sigma e^{-i\phi})\big),
\qquad
\Psi_n(\phi)=(n+\tfrac12)\phi-\tfrac{\pi}{4}-\eta.
\tag{6}
$$
The two arguments in $\eta$ are positive and less than $\pi/2$ by (3). Also $1-e^{-2i\phi}=2\sin\phi\,e^{i(\pi/2-\phi)}$. Thus $e^{in\phi}A=|A|e^{i\Psi_n(\phi)}$. The continuous extension to the closed phase interval has values
$$
\Psi_n(0)=-\pi/4,\qquad \Psi_n(2\pi/3)=2n\pi/3.
\tag{7}
$$
For the first limit, (5) gives $\tau,\sigma\to0$. For the second, (5) gives $\eta\to\arg(1-e^{-2\pi i/3})/2=\pi/12$.

## 3. Sign at phase nodes with $\pi/6\leq\phi<2\pi/3$

For integers $j\geq0$ let $c_j=\binom{2j}{j}/4^j$. The beta integral gives
$$
\pi c_n=\int_0^1 u^{n-1/2}(1-u)^{-1/2}\,du.
$$
For real $u\in(0,1]$ let
$$
A_+(u)=\prod_{\nu\ne+}\left(1-\frac{\lambda_\nu}{u\lambda_+}\right)^{-1/2}.
$$
The real branch point contribution will use $A_1(u)$, defined by replacing $+$ with $1$ in this formula for $\kappa<u\leq1$, where $\kappa=\sigma/\tau$. All factors use principal square roots. The Cauchy coefficient formula deformed to the cuts gives

$$
G_n(-a)=
  2\\,\mathrm{Re}\\,\frac{\lambda_+^n}{\pi}
       \int_0^1\frac{u^{n-1/2}}{\sqrt{1-u}} A_+(u)\\,du
 +\frac{\lambda_1^n}{\pi}
       \int_\kappa^1\frac{u^{n-1/2}}{\sqrt{1-u}} A_1(u)\\,du .
\tag{8}
$$

To see the deformation, define the analytic germ in (2) by the product of the four principal reciprocal square roots. For the conjugate pair use rays $x=y/\lambda_\pm$, $y\geq1$. For the positive real branch points the ray jumps of the two square roots cancel beyond $x=1/\lambda_2$, leaving the interval $[1/\lambda_1,1/\lambda_2]$. On the upper side of a cut in the oriented variable $y=\lambda_\nu x$, the singular factor $(1-y)^{-1/2}$ has value $i(y-1)^{-1/2}$, and the lower value is its negative. The upper side is integrated with $y$ increasing. On the real interval the other factors yield $A_1(1/y)>0$. The small endpoint arcs vanish by the integrable square-root singularities. On the large outer circle, the generating function is $O(|x|^{-2})$ for fixed $a>0$, so its contribution vanishes. Substituting $u=1/y$ in the jumps gives (8).

For the nonreal integral, a factor $(1-z/u)^{-1/2}$ with fixed $z\ne0$ has logarithmic derivative of absolute value at most $|z|/(2u|u-z|)$. This ratio is at most $1/(2u)$ when $\Re z\leq0$ and at most $1/(2u|\sin\arg z|)$ otherwise. For the two real-root factors of $A_+(u)$ the angle of $z$ is $-\phi$, giving a bound $1/u$ for each. For the conjugate factor the angle is $-2\phi$. Where its real part is positive, the angle bound gives $|\sin(2\phi)|\geq\sqrt3/2$, so the derivative bound is $1/(\sqrt3 u)$ in all cases. Thus
$$
\left|\frac{A_+'(u)}{A_+(u)}\right|<\frac3u,\qquad
\frac{|A_+(u)-A|}{|A|}\leq u^{-3}-1.
\tag{9}
$$
Indeed the first bound gives $|A_+(u)|\leq |A|u^{-3}$, and integrating the resulting bound on $|A_+'|$ gives the second. Dividing by $c_n|\lambda_+|^n|A|$, the error when replacing the first integral with $c_n \lambda_+^n A$, before taking $`2\,\mathrm{Re}`$, is at most
$$
\frac{n(n-1)(n-2)}{(n-\frac12)(n-\frac32)(n-\frac52)}-1<\frac1{10},
\qquad n\geq20.
\tag{10}
$$
This is the beta moment of $u^{-3}-1$. Each of the three factors of the first term decreases in $n$, and at $n=20$ their product is $54720/50505<11/10$.

The real contribution is positive and admits a uniform upper bound even when $\tau$ approaches $1$. Its integrand satisfies
$$
A_1(u)=\frac{\tau u}{|1-\tau u e^{-i\phi}|}\sqrt{\frac{u}{u-\kappa}}
 \leq \frac{\tau}{|1-\tau e^{-i\phi}|}\sqrt{\frac{u}{u-\kappa}}.
$$
For the inequality, $ |1-\tau u e^{-i\phi}|^2-u^2|1-\tau e^{-i\phi}|^2
=(1-u)(1+u-2\tau u\cos\phi)\geq0$. The coefficient in front of the square root, divided by $|A|$, equals
$$
\tau \sqrt{\frac{2\sin\phi\,|1-\sigma e^{-i\phi}|}{|1-\tau e^{-i\phi}|}}
 \ \leq\ \sqrt{5/2}.
\tag{11}
$$
Here $|1-\tau e^{-i\phi}|\geq\sin\phi$, $|1-\sigma e^{-i\phi}|\leq1+\sigma<5/4$, and $\tau<1$. Set $u=\kappa+(1-\kappa)v$ in the remaining integral. With $V$ distributed on $(0,1)$ with density $1/(\pi\sqrt{v(1-v)})$, the real contribution divided by $\rho^n |A|$ is at most
$$
\sqrt{5/2}\,\mathbb E[(\sigma+(\tau-\sigma)V)^n]
  \ \leq\ \sqrt{5/2}\,(c_n+2^{-n}).
\tag{12}
$$
For $v\geq1/2$, the linear expression is at most $v$ because $\tau+\sigma<1$. For $v\leq1/2$, it is at most $1/2$ by the same inequality and $\tau>\sigma$. Finally $\mathbb E[V^n]=c_n$.

The elementary bounds $1/(2\sqrt j)\leq c_j\leq1/\sqrt{j+1}$ for $j\geq1$ follow by induction from the quotient $c_{j+1}/c_j=(2j+1)/(2j+2)$. For $n\geq20$ they give $2^{-n}/c_n\leq 2n\,2^{-n}<1/1000$. Therefore, in units of $\rho^n|A|c_n$, the difference between $G_n(-a)$ and its leading oscillation $2\rho^n|A|c_n\cos\Psi_n(\phi)$ is less than
$$
\frac15+\frac85(1+1/1000)<2.
$$
In particular $G_n(-a)$ has sign $(-1)^k$ wherever $\Psi_n(\phi)=k\pi$ in this phase range.

## 4. Sign at phase nodes with $0<\phi\leq\pi/6$

In this interval, (4) gives $m\leq\tan^2(\pi/12)=7-4\sqrt3<1/12$. By (5), $\tau,\sigma<1/6$. The generating function (2) and the Legendre generating function give the exact convolution
$$
\frac{G_n(-a)}{\rho^n}=\sum_{\ell=0}^n h_\ell L_{n-\ell}(\cos\phi),\qquad
\sum_{\ell\geq0}h_\ell z^\ell=(1-\tau z)^{-1/2}(1-\sigma z)^{-1/2}.
\tag{13}
$$
Here $h_0=1$ and $0\leq h_\ell\leq6^{-\ell}$, by bounding the two nonnegative binomial series coefficientwise by $(1-z/6)^{-1/2}$. Each argument in (6) is at most $\arctan((1/6)/(1-1/6))<1/5$, so $0<\eta<1/5$. At a node $\Psi_n(\phi)=k\pi$ with $k\geq1$, we have
$$
(n+\tfrac12)\phi=k\pi+\pi/4+\eta\ \geq\ 5\pi/4.
\tag{14}
$$

For $N\geq1$ set $y_N(\theta)=\sqrt{\sin\theta}\, L_N(\cos\theta)$. The Legendre differential equation gives
$$
y_N''+\left((N+\tfrac12)^2+\frac1{4\sin^2\theta}\right)y_N=0.
$$
At $\theta=\pi/2$ the value and derivative agree with those of
$b_N\cos((N+\tfrac12)\theta-\pi/4)$, where
$$
b_N=\begin{cases}
 c_{N/2},&N\text{ even},\\
 \dfrac{N}{N+1/2}\,c_{(N-1)/2},&N\text{ odd}.
\end{cases}
$$
Indeed the Legendre generating function at $0$ gives $L_{2j}(0)=(-1)^jc_j$, and its derivative gives $L'_{2j+1}(0)=(-1)^j(2j+1)c_j$. Variation of constants for the free equation $y''+(N+\tfrac12)^2y=0$ gives a Volterra integral with kernel bounded in absolute value by $1/(N+\tfrac12)$. Integrating backward from $\pi/2$ and applying Grönwall's inequality gives
$$
\left|\frac{y_N(\phi)}{b_N}-
       \cos((N+\tfrac12)\phi-\pi/4)\right|
 \ \leq\ \exp\left(\frac{\cot\phi}{4(N+1/2)}\right)-1.
\tag{15}
$$
Explicitly, $|y_N(\theta)|/b_N\leq1+\int_\theta^{\pi/2} f(s)|y_N(s)|/b_N\,ds$ with $f(s)=1/(4(N+\tfrac12)\sin^2s)$. Inserting the bound $\exp(\int_\theta^{\pi/2}f)$ into the same integral for the difference gives (15). [Legendre differential equation](https://dlmf.nist.gov/18.8)

For $N\geq n/2$, by (14) and $\cot\phi\leq1/\phi$ the exponent in (15) is at most $2/(5\pi)$. Its exponential is less than $7/6$, using $\pi>3$ and $e^{2/15}\leq(1-2/15)^{-1}=15/13$. The leading term $\ell=0$ in (13), multiplied by $\sqrt{\sin\phi}$ and divided by $b_n$, therefore has sign $(-1)^k$ and magnitude greater than $49/50-1/6$, since the free cosine equals $(-1)^k\cos\eta$ and $\cos\eta\geq1-\eta^2/2>49/50$.

For $n\geq20$, the binomial bounds from Section 3 give $b_n\geq 2/(3\sqrt n)$. For odd $n$, use $n/(n+1/2)\geq40/41$ and $c_{(n-1)/2}\geq1/\sqrt{2(n-1)}$. For $N\geq n/2$, they also give $b_N\leq2/\sqrt n$. Thus, in the same units, the sum of absolute values of terms $1\leq\ell\leq n/2$ is at most $3(7/6)\sum_{\ell\geq1}6^{-\ell}=7/10$. For $\ell>n/2$, the bound $|L_N(\cos\phi)|\leq1$ for all $N\geq0$ follows from the Laplace integral of $(\cos\phi+i\sin\phi\cos u)^N$ against $du/\pi$ on $[0,\pi]$. This part has total at most
$$
(3/2)\sqrt n\sum_{\ell>n/2}6^{-\ell}
 \leq (9/5)n\,6^{-n/2}<1/100 .
$$
The last bound holds at $n=20$ and decreases thereafter. Together the two error bounds are smaller than $49/50-1/6$. Hence $G_n(-a)$ again has sign $(-1)^k$ at every node $\Psi_n(\phi)=k\pi$, $k\geq1$, in the stated phase range. [Laplace integral at integer degree](https://dlmf.nist.gov/18.10.E5)

## 5. Root count and transfer

For $n\geq20$, select nodes in increasing $\phi$ order, one for each $k\geq1$ with $k<2n/3$. This uses continuity and the limits (7). After any selected node for $k$, the intermediate value theorem gives a strictly later node for $k+1<2n/3$. Section 2 identifies increasing $\phi$ with increasing $a$. The signs of $G_n(-a)$ at these nodes alternate. The initial sign is positive at $a=0$. If $3\nmid n$, the last node is $k=D_n$, and this produces $D_n$ distinct negative roots. If $3\mid n$, the last node is $k=D_n-1$. The degree and its positive leading coefficient give the additional sign $(-1)^{D_n}$ at sufficiently large $a$, again producing $D_n$ distinct negative roots. The degree bound makes all the roots simple.

For $0\leq n\leq19$ the [standalone rational Sturm check](code/verify_three_column_prefix.py) constructs the polynomials by (1) and gives exactly $D_n$ distinct roots in $(-\infty,0)$ in each row. It independently reconstructs all coefficients from a binary row transfer and verifies the same root counts for $P_n$. The archived signatures include both versions of each polynomial, the degrees of the Sturm remainders, and all endpoint signs. [Exact prefix records](results/three_column_prefix.jsonl)

Run from the repository root with standard Python.
~~~sh
python3 topics/balanced-arrays/code/verify_three_column_prefix.py
~~~

Finally multiplication of coefficient $k$ by $\binom nk$ preserves real-rootedness on polynomials of degree at most $n$. Indeed, its homogeneous symbol is $w^nJ_n(z/w)$, where
$$
J_n(q)=\sum_{k=0}^n\binom nk^2q^k=(1-q)^n L_n\big((1+q)/(1-q)\big).
$$
The Legendre zeros lie in $(-1,1)$, so $J_n$ factors into linear factors with strictly negative zeros, and the homogeneous symbol is a product of real stable linear forms. Apply the finite-degree real stability-preserver theorem. Thus $P_n=T(G_n)$ is real-rooted and has strictly negative zeros because its coefficients are nonnegative and its constant coefficient is $1$. To see simplicity, restrict $T$ to real polynomials of degree at most $D_n$, where the diagonal map is invertible. A neighborhood of the simple-rooted $G_n$ consists of real-rooted polynomials, as witnessed by sign changes in disjoint intervals about its roots. Therefore a neighborhood of $P_n$ consists of real-rooted polynomials. If $P_n$ had a repeated real factor $(q-\xi)^2$, replacing this factor by $(q-\xi)^2+\varepsilon$ for small $\varepsilon>0$ would contradict that neighborhood property. [Borcea–Brändén, Theorem 2(b)](https://annals.math.princeton.edu/2009/170-1/p14) · [Legendre zero location](https://dlmf.nist.gov/18.16)

## Independent review

An agent-assisted reviewer reconstructed the four reciprocal roots and the endpoint phase, checked the cut orientations and the absolute bounds for both cut integrals, and verified the Legendre normalization, the sign margins, the degree count in each residue class, and the transfer of simplicity. The reviewer also replayed the standalone prefix verifier byte for byte and made a separate exact check for $0\leq n\leq20$, including the first row of the uniform sign proof. Their independent coefficient formula was
$$
a_{n,k}=\sum_{j=0}^{\lfloor n/2\rfloor}
\binom n{2j}\binom{2j}{j}
\binom{n-2j}{k-j}\binom{n-k+j}{k},
$$
with out-of-range binomial coefficients zero. To obtain it, set $B=1+x_3$, write $x_1=\sqrt u\,w$, $x_2=\sqrt u/w$, and take the constant term in $w$ of $(B+u+B\sqrt u(w+w^{-1}))^n$. In the term with $2j$ occurrences of $w+w^{-1}$, taking $u^k$ leaves the power $B^{n-k+j}$. The reviewer used this formula and exact division by $\binom nk$ to construct the two polynomials, then separate primitive rational Sturm chains to count their distinct negative roots.

The proof covers all row counts in shape $U(2,3)$. Consecutive-row interlacing and the unrestricted balanced-array conjecture remain outside its scope. The cited exact computation uses rational arithmetic. Lean checks the root count from the phase and sign hypotheses in Section 5. [Exact formal scope and build instructions](lean/README.md#three-columns-with-row-cap-two)
