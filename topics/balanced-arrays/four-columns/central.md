# The torus integral and its quadratic approximation

For the degree-$\lfloor n/2\rfloor$ polynomial $P_n$ defined in the [main proof](proof.md), use $t>0$, $\zeta=e^{i\pi/4}$ and the principal arguments. Set
$$
S=1+4\zeta t+6it^2,\quad \Lambda=(2\zeta t+4it^2)/S,\quad
\Psi_n=n\arg S-\tfrac32\arg\Lambda,\quad C_n=(\pi n|\Lambda|)^{3/2}/|S|^n.
$$
Write $\rho=t/(1+t)$ and $\sigma=t/(1+t)^2$. We derive the integrated majorants used in the [compact interval calculation](proof.md#the-compact-interval). They also imply $|C_n P_n(-t^4)-\cos\Psi_n|<1/2$ whenever $n\rho\ge450$ and $n\sigma\ge70$.

## The three-angle integral

Put $y_j=\zeta e^{i(\pm p_1\pm p_2\pm p_3)}$, taking the four sign triples with sign product $+1$. Their product is $-1$. The integer linear map from the three angles to the arguments of the first three $y_j/\zeta$ is surjective on the torus because its determinant is nonzero, so normalized Haar measure is pushed forward to normalized Haar measure. Constant-term extraction gives
$$
P_n(-t^4)=\int (1+t e_1(\mathbf y)+t^2 e_2(\mathbf y))^n\,d\mathbf y .
$$
Write $C=\prod_i\cos p_i$, $D=\prod_i\sin p_i$, $U=\sum_i\cos^2p_i$, and $A=U-3/2$. Direct expansion of the six pairs and four singletons gives
$$
R=1+2\sqrt2t(C+D)+i\big(2\sqrt2t(C-D)+4t^2A\big).
$$
On $U\ge3/2$, divide the torus into cubes centered at the eight choices of integer multiples of $\pi$. After recentering, the common domain is
$$
\Omega=\{p\in[-\pi/2,\pi/2]^3: U\ge3/2\}.
$$
Four cubes preserve both $C,D$ and four negate both. Write $R_+,R_-$ for those integrands on $\Omega$. The reflection $p_i\mapsto\pi/2-p_i$ interchanges the two sectors $U\ge3/2$ and $U\le3/2$, and maps $R$ to its conjugate, since it swaps $C,D$ and negates $A$. Thus
$$
P_n(-t^4)=\frac{1}{\pi^3}\Re\int_\Omega (R_+^n+R_-^n)\,dp.
$$
The same reduction applies to an amplitude $W=(R-\Re S)/\Im S$ since the transformation conjugates it.

## Global damping

With $C,D$ interpreted as the signed products in each cube, the squared-modulus gap is exactly
$$
\begin{aligned}
|S|^2-|R|^2={}&4\sqrt2t(1-C-D)+16t^2(1-C^2-D^2)\\
&+16\sqrt2t^3(3/2-A(C-D))+16t^4U(3-U).
\end{aligned}
$$
All four contributions are nonnegative. In fact put $h=U/3$. By AM–GM, $|C|\le h^{3/2}$ and $|D|\le(1-h)^{3/2}$. The inequality $\sqrt h\le(1+h)/2$, applied at $h$ and $1-h$, gives $|C|+|D|\le1-h(1-h)$. Also $C^2+D^2\le h^3+(1-h)^3=1-3h(1-h)$. Finally $3/2-A(C-D)\ge3/2-|A|=\min(U,3-U)\ge U(3-U)/3$. Therefore the gap is at least $B(t) U(3-U)$ for
$$
B(t)=4\sqrt2t/9+16t^2/3+16\sqrt2t^3/3+16t^4.
$$
Put $Q=|p|^2$. On $\Omega$, $U\ge3/2$ and $3-U=\sum\sin^2p_i\ge4Q/\pi^2$. It follows that
$$
|R_\pm/S|\le e^{-aQ},
\qquad a=\frac{3B(t)}{\pi^2|S|^2}>\frac{2}{15}\rho .
$$
For the last inequality, $|S|^2=1+4\sqrt2t+16t^2+24\sqrt2t^3+36t^4$ and coefficient comparison shows $(1+t)B(t)\ge(4/9)t|S|^2$. Use $\pi^2<10$. The bound on $|R_\pm/S|$ uses $\sqrt{1-x}\le e^{-x/2}$ for $0\le x\le1$.

In the minus cube $C\le0$ and $|D|\le(1/2)^{3/2}<1/2$. Thus $1-C-D\ge1/2$ and $3/2-A(C-D)\ge3/4$, so the gap also exceeds $2\sqrt2t+12\sqrt2t^3$. Divide this by $|S|^2$ and compare coefficients after multiplication by $(1+t)^2$ to obtain a second lower bound $b=(\sqrt2/3)\sigma$ for the relative squared gap. Averaging the two lower bounds gives
$$
|R_-/S|\le e^{-aQ/2-b/4}.
$$

## Local damping and the Gaussian error

Work in the ball $Q\le1/4$, which lies within $\Omega$. Here only $R_+$ is considered, with $C\ge0$. We have
$$
0\le C-1+\tfrac12Q\le Q^2/8,\qquad
0\le Q-\sum\sin^2p_i\le Q^2/3,\qquad |D|\le(Q/3)^{3/2}.
$$
The cosine estimate follows by expanding $\prod_i(1-(1-\cos p_i))$, using $0\le1-\cos p_i\le p_i^2/2$ and its fourth-order Taylor bound. The sine-square estimate follows from the fourth-order Taylor bound for $\cos(2p_i)$. The last bound is AM–GM.

The four brackets in the exact gap, in order, are bounded below by $Q$ times
$$
d_1=\frac12-\frac1{32}-\frac1{6\sqrt3},\quad
d_2=\frac56,\quad
d_3=\frac{11}{12}+\frac54d_1,\quad
d_4=\frac{121}{48}.
$$
For the second bracket, with $u_i=\sin^2p_i$, use $1-C^2-D^2=\sum_i u_i-\sum_{i<j}u_i u_j$ and $\sum_{i<j}u_i u_j\le Q^2/3$. The third is $(3-U)+A(1-C+D)$ with $A\ge5/4$, and the fourth is $(3-\sum u_i)\sum u_i$. These constants are each at least $37/50$ times the respective leading coefficients $1/2,1,7/4,3$. Consequently $|R_+/S|\le e^{-a_0Q}$ in the ball with $a_0=(37/50)\Re\Lambda$. Indeed
$$
\Re\Lambda=\frac{\sqrt2t+8t^2+14\sqrt2t^3+24t^4}{|S|^2},
\quad
\Im\Lambda=\frac{\sqrt2t+4t^2+2\sqrt2t^3}{|S|^2}.
$$
Coefficient comparisons give $\Re\Lambda\ge(2/3)\rho$, $|\Lambda|\le2\rho$, and $|\Lambda|\le1$. The displayed real and imaginary parts give $|\Lambda|/\Re\Lambda\le\sqrt2$. In particular
$$
a_0\ge(37/75)\rho>(49/100)\rho,\qquad |\Lambda|/a_0<2,\qquad |\Lambda|/a<15.
$$
The small-$Q$ limit of the global modulus bound also gives $\Re\Lambda\ge a$.

Write $R_+(p)/S=J+K$ and $R_+(-p)/S=J-K$. Here $K$ contains just the odd sine product. Define
$$
B_0=\frac{t/2+4t^2/3}{|S|}+\frac{|\Lambda|^2}{2},\qquad
K_0=\frac{4t}{3\sqrt3|S|}.
$$
Then $|K|\le K_0Q^{3/2}$ and $|J-e^{-\Lambda Q}|\le B_0 Q^2$. For the second inequality, compare both expressions to $1-\Lambda Q$ using the cosine and sine-square bounds and the integral exponential remainder with $\Re\Lambda>0$. Also $B_0\le(7/8)|\Lambda|$ and $K_0^2\le(4/27)|\Lambda|^2$. The former follows from $t/2+4t^2/3\le (3/8)|2\zeta t+4it^2|$, checked by squaring and comparing coefficients, and $|\Lambda|\le1$. The latter follows from $2t\le |2\zeta t+4it^2|$.

By Taylor's formula along the segments from $J$ to $J\pm K$, the average of their $n$th powers differs from $J^n$ by at most
$$
\binom n2 K_0^2 Q^3e^{-(n-2)a_0Q}.
$$
Indeed the linear terms cancel, and all points of the segments are convex combinations of $J+K,J-K$, so their moduli are bounded by $e^{-a_0Q}$. Telescoping the power difference between $J$ and $e^{-\Lambda Q}$ adds at most $nB_0 Q^2e^{-(n-1)a_0Q}$. Since the ball is symmetric, this bounds the local integral error. The integral of the comparison Gaussian on all of $\mathbb R^3$ is $(\pi/(n\Lambda))^{3/2}$ with the branch in the right half-plane. Divide the error by its magnitude, using
$$
\int_{\mathbb R^3} Q^j e^{-hQ}\,dp
=\pi^{3/2}(3/2)_j h^{-3/2-j}.
$$
For $n\ge450$, both factors $(n/(n-1))^{7/2}$ and $(n/(n-2))^{9/2}$ are less than $21/20$. The normalized error on the ball is bounded by
$$
\frac{21}{20}\frac{(|\Lambda|/a_0)^{3/2}}{n a_0}
\left(\frac{15}{4}\frac{B_0}{a_0}+\frac{105}{16}\frac{K_0^2}{a_0^2}\right)
<\frac{33}{n a_0}.
$$

For $Q>1/4$, use $e^{-naQ}\le e^{-na/8}e^{-naQ/2}$. The tails of both $R_+^n$ and the comparison Gaussian contribute at most
$$
2(2|\Lambda|/a)^{3/2}e^{-na/8}<330e^{-n\rho/60}.
$$
In the negative-sign cube integrate the global minus bound to get at most $(2|\Lambda|/a)^{3/2}e^{-nb/4}<165e^{-\sqrt2n\sigma/12}$. All errors are relative to the same Gaussian magnitude. Under $n\rho\ge450,n\sigma\ge70$ the sum is strictly below $1/2$. For instance, $33/(n a_0)<.150$, $330e^{-n\rho/60}<.195$, and $165e^{-\sqrt2n\sigma/12}<.060$, using $\sqrt2>7/5$. Multiplying the Gaussian by $S^n$ and taking its real part gives the stated phase estimate.
