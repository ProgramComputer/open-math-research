# Absolute root counts at moving circles on the large-modulus side

Let $P_n(x)=xH_n(x)$ be the shifted Eulerian-square row polynomial, of degree $n$, and put $N=n+1$, $L=\log N$. The following counts resolve the range where the two nearest outer poles are comparable but all farther poles are still negligible. The count includes the zero at the origin. [Eulerian pole formula and factorial integral](bulk-asymptotics.md)

**Theorem.** There is a constant $a>0$ such that, on the interval

$$
N^{1/4}\le y\le a\sqrt{N/\log N},
\tag{1}
$$

one can define a real phase $\Xi_n(y)$ with $\Xi_n'(y)=(2\pi+o(1))N/y^2$ uniformly. At every cross-section $\Xi_n(y)=k\pi$, the circle $|x|=e^y$ contains no zero of $P_n$ and encloses exactly $k$ zeros with multiplicity. Thus every zero between two consecutive such circles is simple and negative. In particular, for sufficiently large $n$ every zero with log modulus between $(3/2)N^{1/4}$ and $(a/2)\sqrt{N/\log N}$ is simple and negative.

## The four terms on an upper semicircle

For $|x|=e^y$ in the upper half-plane write $x=-e^\xi$, $\xi=y-it$, $0\le t\le\pi$. Define

$$
w_\sigma=-\frac{1+e^\xi}{\xi+i\sigma\pi},\qquad
\tau_{\sigma\eta}=\log(1+e^\xi)-\log(\xi+i\sigma\pi)+i\eta\pi,
\qquad \sigma,\eta\in\{+1,-1\}.
$$

Here $\log(1+e^\xi)=\xi+\log(1+e^{-\xi})$ and the other logarithms of $\xi+i\sigma\pi$ are principal. Then $e^{\tau_{\sigma\eta}}=w_\sigma$. Set

$$
G_N(\omega)=\int_{1/2}^{2}e^{-Nu}u^N(\omega+\log u)^{-N}\,du,\qquad
W_{\sigma\eta}=n!N^{N+1}w_\sigma^{N+1}G_N(L+\tau_{\sigma\eta}).
\tag{2}
$$

On the upper semicircle, $R=|w_+|\asymp e^y/y$, $|w_-|\le R$, and the two logarithmic radii differ by $O(y^{-2})$. Write $\lambda=\log(NR)\sim y$ uniformly in (1). The real parts of the four arguments of $G_N$ are $\lambda+O(y^{-2})$, and their imaginary parts are bounded. The phase of the principal term is taken continuously from the positive point of the semicircle, where $W_{++}$ is positive. Define $\Xi_n(y)$ to be this phase at $t=0$. In particular its formula is the imaginary part of $(N+1)\tau_{++}(y)+\log G_N(L+\tau_{++}(y))$, with the analytic logarithm of $G_N$ specified below.

The saddle estimate for $G_N$ gives, with $J_N=\log G_N$,

$$
J_N(\omega)=c_N-N\log\omega+R_N(\omega),\qquad
R_N^{(j)}(\omega)=O(N/y^{2+j}),\quad 0\le j\le3,
\tag{3}
$$

where $c_N=-N+\frac12\log(2\pi/N)$ is real. The branches are real on the positive real line. To justify (3), use the saddle argument for the factorial integral with phase $-u+\log u-\log(\omega+\log u)$. On a disk of radius a small fixed multiple of $y$ about an argument with real part $\sim y$, the critical point is $1+O(y^{-1})$, the critical value is $-1-\log\omega+O(y^{-2})$, and the second derivative there is $-1+O(y^{-1})$. The error $O(y^{-2})$ in the critical value uses $\log u-u=-1+O((u-1)^2)$ and $\log u=O(y^{-1})$ at the critical point. A horizontal contour through the critical point gives the Gaussian main term with relative $O(N^{-1/5})$ error, uniformly on a slightly smaller disk. The endpoint connectors are exponentially small because $\Re(\log u-u)$ has a strict gap away from $u=1$ on the original segment. This gives the analytic logarithm from the saddle formula and $R_N=O(N/y^2)$ there. Cauchy's estimates on smaller disks give the derivative bounds. For bounded $\Im\omega$, comparison with the real saddle also shows

$$
\int_{1/2}^2\left|e^{-Nu}u^N(\omega+\log u)^{-N}\right|du\le C|G_N(\omega)|.
\tag{4}
$$

Indeed the displacement from the corresponding real saddle is $O(y^{-2})$, and the best real modulus exponent costs at most $O(N/y^4)=O(1)$ relative to the complex saddle exponent. This follows from Taylor expansion at the critical point and strict concavity of the real modulus exponent, as in the [factorial saddle proof](bulk-asymptotics.md#uniform-estimates-for-the-factorial-weighted-row). The real and complex Gaussian factors have comparable moduli.

We claim the uniform residual bound

$$
\frac{P_n(x)}{W_{++}}=1+\frac{W_{--}}{W_{++}}+\frac{W_{+-}}{W_{++}}+\frac{W_{-+}}{W_{++}}
+O(e^{-y/2}+e^{-cN/y^2})
\tag{5}
$$

on the semicircle, for some $c>0$ and a sufficiently small absolute $a$. The details of the residual bound follow.

First keep the two inner poles $w_+,w_-$ in the exact Eulerian pole sum. The remainder is bounded by summing the omitted ratios to $R$. If $\phi=\pi-t\in[0,\pi]$, each omitted inner denominator has imaginary part $\phi+2\pi m$ with $m\ne0,-1$. The gap of its squared imaginary part over $\phi^2$ is at least $4\pi^2$. The squared ratios have sum $O(y)$ by comparison with $y^2/(y^2+c m^2)$. For $k\ge3n/4$, extract the $N/2$th power of the largest omitted ratio and bound the sum of the remaining powers by the squared sum. This bounds the omitted sum of $(k+1)$st powers relative to $R^{k+1}$ by

$$
Cy\left(1+\frac{4\pi^2}{y^2+\pi^2}\right)^{-N/4}
\le Cy\exp(-(\pi^2+o(1))N/y^2).
$$

For $k<3n/4$, use the squared-ratio sum and $\sum_{k<3n/4} A(n,k)k!R^k\le n!(nR)^{3n/4}$. By (2)–(3) this is exponentially small compared with $|W_{++}|/R$, even after multiplying by $y$. The large-$k$ bound multiplies $R F_n(R)$, and the positive-radius saddle gives

$$
R F_n(R)/|W_{++}|\le C\exp((\pi^2/2+o(1))N/y^2).
$$

For this last inequality, the positive-radius principal term is $n!N^{N+1}R^{N+1}G_N(\lambda)$ up to a bounded relative factor. Its other poles have a fixed squared angular gap. The cost of changing $\lambda$ to $L+\tau_{++}$ in $G_N$ is at most $(\pi^2/2+o(1))N/y^2$, by the logarithm in (3) and the reality of $R_N$ on the positive real line. In particular the first-order variation of $R_N$ in the imaginary direction is purely imaginary. These estimates give an inner residual $O(e^{-cN/y^2})$ for small $a$, absorbing the factor $y$ because $N/y^2\ge a^{-2}\log N$.

For each of the two retained $w_\sigma$, use the outer Eulerian pole sum inside $F_n(w_\sigma)=\int_0^\infty e^{-s}A_n(w_\sigma s)\,ds$. For $s=Nu$, $1/2\le u\le2$, retain the two logarithmic branches $\tau_{\sigma,+},\tau_{\sigma,-}$. On the semicircle $\Im\tau_{++}=\phi-\arctan(\phi/y)+O(e^{-y})$, and its exact branch lies between $0$ and $\pi$. The other upper branch $\Im\tau_{-+}$ lies between $0$ and $\pi+O(1/y)$. In fact it equals $\phi+\arctan((2\pi-\phi)/y)+O(e^{-y})$ and is positive for all $\phi\in[0,\pi]$. Every omitted outer branch has absolute imaginary part at least $2\pi-O(e^{-y})$. Its squared gap over the principal denominator remains at least a positive constant, since the two real logarithmic parts differ by only $O(y^{-2})$. For branches with large index the squared gap is at least a constant times the squared index. Extracting the smallest gap factor and summing reciprocal quadratics bounds the normalized sum by $Cy e^{-cN/y^2}$. The factor $|w_-|^{N+1}/|w_+|^{N+1}\le1$ helps this comparison, and (4) transfers it to the complex principal integral. On each retained branch, replacing $(Nw_\sigma u-1)^N$ by $(Nw_\sigma u)^N$ has relative pointwise error $O(1/R)$. Equation (4) transfers this bound after integration. The four retained magnitudes are bounded by a constant times $|W_{++}|$, as also follows from (7) below. This gives the $O(e^{-y/2})$ term.

The tails of the two outer integrals outside $s\in[N/2,2N]$ are exponentially small relative to the principal term. One may bound $|A_n(w_\sigma s)|$ by $A_n(Rs)$. For $s\le N^{1/4}$ the elementary bound $A_n(Rs)\le n!\max(1,Rs)^n$ after normalization by $n!(NR)^N$ gives $O(N^{-3n/4})$, exponentially small compared to $e^{-N}\lambda^{-N}$. For $s\ge N^{1/4}$ and $u=s/N$, the positive-radius pole estimate gives the outside-interval factor $(u e^{1-u}\lambda/(\lambda+\log u))^N$ times $O(1+\lambda+\log u)e^{N(-1-\log\lambda)}$. On $N^{-3/4}\le u\le1/2$ the logarithmic ratio is $1+o(1)$ since $y\ge N^{1/4}$, and $u e^{1-u}\le e^{1/2}/2$. On $u\ge2$ the ratio is at most one and $u e^{1-u}\le (2/e)e^{-(u-2)/2}$. The angular penalty to compare with $|W_{++}|$ is at most $\exp(O(N/y^2))$, so the integrated tails are negligible. This also proves the positive-radius estimate used for the inner omitted poles. All these bounds establish (5).

## Winding at a phase level

For brevity put

$$
A=W_{--}/W_{++},\qquad B=W_{+-}/W_{++},\qquad C=W_{-+}/W_{++},\qquad g=N/y^3.
$$

In the arguments of $J_N$, let $\omega=L+\tau_{++}$ and $d=\log(\xi+i\pi)-\log(\xi-i\pi)$. The four arguments are $\omega,\omega-2\pi i,\omega+d,\omega+d-2\pi i$. Also $w_-/w_+=e^d$. This gives the exact identity

$$
A=BCe^{\mathcal K},\qquad
\mathcal K=J_N(\omega+d-2\pi i)-J_N(\omega-2\pi i)-J_N(\omega+d)+J_N(\omega).
\tag{6}
$$

Uniformly along the semicircle,

$$
\Re\mathcal K=(4\pi^2+o(1))g,\qquad
|\partial_t\mathcal K|=O(g/y),\qquad
\partial_t\log|B|=-(2\pi+o(1))N/y^2,\quad
\partial_t\log|C|=-(2\pi+o(1))N/y^2.
\tag{7}
$$

Indeed, $d=2\pi i/y+O(y^{-2})$, $d'=-2\pi i/(\xi^2+\pi^2)$, $\omega'=1+O(y^{-1})$, with primes in $\xi$. The mixed difference $\mathcal K$ equals $-2\pi i d$ times the average of $J_N''$ over the two straight shifts. In (3), $J_N''=N/\omega^2+O(N/y^4)$ and $J_N'''=O(N/y^3)$, proving the first two estimates. The derivative of $\log B$ in $\xi$ is $(J_N'(\omega-2\pi i)-J_N'(\omega))\omega'=-(2\pi i+o(1))N/y^2$. The derivative of $\log C$ is $(N+1)d'$ plus $O(N/y^3)$ from the $J_N$ difference. Multiplication by $-i$ and taking real parts gives the estimates in $t$. Likewise, differentiating

$$
\log A=(N+1)d+J_N(\omega+d-2\pi i)-J_N(\omega)
$$

twice in $\xi$ gives $O(g)$, by $d''=O(y^{-3})$, $\omega''=O(y^{-2})$, and the $J_N$ derivative bounds. At $t=0$, by conjugation $W_{--}=\overline{W_{++}}$ and $W_{-+}=\overline{W_{+-}}$. Thus $|A|=1$ and $|B|=|C|=\exp(-\Re\mathcal K/2)$ there. In particular both $|B|,|C|$ start below one and decay. Equation (6) shows $|A|\le\exp(-ctN/y^2)$, using (7).

Suppose $\Xi_n(y)=k\pi$. Then $A=1$ at $t=0$. The first derivative of $\log A$ in $\xi$ at that point is purely imaginary by conjugation on the real interval. Its contribution along $\xi=y-it$ is real, so the continuous argument of $A$ starting at zero satisfies $|\arg A|\le Cgt^2$. We claim that

$$
\Re(1+A+B+C)\ge c_0\min(1,g)
\tag{8}
$$

for a positive absolute constant. If $g$ exceeds a sufficiently large fixed $G$, then $|B|+|C|\le1/4$. Either $|A|\le1/4$ or $t=O(y^2/N)$ by its decay. In the latter case $|\arg A|=O(y/N)=o(1)$, so $\Re A\ge0$. Both cases give a positive constant bound.

If $g\le G$, then for $t$ greater than a fixed small $t_0>0$ all three ratios are $o(1)$ by (7) and $N/y^2\to\infty$. For $0\le t\le t_0$, choose $t_0$ small enough depending on $G$ that $e^{\Re\mathcal K}\cos(\arg A)\ge1+c_1g$ uniformly. This follows from $|\arg A|\le Cgt^2$ and $\Re\mathcal K\ge c_2 g$. With $b=|B|$, $c=|C|$ and (6),

$$
\Re(1+A+B+C)\ge (1-b)(1-c)+c_1g b c.
$$

If $b,c\le1/2$ the first term is at least $1/4$. If either exceeds $1/2$, the derivative and initial value estimates in (7) give $tN/y^2=O(1)$ and bound the other below by a positive constant, since $g\le G$. This proves (8). All constants are independent of $a$ once it is chosen sufficiently small.

The residual in (5) is $o(\min(1,g))$ in (1): $g\ge a^{-3} (\log N)^{3/2}/\sqrt N$, and choosing $a$ small makes the power bound $e^{-cN/y^2}$ smaller than $N^{-2}$. Consequently $P_n/W_{++}$ has positive real part on the entire upper semicircle. At its positive endpoint both $P_n$ and $W_{++}$ are positive real. At its negative endpoint both are real and their ratio is positive. The continuous argument of $P_n$ along this arc therefore starts at $0$ and ends at $k\pi$, since the ratio contributes zero at both endpoints. Reflection in the real axis gives a total winding of $k$ on the full circle, which is zero-free. By the argument principle the disk contains exactly $k$ roots with multiplicity.

Finally, at $t=0$, $\Im\tau_{++}=\pi-\arctan(\pi/y)$ and $\partial_y\tau_{++}=1-1/(y+i\pi)+O(e^{-y})$. With (3) these give $\partial_y\Xi_n=(2\pi+o(1))N/y^2$. Successive phase levels give annuli containing exactly one root counted with multiplicity. Conjugation and positivity on the positive real axis make that root simple and negative. The spacing in $y$ is $O(y^2/N)$, proving the stated interior range.

The absolute counts here concern the two-outer-pole range. Their upper boundary is a small fixed multiple of $\sqrt{N/\log N}$, where the error from farther poles is still smaller than the principal coupling of order $N/y^3$. For simplicity beyond this range, the [lower logarithmic theta bridge](theta-lower-bridge.md) starts at any prescribed positive multiple of $\sqrt{n/\log n}$. The two bounds overlap when this prescribed multiple is less than $a/2$. The estimates here do not specify an effective cutoff in $n$.
