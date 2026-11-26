# Explicit small-parameter signs at $nt\ge40$

Use the notation $S,\Lambda,\Psi_n,C_n,R_\pm,\Omega,Q$ from [the three-angle saddle estimates](central.md). For $0<t\le1/5$ and $T=nt\ge40$,
$$
\left|C_nP_n(-t^4)-\cos\Psi_n\right|<\frac12.
$$
This supplies the phase signs down to $t=40/n$. The proof uses separate radial bounds on the three-angle integral and the exact angular averages of its quartic and squared cubic errors.

## Damping on the angular domain

Throughout this range $\Re\Lambda\ge(5/4)t$, $|\Lambda|\le 2t/(1+t)$, and $1+2\sqrt2t\le |S|$, with the last two bounds from the explicit expressions. For the first, multiply by $|S|^2/t$. The difference is
$$
\sqrt2-\frac54+(8-5\sqrt2)t+
(14\sqrt2-20)t^2+(24-30\sqrt2)t^3-45t^4>0.
$$
For example $7/5<\sqrt2<17/12$ and $t\le1/5$ bound it below by $3/20+(11/12-59/50)t>0$.

In the plus cube, the bounds $|R_+/S|\le e^{-a Q}$ hold with $a$ equal to each of
$$
\frac{37}{40}t\quad(Q\le1/4),\qquad
\frac34t\quad(Q\le1/2),\qquad
\frac5{12}t\quad(Q\le1).
$$
To check them, for a general $Q\le u\le1$ the four brackets in the exact squared-modulus gap are at least $Q$ times
$$
\begin{aligned}
d_1(u)&=\frac12-\frac{u}{8}-\frac{\sqrt u}{3\sqrt3},&
d_2(u)&=1-\frac{2u}{3},\\
d_3(u)&=1-\frac u3+(3/2-u)d_1(u),&
d_4(u)&=(3-u)(1-u/3).
\end{aligned}
$$
These follow from the elementary angular bounds in the companion note. For $u=1/4,1/2,1$, they are entrywise at least $37/50,3/5,1/3$ times the vector of leading coefficients $(1/2,1,7/4,3)$. The damping rates follow from the explicit $\Re\Lambda$ and its lower bound above.

There is stronger global damping in $\Omega$ available at small $t$. It starts with
$$
1-C-D\ \ge\ \frac{4}{3\pi^2}Q .
$$
Put $w=\sqrt{Q/3}$. By concavity of $\log\cos\sqrt x$ and $\log\sin\sqrt x$ on the coordinate-square interval, Jensen's inequality gives $C\le\cos^3w$ and $|D|\le\sin^3w$. The former concavity follows because $\tan u/u$ is increasing, and the latter by composition of increasing concave $\log\sin u$ with $\sqrt x$. The endpoint cases follow by continuity. If $w\le\pi/4$, put $p=\cos w\sin w$. For $L=\cos^3w+\sin^3w$ one has $1-L^2=p^2(3-2p)\ge2p^2$ and $L\le1$. Thus $1-L\ge p^2\ge4w^2/\pi^2$.

For $w\ge\pi/4$, the definition of $\Omega$ gives $|D|\le(1/2)^{3/2}$ and $Q\le3\pi^2/8$, the latter from $\sin^2 p_i\ge4p_i^2/\pi^2$. The function
$$
1-(1/2)^{3/2}-\cos^3 w-\frac{4w^2}{\pi^2}
$$
is concave on $[\pi/4,\pi/\sqrt8]$ by its second derivative. Its first endpoint is $3/4-1/\sqrt2>0$, and its last endpoint is greater than $1/2-1/(2\sqrt2)-1/8>0$, since $\pi/\sqrt8>\pi/3$. This proves the global angular bound.

Combine that bound with the other three global brackets from the companion note. The damping rate is at least
$$
\frac{8\sqrt2t/3+16t^2+16\sqrt2t^3+48t^4}{\pi^2|S|^2}>\frac{t}{4}.
$$
For the strict inequality, use $\pi^2<10$ and subtract $(5/2)|S|^2$ from the numerator after division by $t$. The difference is
$$
8\sqrt2/3-5/2+(16-10\sqrt2)t+
(16\sqrt2-40)t^2+(48-60\sqrt2)t^3-90t^4>0.
$$
Using $7/5<\sqrt2<17/12$ and $t\le1/5$, a lower bound is $37/30-(88/5)/25-37/125-90/625>0$.

In the minus cube, the first exact gap bracket alone is at least $1-1/(2\sqrt2)$ since its signed $C\le0$ and $|D|\le(1/2)^{3/2}$. Hence the squared gap exceeds $(4\sqrt2-2)t>|S|^2t$, where $|S|^2\le16/5$ in the range under consideration. This yields $|R_-/S|^n\le e^{-T/2}$.

## Integrated error

As in the companion note, write $R_+(p)/S=J+K$, $R_+(-p)/S=J-K$. Use the fourth-order bound
$$
0\le C-1+Q/2\le
\sum_i\frac{p_i^4}{24}+\sum_{i<j}\frac{p_i^2p_j^2}{4},
$$
and the bound $0\le Q-\sum_i\sin^2p_i\le\sum_i p_i^4/3$. Also $|K|^2\le(16t^2/|S|^2)p_1^2p_2^2p_3^2$. The following are the spherical averages of the three polynomials, on any radius:
$$
\mathbb E_\mathrm{ang}\sum_i p_i^4=\frac35 Q^2,\qquad
\mathbb E_\mathrm{ang}\sum_{i<j}p_i^2p_j^2=\frac15 Q^2,\qquad
\mathbb E_\mathrm{ang}p_1^2p_2^2p_3^2=\frac1{105}Q^3.
$$
These identities follow from the independent one-dimensional Gaussian even moments after separating the radial integral. This gives
$$
\begin{aligned}
\mathbb E_\mathrm{ang}|J-e^{-\Lambda Q}|
&\le \left(\frac{(3/10)t+(4/5)t^2}{|S|}
+\frac{|\Lambda|^2}{2}\right)Q^2
\le\frac{26}{45}tQ^2,\\
\mathbb E_\mathrm{ang}|K|^2&\le\frac{16}{105}t^2 Q^3.
\end{aligned}
$$
For the first bound, divide its parenthesis by $t$, use $|S|\ge1+2\sqrt2t$ and $|\Lambda|\le2t/(1+t)$, and note $3/10+2t/(1+t)^2\le26/45$ for $t\le1/5$. The bound on $K$ uses $|S|\ge1$.

Write $G_m(x)=\Gamma(m+1/2,x)/\Gamma(m+1/2)$ for the normalized Gaussian tail, and let $F_*=(100/99)^5$. On a radial subregion with $Q\ge q_0$ and $|R_+/S|\le e^{-\alpha t Q}$, the normalized integrated error from the two local terms is bounded by
$$
\mathcal L(T,\alpha,q_0)=
\frac{F_*}{T}(2/\alpha)^{3/2}
\left[
\frac{15}{4}\frac{26}{45\alpha^2}
G_3\!\left(\frac{99}{100}\alpha Tq_0\right)
+\frac1{\alpha^3}
G_4\!\left(\frac{99}{100}\alpha Tq_0\right)
\right].
$$
Indeed the Taylor error after the odd term cancels is bounded by $\binom n2|K|^2 e^{-(n-2)\alpha tQ}$, and telescoping the powers of $J$ and $e^{-\Lambda Q}$ adds $n|J-e^{-\Lambda Q}|e^{-(n-1)\alpha tQ}$. The formula follows by integrating $Q^2,Q^3$ and dividing by the magnitude $(\pi/(n|\Lambda|))^{3/2}$ of the leading Gaussian integral. Here $n\ge200$, so $(n-2)/n\ge99/100$, and both prefactor losses are bounded by $F_*$. The exponential Gaussian itself is bounded by the same damping since $\Re\Lambda\ge (5/4)t$.

Use $\mathcal L(T,37/40,0)$ on $Q\le1/4$, and $\mathcal L(T,3/4,1/4)$ on $1/4<Q\le1/2$, enlarging the integral for each bound. The remaining actual plus tails on $1/2<Q\le1$ and $Q>1$ contribute at most
$$
(24/5)^{3/2}G_1(5T/24)+8^{3/2}G_1(T/4).
$$
The entire comparison Gaussian tail on $Q>1/2$ adds at most $(8/5)^{3/2}G_1(5T/8)$. The minus cube has volume at most $\pi^3$, so its relative contribution is at most $(2\pi T)^{3/2}e^{-T/2}$. The sum is decreasing for $T\ge40$, since the normalized Gaussian tails decrease and $T^{3/2}e^{-T/2}$ decreases for $T>3$.

At $T=40$, this sum is less than $2/5$. The [rational enclosure](code/small_constants.py) bounds fractional powers by integer square roots, uses $\pi<22/7$, and evaluates elementary exponential and Gaussian tail bounds with exact rational arithmetic. It uses the recurrence
$$
G_m(x)\le\frac{e^{-x}}{\sqrt\pi}
\left(\frac1{\sqrt x}
+\sum_{j=1}^m\frac{x^{j-1/2}}{(1/2)_j}\right),\qquad x>0,
$$
which follows by integration by parts and the Gaussian integral upper bound at the base exponent. The phase estimate follows by taking the real part of the two conjugate saddle contributions as before.
