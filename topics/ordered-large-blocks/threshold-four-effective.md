# Real-rootedness and strict interlacing at ordered threshold four

Let $O_{n,4}(t)$ count ordered partitions of $[n]$, weighted by $t$ for every block of size at least four. Every $O_{n,4}$ has only simple negative zeros, and adjacent rows strictly interlace, with the first root in increasing absolute value always belonging to the later row. The proof gives real-rootedness directly for $n\ge119$ and interlacing with row $n+1$ for $n\ge199$. An exact finite check supplies the remaining rows and pairs. [Alexandersson's ordered conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

## A certified strip bound

Use the notation and the pole classification of the [eventual proof](threshold-four-eventual.md#separation-of-the-four-low-poles). In particular $0<v<v_*<1/12$, the right pair is $z,\bar z$, the left pair is $w,\bar w$, and $\rho=|w|<2$ and $r=|z|/\rho\le e^{-\rho/36}$.

All four low poles in fact satisfy $|\Im z|<4/3$. It is enough to exclude zeros on $z=x+(4/3)i$ for $-2\le x\le2$ and $0\le v\le1/12$, because the four low poles already satisfy $|z|<2$ there and tend to zero as $v\to0$. Conjugation excludes the lower line. For $y=4/3$, the necessary imaginary-part equation is

$$
v=1-\frac{y(1+x+x^2/2-y^2/6)}{e^x\sin y}.
$$

Substituting this expression in the real part gives

$$
F(x)=(1-v)e^x\cos y-\left(1+x+(x^2-y^2)/2+(x^3-3xy^2)/6\right)+2v.
$$

The [checker](code/threshold_four_effective.py) covers $[-2,2]$ by dyadic intervals, evaluating these two expressions in Arb with certified rounding. Each of the 51 resulting intervals has either $v$ strictly outside $[0,1/12]$ or $F$ strictly away from zero. Thus no relevant zero can cross the line. The checker also verifies $\cos(4/3)>1/5$ and $-\log\cos(4/3)<8/5$.

## An effective error for the principal pair

Let $g$ be the entire quotient of $D_v$ by its four low root factors. We use the same exponential divided-difference integral as in the eventual proof. The factor $g(0)$ is real positive and bounded below by

$$
\frac{11}{12}\cdot\frac1{24}\cdot e^{-2}\cdot \cos(4/3) >\frac1{2000}.
$$

On $|t|=2L$ with $L\ge3$, the bound $|g(t)|\le2e^{2L}$ follows by dividing the elementary exponential and cubic bound for $D_v$ by the four factors of modulus at least $2L-2$. Jensen's formula therefore gives at most $(2L+\log4000)/\log 2<10L$ distant poles in $|t|\le L$. Since every distant pole has modulus larger than $\pi>3$, summing over the dyadic annuli beginning at radius three bounds the sum of their reciprocal cubes by $80/27<3$.

The two integrals defining $g(z)$ and $g(w)$ have moduli of their integrands differing by at most $e^{2\rho}$. At $w$ the complex argument of each integrand has absolute value at most $t_0=\max(\Im z,\Im w)\le\min(4/3,\rho)$, so the integral itself costs at most a secant factor in a lower bound. By convexity, $-\log\cos t_0\le (6/5)t_0$ from the bound at $4/3$. It follows that $|g(z)|/|g(w)|\le e^{(16/5)\rho}$.

Also $\Im z\le\Im w$. To see this, retain $a=\Re(1/z)>0$, $b=-\Re(1/w)>0$, $U=|z|^{-2}$ and $V=|w|^{-2}$ from the [logarithmic derivative argument](threshold-four-eventual.md#a-gap-between-the-two-pole-moduli). It gives $a>b$ and $U>V$. The bound $\pi/2<\arg w<3\pi/4$ gives $2b^2<V$. The function $(u-b^2)/u^2$ decreases on $u\ge V$, so

$$
(\Im z)^2=\frac{U-a^2}{U^2}\le\frac{U-b^2}{U^2}
\le\frac{V-b^2}{V^2}=(\Im w)^2.
$$

Consequently the left pair's contribution relative to the principal cosine amplitude is bounded by

$$
\frac{|D'_v(z)|}{|D'_v(w)|}r^{n+1}
=\frac{\Im z}{\Im w}\frac{|g(z)|}{|g(w)|}r^{n+1}
\le \exp\!\left(\left(\frac{16}{5}-\frac{n+1}{36}\right)\rho\right).
$$

Set $N=n+1$. At $N\ge120$ this is at most $e^{-\rho/8}$. For a distant pole $\zeta$ we have $|D'_v(\zeta)|=|\zeta^3/6-2v|\ge|\zeta|^3/7$. At the primary pole the divided-difference integral gives $|g(z)|\le e^2/24<1/3$, hence $|D'_v(z)|\le(8/3)(\Im z)\rho^2$. The preceding Jensen bound on reciprocal cubes, and $|z|<2$, bound the distant residue error relative to the principal cosine amplitude by $224\rho(2/3)^N<\rho/100$. This also bounds the conjugate sum with the positive normalization used in the eventual proof. The total error is strictly smaller than one because

$$
1-e^{-\rho/8}\ge\frac{\rho}{8+\rho}>\frac{\rho}{10}.
$$

## Signs and exact root ranks

Let $\Phi_n(q)=(n+1)\arg z+\arg D'_v(z)$. The exact residue formula in the [eventual proof](threshold-four-eventual.md#residues-and-signs-on-the-inner-part) now shows that the sign of $O_{n,4}(-q)$ is $-(-1)^k$ whenever $\Phi_n(q)=k\pi$ and $n\ge119$. Here $q>q_*$. The continuous phase has endpoint values $\pi/2$ and $(n+4)\pi/4$. For $m=\lfloor n/4\rfloor$ this yields a sign change between each successive pair of levels $k\pi,(k+1)\pi$ for $k=1,\ldots,m$, except possibly when the last upper level equals the terminal phase. If that level is unattained at finite $q$, take the ray beginning at the last hit of its lower level and use the leading sign $(-1)^m$ at infinity. For the other brackets take the first upper hit and the last preceding lower hit. These ordered disjoint brackets have phases strictly between their boundary levels at every interior point. The resulting $m$ distinct negative roots exhaust the degree. In particular $\sin\Phi_n$ has sign $(-1)^j$ at the old root of rank $j$ in increasing absolute value.

## Sharper suppression away from the outer edge

Write $\varphi=\arg z$, $\chi=\arg w$ and $\Psi=N\chi+\arg D'_v(w)$, and abbreviate $\Phi=\Phi_n$. In the notation above the normalized residue expansions at the same argument $-q$ are

$$
C_n=-\cos\Phi-A\cos\Psi+E_N,\qquad
C_{n+1}=-\cos(\Phi+\varphi)-Ar\cos(\Psi+\chi)+E_{N+1},
\qquad
A=\frac{|D'_v(z)|}{|D'_v(w)|}r^N .
$$

These normalizations are positive multiples of the corresponding polynomial values. Keeping $\Im z\le\rho\sin\varphi$ when bounding the distant residues gives

$$
|E_N|\le56\sin\varphi\,\rho^3(2/3)^N.
\tag{1}
$$

We improve the modulus gap by returning to inequality (2) in the eventual proof. Set $S=U+V$, $H=a+b$, and $d=a-b$ in its notation. The right-hand side before estimation is at least

$$
\frac32 dS+3d-2d^3-\frac{25}{16}.
$$

Its minimum for $1/2\le d\le1$ occurs at an endpoint and is $3S/4-5/16$, as $S\ge1/2$. Also $H^2=S-d^2+1+c_2/2\le S+7/8$. If $r>4/5$, these inequalities and $(U-V)/(U+V)\le-\log r$ give

$$
-\log r \ \ge\ \rho\,c(\rho),\qquad
c(\rho)=\frac{1/2-5\rho^2/48}{\sqrt{41/16+7\rho^2/8}},
\tag{2}
$$

using $2/\rho^2\le S\le(41/16)/\rho^2$. On the intervals $[3/50,1/2]$, $[1/2,1]$ and $[1,2]$, the decreasing function $c$ is bounded below respectively by $7/25$, $1/5$ and $3/100$. For $N\ge200$, each lower bound yields $(Nc(\rho)-16/5)\rho>2$. If $r\le4/5$, instead use $-\log r\ge1/5$ and $\rho<2$. By $\Im w>\rho/\sqrt2$ and the bound on $g(z)/g(w)$, this proves

$$
A\le\sqrt2 e^{-2}\sin\varphi<\tfrac14\sin\varphi
\qquad (N\ge200,\ \rho\ge3/50).
\tag{3}
$$

At a zero of $C_n$, this gives $|\cos\Phi|\le A+|E_N|\le(26/100)\sin\varphi$ and hence $|\sin\Phi|>9/10$. The difference between $C_{n+1}$ and $\sin\Phi\sin\varphi$ is at most $(1+r)A+|E_N|+|E_{N+1}|\le(52/100)\sin\varphi$, using (1). Therefore $C_{n+1}$ has the sign of $\sin\Phi$ at these roots of $C_n$.

## Two-pair cancellation close to the outer edge

Assume $\rho\le3/50$ and $N\ge200$. Let $h=(24v)^{1/4}$. Since $\Re w<0$, the Taylor remainder gives $|C_4(w)|\le\rho^4/24$ and $|2-e^w|>1$, so $h\le\rho$. On this range (2) gives $-\log r\ge(3/10)\rho$, including when $r\le4/5$ by the elementary bound above. Consequently

$$
A\le \exp\!\bigl(-(3N/10-16/5)\rho\bigr)\le e^{-Nh/4}.
\tag{4}
$$

Set $\lambda=h e^{i\pi/4}$, so $v=-\lambda^4/24$, and write $z=\lambda L(\lambda)$ and $w=i\lambda L(i\lambda)$. The two poles are expressed by the same analytic function $L$ because multiplication of $\lambda$ by $i$ preserves $v$. More explicitly, $L$ is the unique solution in $|L-1|<1/4$ of

$$
L^4 S_4(\lambda L)=2-e^{\lambda L},\qquad
S_4(\xi)=\sum_{\ell\ge0}\frac{24}{(\ell+4)!}\xi^\ell .
$$

For $|\lambda|\le1/4$, on $|L-1|=1/4$ the perturbation of $L^4-1$ is bounded by $(1+(5/4)^4/5)(e^{5/16}-1)$, because $|S_4(\xi)-1|\le(e^{|\xi|}-1)/5$. This is strictly smaller than $(1/4)(\sqrt2-1/4)^2(2-1/4)$, a lower bound for $|L^4-1|$ there. Rouché's theorem proves existence and uniqueness with multiplicity one, giving analyticity by the implicit function theorem. Conjugation and uniqueness imply real Taylor coefficients. These branches agree with the two upper poles by their limiting directions, and $\rho\le(5/4)h$.

Use analytic logarithms

$$
F(\lambda)=\log L(\lambda),\qquad
T(\lambda)=3F(\lambda)+\log(1+\lambda/(2L(\lambda)^3))
$$

with value zero at zero. The derivative identity $D'_v(z)=z^3/6-2v$ gives $D'_v(\lambda L(\lambda))=(\lambda^3/6)e^{T(\lambda)}$. On $|\lambda|\le1/4$, the log series give $|F|\le\log(4/3)<3/10$ and $|T|\le\log(64/19)<5/4$. Expanding the defining equation then gives

$$
F(\lambda)=-\frac3{10}\lambda-\frac{49}{300}\lambda^2+O(\lambda^3),
\qquad
T(\lambda)=-\frac25\lambda-\frac{33}{200}\lambda^2+O(\lambda^3).
$$

Indeed the coefficients of $z$ and $z^2$ in $\log(2-e^z)-\log S_4(z)$ are $-6/5$ and $-76/75$, and this series equals $4F$ upon substituting $z=\lambda e^F$. The first two coefficients of $T$ then follow from its logarithm formula.

Define

$$
\delta=\chi-\varphi-\pi/2,\qquad
\beta=\arg D'_v(w)-\arg D'_v(z)+\pi/2,\qquad
\kappa=N\delta+\beta.
$$

Choose the two derivative arguments continuous from their limits $3\pi/4$ at $z$ and $\pi/4$ at $w$. Then $\delta=\Im(F(i\lambda)-F(\lambda))$ and $\beta=\Im(T(i\lambda)-T(\lambda))$. Since $i\lambda=-\bar\lambda$ and both series have real coefficients, only powers of order $2$ modulo $4$ contribute to either difference. Cauchy's coefficient bounds therefore give, for $h\le3/50$,

$$
0\le\pi/4-\varphi\le h/3,\qquad
|\delta|\le(2/5)h^2,\qquad
|\beta|\le h^2/2,\qquad
|\kappa|\le(41/100)Nh^2 .
\tag{5}
$$

For the first bound, use the first two coefficients of $F$ and bound the higher orders by $(3/10)(4h)^3/(1-4h)$. For the next two bounds, the coefficients of order two contribute magnitudes $(49/150)h^2$ and $(33/100)h^2$, and the remainder bounds are respectively $(3/5)(4h)^6/(1-(4h)^4)$ and $(5/2)(4h)^6/(1-(4h)^4)$.

Let $s=n\bmod4$ and $\alpha=s\pi/2+\kappa$. Then $\Psi-\Phi=\alpha$ modulo $2\pi$. Write

$$
U_0=1+A e^{i\alpha},\qquad
V_0=e^{i\varphi}(1+iAr e^{i(\alpha+\delta)}),\qquad
\Delta=\Im(V_0\overline{U_0}) .
$$

At an old root, $\Re(e^{i\Phi}U_0)=E_N$ and hence the exact identity

$$
(\Re U_0) C_{n+1}=\sin\Phi\,\Delta+(\Re U_0)E_{N+1}-(\Re V_0)E_N
\tag{6}
$$

holds. We have $\Re U_0\ge1-A>0$. Temporarily setting $\kappa=\delta=0$ gives the following four values of $\Delta$, in order of $s$:

$$
\begin{array}{ll}
(1+A)(\sin\varphi+Ar\cos\varphi),&
(1-Ar)(\sin\varphi-A\cos\varphi),\\
(1-A)(\sin\varphi-Ar\cos\varphi),&
(1+Ar)(\sin\varphi+A\cos\varphi).
\end{array}
$$

The factor $\sin\varphi-A\cos\varphi$ is positive. Indeed $1-\tan\varphi\le2(\pi/4-\varphi)\le2h/3$, and $(1-A)^{-1}\le1+4/(Nh)$ by (4), giving $2h/(3(1-A))<3/50$. Each of the four values is therefore at least $(1-A)(\sin\varphi-A\cos\varphi)>(7/10)(47/50)(1-A)^2$, using $\cos\varphi\ge1/\sqrt2>7/10$. By the elementary bound on differences of unit complex exponentials, the change in the determinant from nonzero phase gaps is at most

$$
2A(2|\kappa|+|\delta|)\le (33/20)ANh^2\le\frac{132}{1000}(1-A)^2 .
$$

The last step uses (4) and $e^{-x}x^2\le(1-e^{-x})^2$ at $x=Nh/4$. Hence $\Delta>(1-A)^2/2$.

Finally $|E_N|,|E_{N+1}|\le(1-A)^2/100$. This follows from (1), $\rho\le(5/4)h$, and

$$
\frac{\rho^3}{(1-A)^2}\le(5/4)^3 h(h+4/N)^2 .
$$

To bound $\sin\Phi$ at the root, first note $\Re U_0/|U_0|\ge1/3$. If $A\le1/2$, use $1-A$ and $1+A$ to bound numerator and denominator. If $A>1/2$, then $Nh<4\log 2<3$, so $|\kappa|<1/10$ by (5). For $s\ne2$ this gives $\Re U_0\ge9/10$ and $|U_0|\le2$. For $s=2$, use

$$
\frac{|\Im U_0|}{\Re U_0}\le\frac{A|\kappa|}{1-A}
\le(41/25)h<1/10
$$

by $1-A\ge A Nh/4$. Now $|\cos(\Phi+\arg U_0)|=|E_N|/|U_0|\le1/100$, since $|U_0|\ge1-A$. The angle addition identity gives

$$
|\sin\Phi|\ge\frac13\sqrt{1-1/10000}-1/100>1/4.
$$

In (6) the term $\sin\Phi\,\Delta$ therefore has magnitude greater than $(1-A)^2/8$. The two residual terms together have magnitude at most $4(1-A)^2/100$, because both $U_0$ and $V_0$ have modulus at most two. This proves that $C_{n+1}$ has the sign of $\sin\Phi$ also in the outer region.

## Interlacing and the finite prefix

For $n\ge199$, the two bounds give $O_{n+1,4}(-q)$ of sign $(-1)^j$ at the old root $-q$ of rank $j$ in increasing absolute value. Because $O_{n+1,4}(0)>0$, there is a new root before the first old root and one between each pair of old roots. If $n\equiv3\bmod4$, the degree increases by one and the leading sign at infinity gives one additional root beyond the last old root. These strictly ordered roots exhaust the degree in both cases.

The exact finite check reconstructs the coefficients from the first-block rule and the delayed recurrence

$$
O_{n+1}=(n+1)O_n+2tO_n'+(n+\tbinom n2)O_{n-1}
       +(\tbinom n2+\tbinom n3)O_{n-2}
       +t\tbinom n3\bigl(O_{n-3}+(t-1)O_{n-3}'\bigr)
$$

for $n\ge3$. Indeed, for the exponential generating function $H(z,t)$ the defining reciprocal gives

$$
(2-E_3(z))\,\partial_z H
=(E_2(z)+tz^3/6)H+t(2+(t-1)z^3/6)\,\partial_t H.
$$

Equating coefficients gives the delayed recurrence. The first four polynomials are constants $1,1,3,13$. The two methods agree through row 200. The positive leading coefficients and the successive degree drops in the signed Euclidean remainder chains certify strict oriented interlacing through the pair ending at row 200. For equal degrees the chain starts with the later row and the remainder of the earlier row modulo the later row. For successive degrees it starts with the later and earlier rows. At each zero of the later row the earlier row has the sign of the second member of the chain, which is positive at the largest zero and alternates at the others. These checks also prove individual real-rootedness and simplicity in the finite prefix. Replay from the repository root with `python-flint` installed.

~~~
python -I -O topics/ordered-large-blocks/code/threshold_four_effective.py
~~~
