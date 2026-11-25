# A sharp lower bound for real root moduli at every ordered threshold

For an integer $j\ge2$, let $O_{n,j}(t)$ count ordered set partitions of $[n]$ by their blocks of size at least $j$. Define
$$
S_{j-1}(z)=\sum_{s=0}^{j-1}\frac{z^s}{s!},\qquad
T_j(z)=e^z-S_{j-1}(z),\qquad
D_{j,q}(z)=2-S_{j-1}(z)+qT_j(z).
$$
The ordered sequence construction gives $\sum_{n\ge0}O_{n,j}(-q)z^n/n!=1/D_{j,q}(z)$. The question concerns the lower edge of the moduli of negative real zeros. The full interlacing result for $j=2$ is given separately. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Threshold two](threshold-two.md)

**Theorem.** Let $\rho_j$ be the unique positive solution of
$$
 e^{\rho_j}-2=2\,\frac{T_j(\rho_j)}{\rho_j^{j-1}/(j-1)!},
\qquad
 q_j^*=\frac{S_{j-1}(\rho_j)-2}{T_j(\rho_j)}.
$$
Then $q_j^*>0$ and $O_{n,j}(-q)>0$ for every $n\ge0$ and $0\le q\le q_j^*$. At $q=q_j^*$, $D_{j,q}$ has a double zero at $\rho_j$, and every other zero has modulus strictly greater than $\rho_j$. For each $q>q_j^*$ there are infinitely many $n$ with $O_{n,j}(-q)<0$. In particular, $q_j^*$ is the infimum of the moduli of the negative real zeros over all rows. Every neighborhood of this edge above $q_j^*$ contains a zero from infinitely many rows.

## The critical radius

For $r>0$, write
$$
A_j(r)=\frac{T_j(r)}{r^{j-1}/(j-1)!}
      =\sum_{\ell\ge1}\frac{r^\ell}{j(j+1)\cdots(j+\ell-1)},
\qquad E_j(r)=e^r-2-2A_j(r).
$$
The coefficient of $r^\ell$ in $E_j$ is nonnegative for $\ell\ge1$, since $j(j+1)\cdots(j+\ell-1)\ge(\ell+1)!$. It is positive for $\ell\ge2$. Thus $E_j$ increases strictly from $-1$ to infinity and has exactly one positive zero. At fixed $r>0$, $A_j(r)$ decreases strictly as $j$ increases. Consequently $\rho_j$ decreases with $j$.

A positive zero of $D_{j,q}$ at $r$ requires $q=Q_j(r)=(S_{j-1}(r)-2)/T_j(r)$. The derivative of $Q_j$ has the sign of $-E_j(r)$. In fact, writing $w=r^{j-1}/(j-1)!$, the numerator of its derivative is
$$
S_{j-2}(r)T_j(r)-(S_{j-1}(r)-2)(T_j(r)+w)
=-wE_j(r).
$$
The ratio $Q_j$ is zero where $S_{j-1}=2$, has positive derivative there, and tends to zero at infinity. It has a strict maximum $q_j^*>0$ at $\rho_j$ with negative second derivative. The identity $D_{j,q}(r)=T_j(r)(q-Q_j(r))$ shows that this critical zero is double. It also shows that $D_{j,q}$ has no positive zero when $q>q_j^*$.

The critical equation also gives $q_j^*=2(j-1)!/\rho_j^{j-1}-1$. For $\lambda=\log 2$ and large $j$, the series for $A_j$ yields $A_j(\rho_j)=\rho_j/j+O(j^{-2})$, uniformly because the radii are bounded. Using $e^{\rho_j-\lambda}=1+A_j(\rho_j)$ gives
$$
\rho_j=\lambda\left(1+\frac1j\right)+O(j^{-2}),
\qquad q_j^*\sim \frac{2(j-1)!}{e\,\lambda^{j-1}}.
$$

## Positivity at the critical value

Put $\rho=\rho_j$, $q=q_j^*$, and $D(z)=D_{j,q}(\rho z)$. First suppose $\rho\ge1$. The coefficient of $z^k$ in $G(z)=D(z)/(1-z)$ is the sum of the first $k+1$ coefficients of $D$. For $1\le k<j$, this is $1-\sum_{s=1}^k\rho^s/s!\le0$. For $k\ge j$, it is $-q\sum_{s>k}\rho^s/s!<0$, by $D(1)=0$. Hence $B=1-G$ has nonnegative coefficients and zero constant term. The expansion $(1-z)^{-1}\sum_{k\ge0}B(z)^k$ proves strict coefficient positivity of $1/D$. At the double zero, $G(1)=0$, so $B(1)=1$. For $|z|<1$, $|B(z)|<1$. On $|z|=1$, equality $B(z)=1$ forces all powers with positive coefficients to equal $1$. Their support contains consecutive integers, so this occurs only at $z=1$. Thus the critical zero is isolated strictly in modulus in this case.

For the remaining radii use $H(z)=D(z)/(1-z)^2$, an entire function. Write $a_s=\rho^s/s!$ and $b_s=q\rho^s/s!$. For $z=e^{i\theta}$ with $x=1-\cos\theta>0$, the identity $(1-z)^2=-2xz$ and $D(1)=0$ give
$$
2\Re H(e^{i\theta})=1-\sum_{s=2}^{j-1}a_s R_{s-1}(\theta)+\sum_{s\ge j}b_s R_{s-1}(\theta),
\qquad R_k(\theta)=\frac{1-\cos(k\theta)}{1-\cos\theta}.
$$
The quotient has a continuous extension at zero with value $k^2$. Also $0\le R_k\le k^2$, by the geometric-sum expression for $|1-e^{ik\theta}|/|1-e^{i\theta}|$.

The elementary bounds on the critical radii used below are
$$
\rho_3>1,\qquad \frac{83}{100}<\rho_6,\qquad
\rho_4<\frac{19}{20},\quad \rho_5<\frac{89}{100},\quad
\rho_6<\frac{17}{20},\quad \rho_7<\frac56.
$$
They follow by evaluating the sign of $E_j$ at the given rational arguments. For $0<x\le1$, bound $e^x$ below by $\sum_{s=0}^6 x^s/s!$ and above by this sum plus $x^7/(7!(1-x/8))$. Bound $A_j(x)$ below by its first two terms and above by $x/j+x^2/(j(j+1)(1-x/(j+2)))$. The rational comparisons are verified in the companion script. In particular, the preceding $G$ argument applies at $j=2,3$.

For $j\ge7$, monotonicity gives $\rho<5/6$, and the sum of all the negative contributions is bounded above by
$$
\sum_{s\ge2}(s-1)^2\frac{(5/6)^s}{s!}
=\frac{31}{36}e^{5/6}-1<1.
$$
For $j=4,5,6$, let $U_j$ be the indicated rational upper bound on $\rho_j$. If $x\ge1/4$, then $R_2=4-2x\le7/2$ and $R_3=(3-2x)^2\le25/4$. Together with $R_1=1$ and $R_4\le16$ these give the first column of strict upper bounds below. For $0<x\le1/4$ we may take $\theta\in[0,\pi]$ by symmetry and have $\theta\le\pi/3$ and $\theta\le(j-1)\theta\le2\pi-\theta$. Therefore $R_{j-1}\ge1$. Since
$$
b_j=(S_{j-1}(\rho)-2)\frac{\rho^j/j!}{T_j(\rho)}
>\frac45\left(\sum_{s=0}^3\frac{(83/100)^s}{s!}-2\right)=:L,
$$
the $s=j$ contribution supplies at least $L$. Here the tail ratio bound gives $(\rho^j/j!)/T_j(\rho)\ge1-\rho/(j+1)\ge j/(j+1)\ge4/5$. All arithmetic in the following upper bounds is rational. The decimal values are rounded up.

| $j$ | $\sum_{s=2}^{j-1}(U_j^s/s!)R_{s-1}$ with $x\ge1/4$ | $\sum_{s=2}^{j-1}(s-1)^2 U_j^s/s!-L$ |
|---:|---:|---:|
| 4 | $0.952$ | $0.808$ |
| 5 | $0.971$ | $0.886$ |
| 6 | $0.915$ | $0.810$ |

Thus $\Re H$ is strictly positive on the unit circle, including at $1$ by continuity and the strict uniform bounds. The minimum principle for harmonic functions gives $\Re H>0$ on the closed disk. This also rules out every other zero of $D$ there. The reciprocal $K=1/H$ is analytic on a neighborhood of the closed disk and has positive real part there. Its real Taylor coefficients $K_k$ give
$$
[z^n]\frac{1}{D(z)}
=\sum_{k=0}^n(n+1-k)K_k
=\frac{1}{2\pi}\int_{-\pi}^{\pi}\Re K(e^{i\theta})
  \left|\sum_{k=0}^n e^{\mathrm{i}k\theta}\right|^2 d\theta>0.
$$
The integral identity follows by expanding the square, whose Fourier coefficients are $n+1-|k|$ for $|k|\le n$. The integrand is positive away from the finitely many zeros of the squared sum. Rescaling $z$ by the positive $\rho$ preserves coefficient signs.

## All subcritical parameters and sharpness

Write $F_p(z)=1/D_{j,p}(z)$. For $0\le q\le q_j^*$ the exact identity
$$
F_q=\frac{F_{q_j^*}}{1-(q_j^*-q)T_jF_{q_j^*}}
$$
has a coefficientwise nonnegative geometric expansion, with the strictly positive coefficients of $F_{q_j^*}$ as its first term. It proves the claimed positivity throughout the interval.

For $q>q_j^*$, the reciprocal $F_q$ is analytic across the whole positive real axis and tends to zero there at infinity. Suppose its coefficients were eventually nonnegative. Add a polynomial to make the full series nonnegative. A nonnegative Taylor series of finite radius $R>0$ must be singular at $R$. Indeed, if it extended analytically across $R$, each Taylor coefficient of its expansion about $R$ would be the limit of a nonnegative derivative series from below. Expanding at $R+\varepsilon$ and interchanging the nonnegative summations would give convergence of the original series at $R+\varepsilon$, a contradiction. Here there is no positive real singularity, so the series after adding the polynomial would be entire. It would have infinitely many nonzero coefficients, since $F_q(0)=1$ and $F_q(x)\to0$ imply $F_q$ is not a polynomial. Nonnegative coefficients with infinite support force growth along the positive real axis exceeding every fixed polynomial bound. That contradicts the behavior of $F_q$ plus the added polynomial. Thus infinitely many coefficients of $F_q$ are negative. For every corresponding row, continuity yields a real zero with modulus strictly between $q_j^*$ and $q$.

The result concerns $j\ge2$. At $j=1$, every block carries the variable and every positive-size row has a zero at the origin, so that threshold has a different endpoint behavior.

[Rational comparison checker](code/verify_lower_spectral_edge.py)

```sh
python topics/ordered-large-blocks/code/verify_lower_spectral_edge.py
```
