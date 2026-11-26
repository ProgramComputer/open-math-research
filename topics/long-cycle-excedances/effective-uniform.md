# A numerical cutoff for every minimum cycle length

**Partial theorem.** For $n\ge10^{20}$ and every $3\le k\le n$, the nonzero zeros of the two consecutive minimum-cycle-length excedance polynomials are simple, negative and strictly interlace. This makes the earlier existential cutoff explicit. Checking the entire finite complement by enumeration is computationally impractical. The sign comparison below is for the actual next row.

Use the [effective large-threshold theorem](effective-threshold.md) if $k\ge2000\sqrt n(3+\log(3\sqrt{n/k}))$. In the remaining range the short-cycle estimate applies. More generally, it proves strict interlacing for every $n\ge10^6$ satisfying
$$
\frac n{200k}>30\log n+20. \tag{1}
$$
To check that the two sufficient conditions cover every threshold when $n\ge10^{20}$, observe first that if $k\le\sqrt n$ equation (1) follows directly. Otherwise $k>\sqrt n$ and $k<2000\sqrt n(3+\log 3+(\log n)/4)$. At $n=10^{20}$, $400000(3+\log3+(\log n)/4)(30\log n+20)<10^{10}$ using $\log 3<6/5$ and $\log10<7/3$. The ratio of $\sqrt n$ to these two logarithmic factors increases for $\log n\ge40$, by logarithmic differentiation.

## A common coefficient contour

Use $t=-e^{-s}$, $s\ge0$, $w_p=s+ip\pi$ for odd $p$, $r=|w_1|$, $S=\sin\theta=\pi/r$ and $z_p=r/w_p$. Define $T_s$ by the [fixed-threshold coefficient identity](fixed-threshold.md)
$$
\frac{E_{j,k}(t)}{j!(1-t)^{j+1}}=[w^j]\frac{T_s(w)}{1+e^{w-s}}.
$$
The logarithm $G_s(w)$ of $T_s(w)$ is the specific polynomial with $G_s(0)=0$. Its linear term is $e^{-s}w/(1+e^{-s})$. Its terms of degree $\ell\ge2$ have absolute size at most $(|w|/r)^\ell\sum_p|z_p|^\ell/\ell$, by the Eulerian pole formula. For $s>0$ it also has the absolutely convergent expansion
$$
G_s(w)=-\sum_{a\ge1}\frac{(-e^{-s})^a}{a}\sum_{\ell=1}^{k-1}\frac{(aw)^\ell}{\ell!}.
$$
On $|w|\le R_*=r(1+1/(50k))$ we claim
$$
|G_s(w)|\le B:=6+10\log k . \tag{2}
$$
For $s\le10$, $\sum_p|z_p|^2\le2+1/(2S^2)<8$, by telescoping $\sum_{p=3,5,\dots}1/(p^2-1)=1/4$. The linear term costs less than six, and $8e^{1/50}<10$ bounds the coefficient of the harmonic sum in the rest.

For $s>10$ put $L=\min(k-1,\lfloor s^2/16\rfloor)$ and $\delta=R_*-s\le5/s+s/(40k)$. For terms of degree at most $L$, use the exponential sum. The absolute truncated exponential, including the factor $e^{-as}$, is bounded by $e^{a\delta}\Pr(\operatorname{Pois}(aR_*)\le L)$. If $a\le2L/s$, then $a\delta\le5/8+1/20<1$, so this range contributes at most $3(1+\log k)$. For $a>2L/s$ the truncated exponential series times $e^{-aR_*}$ is bounded by the lower-tail probability $\Pr(\operatorname{Pois}(aR_*)\le aR_*/2)\le e^{-aR_*/8}$. Since $\delta/s<3/50$, the resulting sum is at most $\sum_{a\ge1}e^{-as/16}/a<2$. Any remaining degrees have $\ell\ge7$ and $\ell S^2>1/2$. By the lattice integral estimate in [the pole argument](separated-poles.md),
$$
\sum_p|z_p|^\ell\le2+\frac{3\pi}{4\sqrt2 S\sqrt\ell}<5 .
$$
Here the integral estimate is valid for $\ell\ge4$ because $(1+x)^{\ell/4}\ge1+\ell x/4$. Thus the higher degrees cost at most $6\log k$, proving (2).

Take $nS^2\ge1$. If $s\le10\sqrt k$ use the circle $R=r(1+1/(100k))$. Only $w_{\pm1}$ are inside, since $R_*^2-r^2<5$ whereas $|w_3|^2-r^2=8\pi^2$. The distance from the circle to each pole exceeds $n^{-2}$, using $r/(100k)\ge\pi/(100n)$ for the first pair and the squared gap for the others. If $s>10\sqrt k$, choose a radius in $[r(1+1/(100k)),R_*]$ whose distance from every pole radius is at least $n^{-2}$. This interval has length at least $\pi/(100n)$ and fewer than $10\sqrt n$ pole radii can meet it within $n^{-2}$, as $r\le\pi\sqrt n$. On both circles $|1+e^{w-s}|^{-1}\le4n^2$. Indeed, when $|\Re(w-s)|\ge n^{-2}/2$ use $|1-e^{\Re(w-s)}|$. Otherwise the distance of $\Im w$ from the nearest odd multiple of $\pi$ is at least $\sqrt3\,n^{-2}/2$, and the squared modulus is $(1-e^{\Re(w-s)})^2+4e^{\Re(w-s)}\cos^2(\Im w/2)$.

For $j=n,n+1$ use the common positive normalization
$$
Y_j=\frac{r^{j+1}E_{j,k}(t)}{2|T_s(w_1)|j!(1-t)^{j+1}} .
$$
The residues give the sum over enclosed positive odd $p$ of $\Re(T_s(w_p)z_p^{j+1})/|T_s(w_1)|$. The circle remainder in either row has magnitude at most $2n^2r\exp(2B-n/(200k))<n^{-2}$, by (1).

## Neighboring residues

Put $\gamma=\Im G_s(w_1)$ and $\Psi=(n+1)\theta-\gamma$. The principal pair contributes $\cos\Psi$ to $Y_n$. For $s>10\sqrt k$, at odd poles one has
$$
G_s(w_p)=-\log(1+e^{-s})-H(w_p),\qquad
H(w)=\sum_{a\ge1}\frac{e^{-aw}}a\sum_{\ell=0}^{k-1}\frac{(aw)^\ell}{\ell!}.
$$
This follows by substituting $e^{-aw_p}=(-e^{-s})^a$ in the polynomial expansion. On the vertical segments from $s$ to enclosed $w_p$ one has $\log(|w|/s)\le 7/(100k)$. Differentiating the uniformly converging series for $H$ there gives
$$
|H'(w)|\le e^{7/100}\sum_{a\ge1}e^{-as}(as)^{k-1}/(k-1)!.
$$
For $k\ge14$ the sum is at most $1/s+1/\sqrt{2\pi(k-1)}$, by summing the unimodal gamma density on a mesh of spacing $s$. Its integral is one and Stirling's lower bound gives the stated bound at its mode $k-1$. Thus $\pi |H'|\le\pi e^{7/100}(1/(10\sqrt{14})+1/\sqrt{26\pi})<12/25$. For $3\le k\le13$, $s>10\sqrt k\ge2k$ and $s>17$. Each summand is bounded by the Poisson probability of falling below half its mean, at most $e^{-as/8}$. Therefore $\pi |H'|\le\pi e^{7/100}/(e^{17/8}-1)<12/25$. Since $H(s)$ is real,
$$
|\gamma|<12/25,\qquad
|G_s(w_p)-G_s(w_1)|\le(12/25)(p+1) \quad(p\ge3).
$$

An enclosed pole has $(p^2-1)S^2\le1/(20k)$, hence $|z_p|^n\le\exp(-(49/100)(p^2-1))$. The total nonprincipal weighted error on this circle is bounded by
$$
\sum_{p=3,5,\ldots}p\,|z_p|^n\,|T_s(w_p)/T_s(w_1)|
<3e^{-2}+\sum_{p=5,7,\ldots}p e^{-(37/100)(p^2-1)}<21/50 ,
$$
where the sum on the left runs only over enclosed poles. For $p\ge5$, $(p+1)/(p^2-1)\le1/4$. The remaining sum is bounded by its first term and half the integral of the decreasing summand from $5$ to infinity. For $s\le10\sqrt k$ the nonprincipal sum is empty. Subtracting $\cos\theta\,Y_n$ from the following row multiplies each pole contribution by $z_p-\cos\theta$, whose magnitude is at most $pS$. Thus
$$
|Y_n-\cos\Psi|<1/2,\qquad |Y_{n+1}-\cos\theta\,Y_n+S\sin\Psi|< S/2. \tag{3}
$$
These hold throughout $nS^2\ge1$. The correction $\gamma$ need only be bounded on the outer endpoint for the root count.

## A phase-crossing argument

Let $H_0=\lfloor7\sqrt n/20\rfloor$ and $\theta_*=(H_0+5/6)\pi/n$. Then $n\sin^2\theta_*>1$, $\theta_*<1/100$ and $s_*=\pi\cot\theta_*>2\sqrt n>10\sqrt k$. These follow from $H_0+1\le(9/25)\sqrt n$, the sine and cosine Taylor bounds, and (1). Thus $\Psi(\theta_*)<(H_0+1)\pi$ by $12/25+1/100<\pi/6$. All $H_0$ exterior roots from the [effective front proof](effective-front.md) lie below $|t(\theta_*)|$. Indeed their moduli are bounded by $(9/8)(51/5)(H_0/(H_0+1))^n$ and
$$
n\log(1+1/H_0)-\frac n{H_0+5/6}
\ge \frac n{(H_0+1)^2}\left(\frac12-\frac{H_0+1}{6(H_0+5/6)}\right)
>\frac{33/100}{(9/25)^2}>\frac52>\log((9/8)(51/5)).
$$
Use $\pi\cot\theta_*<n/(H_0+5/6)$. At the central endpoint $s=0$, $\gamma=\pi/2$: the linear term gives this value, even powers in $G_0(i\pi)$ are real, and odd powers of degree at least three have zero coefficient by the Eulerian pole formula. Hence $\Psi(\pi/2)=n\pi/2$ exactly.

Take the first hits, after $\theta_*$, of the levels $j\pi$ for $H_0+1\le j\le\lfloor n/2\rfloor$. They occur in the indicated order by continuity. Between two consecutive hits take the last hit of the lower level before the upper one. On the intervening open interval the phase is strictly between the two levels. By (3) the old polynomial has opposite endpoint signs. Select one zero there. Its phase gives the sign of the next polynomial by (3), since $|\cos\Psi|<1/2$ implies $|\sin\Psi|>\sqrt3/2$. For even $n$, an early first hit of the central level is harmless: the reciprocal intervals are disjoint and the degree count below exhausts all roots. For odd $n$, the odd reciprocal polynomial $P_n$ has the additional zero $-1$ with the required next-row sign directly from (3) at $\pi/2$. Reflecting the selected half-intervals and including the $2H_0$ exterior roots yields $n-2$ distinct negative roots for $P_n$ in both parities. Its degree is $n-2$, so each is simple. The old-root signs from (3) and the exterior-root estimates alternate for $P_{n+1}$ after division by $t$. Reciprocity gives $P_{n+1}(1/x)=x^{-(n-1)}P_{n+1}(x)$ at the reflected roots. Its constant and leading coefficients are one and its degree is $n-1$. The intermediate value theorem gives strict interlacing. This proof needs no derivative bound or monotonicity for the phase correction.

**Scope.** This argument bounds the size of a possible counterexample. It does not settle the remaining finite range. There is no checked Lean or Rocq proof.

[Independent agent-assisted review](review-uniform-effective.md) · [Exact scalar checks](verify_uniform_effective_constants.py)
