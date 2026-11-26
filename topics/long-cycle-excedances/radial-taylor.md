# A uniform Taylor estimate on a wider coefficient circle

Let $E_{n,k}$ count permutations on $n$ labels by excedances, with every cycle of length at least $k$. Write $P_n(t)=E_{n,k}(t)/t$. For $n\ge10^6$ and $400\le k\le n$, the $n-2$ zeros of $P_n$ are simple and negative and strictly interlace the zeros of $P_{n+1}$ at the same threshold provided

$$
\frac{89 n}{100k}>47+\frac52\log n. \tag{1}
$$

Together with the signed-pole theorem for $k\ge2000\sqrt n$ this gives the conclusion for every $3\le k\le n$ as soon as $n\ge250000^2$. The uniform estimate concerns the actual consecutive rows. The original conjecture at all sizes remains open. Lean or Rocq coverage is ⬜ None.

## The truncated logarithm

Use the [coefficient identity](fixed-threshold.md) at $t=-e^{-s}$, $s\ge0$. Put $w_p=s+ip\pi$ for odd $p$, $r=|w_1|$, $S=\pi/r=\sin\theta$, and $z_p=r/w_p$. The analytic logarithm $L(w)=\log((1+e^{w-s})/(1+e^{-s}))$ on $|w|<r$ is fixed by $L(0)=0$. Its Taylor polynomial through degree $k-1$ is $G$, the logarithm of the numerator $T_s=e^G$ in that identity. This follows also by expanding $\log(1+e^{w-s})$ near zero for $s>0$ and taking the limit at $s=0$. We compare $G$ on $r\le |w|\le R_{\ast}=(1+1/k)r$ with $L$ at $\widehat w=(1-1/k)r w/|w|$. We will prove

$$
|G(w)-L(\widehat w)|+|G(w_1)-L((1-1/k)w_1)|<34. \tag{2}
$$

For $s\le4\sqrt k$ use the [Eulerian pole expansion](effective-uniform.md). The degree-one coefficient times $r$ is at most $4$ by $r\le s+\pi$ and $1/(1+e^s)\le e^{-s}$. For $j\ge2$ the absolute coefficient of degree $j$ times $r^j$ is bounded by $B_j/j$, where

$$
B_j=\sum_p|z_p|^j\le2+\frac{9}{4S\sqrt j}.
$$

Indeed $p^2-1\ge (p-1)^2$ for $p\ge1$. The nonprincipal sum is at most $I_j/S$ by the decreasing integral bound, where $I_j=\int_0^\infty(1+v^2)^{-j/2}\mathrm{d}v$. Integration by parts gives $I_{j+2}=(j-1)I_j/j$. Thus $\sqrt j I_j$ decreases in each parity and its initial values at $j=2,3$ are $\pi/\sqrt2$ and $\sqrt3$, both below $9/4$.

Write $U=1/(S\sqrt k)<129/100$ in this range. For $1\le j<k$ we have $((1+1/k)^j-(1-1/k)^j)/j\le e/k$. This uses convexity of $e^x$ on $[0,1]$ and Bernoulli's inequality. At the principal radius $r$ the same bound is $1/k$. The tail at the contracted radius in either comparison costs at most

$$
(2+9U/4)\sum_{j\ge k}\frac{e^{-j/k}}j
\le \frac{2+9U/4}{ek(1-e^{-1/k})}<\frac{38}{100}(2+9U/4).
$$

Since $\sum_{j<k}j^{-1/2}\le2\sqrt k$, the sum in (2) is bounded by $12/k+(e+1)(2+9U/2)+(76/100)(2+9U/4)<34$. The $12/k$ covers the two linear-term differences.

For $s>4\sqrt k$ use the exponential expansion of $L$. Here $r/s<1001/1000$, $r-s< (31/100)s/k$, $R_{\ast}-s<(132/100)s/k$, and $s-\widehat r>(69/100)s/k$ with $\widehat r=(1-1/k)r$. The Taylor truncation can be bounded before summing over exponential frequencies. For $R=|w|$ the radial change $|G(w)-G(\widehat w)|$ is at most

$$
(R-\widehat r)\sum_{a\ge1}e^{a(R-s)}\Pr\lbrace \mathrm{Pois}(aR)\le k-2\rbrace. \tag{3}
$$

Indeed the Taylor series of $\log(1+e^{w-s})$ supplies the absolute majorant $e^{-as}/a$ times the first $k-1$ nonconstant terms of $\exp(aw)$ at each frequency $a$. Differentiate this finite exponential sum along the radial interval and bound its nonnegative derivative by its value at $R$.

For $a\le5k/(4s)$ the sum in (3), after multiplication by the radial width, costs at most $(2r/k)(5k/(4s))e^{33/20}<27/2$. At $R=r$ it costs at most $(r/k)(5k/(4s))e^{31/80}<2$. For larger $a$, the mean $aR$ is greater than $5k/4$. The Poisson lower-tail bound at $4/5$ of the mean is at most $e^{-aR/50}$. Hence the tail of (3) costs at most $(2r/k)\sum_{a\ge1}e^{-as/60}\le120r/(ks)<31/100$, since $1/50-1.32/400>1/60$.

The remaining Taylor tail $|L(\widehat w)-G(\widehat w)|$ costs at most

$$
\sum_{a\ge1}\frac{e^{-a(s-\widehat r)}}a\Pr\lbrace \mathrm{Pois}(a\widehat r)\ge k\rbrace.
$$

For $a\le k/(2\widehat r)$ apply the exponential Markov inequality with parameter $\log 2$. This part is below $(1+\log k)e^{-k/6}<1/10$. Above that range bound $1/a$ by $2\widehat r/k$ and sum the geometric series to obtain a contribution at most $2\widehat r/[k(s-\widehat r)]<3$. All these estimates imply (2).

The two exact logarithms in (2) have readily bounded real parts. Over the outer circle $|1+e^{\widehat w-s}|\le1+e^{r-s}\le1+e^\pi<25$. At the contracted principal pole the numerator modulus is $|1-e^{-(s+i\pi)/k}|\ge\sin(\pi/k)\ge2/k$, by minimizing $|1-xe^{-i\pi/k}|$ over real $x$. The factors $1+e^{-s}$ cancel. We obtain

$$
\max_{r\le |w|\le R_{\ast}}\frac{|T_s(w)|}{|T_s(w_1)|}<13k e^{34}. \tag{4}
$$

## Coefficient circle and neighboring poles

There is a circle of radius $R$ in $[r(1+9/(10k)),R_{\ast}]$ at distance at least $\delta=\min(r/(40k),1/r)$ from all poles. The interval length is at least $4\delta$. The positive pole radii within $\delta$ of the interval are separated by at least $8\pi^2/(2(R_{\ast}+\delta))>2\delta$, by subtraction of squares. Their individual excluded intervals have length $2\delta$ and cannot cover the whole interval. On the chosen circle $|1+e^{w-s}|^{-1}\le4/\delta$. In fact if $|\Re w-s|\ge\delta/2$, use $1-e^{-\delta/2}\ge\delta/4$. Otherwise the imaginary distance to the nearest odd multiple of $\pi$ exceeds $\sqrt3\delta/2$ and the squared-modulus identity in the [original contour estimate](effective-uniform.md) gives the same conclusion.

Normalize each row as in that estimate, with $Y_j=r^{j+1}E_{j,k}(t)/(2|T_s(w_1)|j!(1-t)^{j+1})$. For $nS^2\ge1$, (4) bounds the circle remainder for either row by

$$
26k(40k+r^2)\exp(34-0.89n/k)<1300 n^2\exp(34-0.89n/k)<S/100.
$$

Here $k\log(1+0.9/k)>0.89$, $r^2\le\pi^2 n$ and (1) supplies the last inequality using $e^{13}>130000$.

When $s\le4\sqrt k$ the circle encloses only $w_{\pm1}$ because $R_{\ast}^2-r^2<33<8\pi^2$. Otherwise on the vertical segments from $s$ to any enclosed pole, $\log(|w|/s)\le(1+\pi^2/32)/k<1.32/k$. The derivative estimate for the pole value correction $H$ in the [neighboring-residue proof](effective-uniform.md) now gives

$$
\pi |H'(w)|\le\pi e^{1.32}\left(\frac1s+\frac1{\sqrt{2\pi(k-1)}}\right)<12/25 .
$$

Thus the argument of $T_s(w_1)$ chosen as $\gamma=\Im G(w_1)$ satisfies $|\gamma|<12/25$ in this range, and the ratio $|T_s(w_p)/T_s(w_1)|$ is bounded by $e^{(12/25)(p+1)}$ for enclosed positive odd $p\ge3$. For such poles $(p^2-1)S^2\le(1+1/k)^2-1<0.006$, so $|z_p|^n\le e^{-(49/100)(p^2-1)}$ using $nS^2\ge1$. Consequently the same weighted nonprincipal tail from the original proof is below $21/50$.

Set $C=\cos\theta$ and $\Psi=(n+1)\theta-\gamma$. Taking the difference of the common residues introduces the multiplier $z_p-C$, of modulus at most $pS$. With the two circle errors just proved this gives $|Y_n-\cos\Psi|<1/2$ and $|Y_{n+1}-CY_n+S\sin\Psi|<S/2$. These are precisely the two estimates used in the [phase-crossing and root count](effective-uniform.md). For clarity, (1) and $n\ge10^6$ imply $n>4k$, so its outer endpoint $s_{\ast}>2\sqrt n$ satisfies $s_{\ast}>4\sqrt k$. Its bound on $\gamma$ holds there. The endpoint at $s=0$ and the [exterior-root theorem](effective-front.md) are unchanged. Selecting one old root between successive phase levels and reflecting as in that proof gives $n-2$ distinct negative roots and alternating next-row signs, proving (1).

## Combining the two ranges

For $n\ge250000^2$, thresholds $k\ge2000\sqrt n$ are covered by the [signed-pole theorem](uniform-hilbert/README.md). For $400\le k<2000\sqrt n$, condition (1) follows from $(89/100)\sqrt n/2000>47+(5/2)\log n$. It holds at $n=250000^2$ using $\log 250000<25/2$, and the difference increases thereafter by differentiation. For $3\le k<400$ the [earlier short-cycle criterion](effective-uniform.md) applies since $n/(200\cdot400)>30\log n+20$ at the same endpoint, again with increasing difference. All upper bounds are sufficient and do not assert an optimal transition size.

[Exact scalar checks](verify_radial_taylor.py)

[Independent mathematical audit and boundary checks](review-radial-taylor.md) · [Independent rational checker](review-radial-constants.py) · [Prior-art screen](uniform-hilbert/literature.md)

On November 26, 2026, an independent search of native GitHub issues for `"long-cycle excedances" "Taylor" interlacing`, native GitHub code for `"minimum cycle length" "excedances" "interlacing"`, and indexed X results for Alexandersson, excedances, long cycles and interlacing returned no competing proof of the present range. Index coverage is incomplete. Alexandersson states the consecutive-row problem for the excedance statistic. [Primary source](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)
