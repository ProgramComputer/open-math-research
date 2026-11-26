# Partial fractions for any number of occupied Eulerian poles

This estimate compares the middle roots of consecutive rows with arbitrary numbers of permitted cycles. Let $S=\sin\theta$, $nS^2\ge1$, $n\ge100$, $n\ge k\ge32$. Put $D_0=\sqrt{n/k}$ and $U=3+\log(3D_0)$. Assume
$$
kS\ge2000 U. \tag{A}
$$
We prove that the integer-phase signs and both insertion signs at old roots hold under (A), within the residual-index range below. It suffices below to consider $n\ge2k-1$, since the earlier transitions are single-cycle Eulerian. For the lag estimates below first take $k\le n/3$; the other thresholds are covered by the one- and two-cycle band, apart from the single transition $n=3k-1$ which has $k>n/3$. The same residual estimates in fact hold for $k\le(n+3)/3$, so the displayed proof covers this transition too.

## Expanding by occupied pole subsets

Use $z_p=(\cos\theta+ipS)^{-1}$, $\rho_p=|z_p|$, and $F_j,D,d_j$ as in the [central interval proof](central-interval.md). Put $g_j=d_j$ for $j\ge k$ and zero elsewhere. Let $b_j=g_j-g_{j-1}$, so $\sum|b_j|<2/k$ and $b_j=0$ below $k$. The exact generating series is
$$
\sum_m F_m u^m=\prod_{p\,\mathrm{odd}}D(z_pu),\qquad
D(z)-1=\frac{\sum_{j\ge k} b_j z^j}{1-z}.
$$
The contribution supported on a single pole is $d_m B_m$, $B_m=\sum_p z_p^m$. Write $R_m=F_m-d_m B_m$ when $m\ge k$. For a finite set $I$ of $h\ge2$ distinct occupied poles the coefficient with total exponent $m$ is summed over $s_p\ge k$, $\sum s_p\le m$, with weight $\prod b_{s_p}$. By partial fractions of $\prod_{p\in I}(1-z_pu)^{-1}$ its remaining factor is
$$
\sum_{a\in I} \prod_{p\in I} z_p^{e_p}
\prod_{q\in I\setminus\{a\}}(1-z_q/z_a)^{-1},
$$
where $e_q=s_q$ for $q\ne a$, $e_a=s_a+m-\sum s_p$, and $\sum e_p=m$. The distinctness of the $z_p$ holds for $0<\theta<\pi$. In particular $e_p\ge k$ and some $b\in I$ has $e_b\ge m/h$.

We will bound the value for $m=n$ and $m=n+1-k\ge k$ with $mS^2\ge2/3$. The derivative bound only uses $m=n$. Write $w_p=\rho_p^{k/3-1}$. Since
$$
|1-z_q/z_a|=|q-a| S\rho_q,
$$
the absolute value of each term inside the sum over $a$, after suppressing the $b_{s_p}$ weights, is at most
$$
S^{1-h}\rho_b^{m/(3h)}\,w_a\prod_{q\ne a}\frac{w_q}{|q-a|}. \tag{B}
$$
We took $k/3$ powers at every pole and $m/(3h)$ at $b$. A further $e_p/3$ powers remain at each pole and can be used for differentiating. We can upper bound (B) by summing over all choices of $b$ before summing the weights. Their absolute sum for a fixed $I$ is at most $(2/k)^h$.

For the normalized derivative at $m=n$, differentiating the powers costs at most $9h/4$ in this bound. For $|p|=1$, the cost $e_p/n$ is at most one. For $|p|\ge3$, $|z_p'/z_p|\le|p|\rho_p$ and
$$
\frac{e_p}{n}|p|\rho_p^{1+e_p/3}
\le \frac{6|p|}{n(p^2-1)S^2}\le\frac94
$$
by Bernoulli's inequality with exponent $e_p/6\ge1$. Each differentiated inverse denominator has relative magnitude $\rho_q/S$, since it equals $(\cot\theta+iq)/(i(q-a))$. Thus differentiation of the denominators costs at most $(h-1)/(nS)$, giving total normalized derivative cost below $5h/2$. These bounds apply to the finite-degree coefficient for each finite set and pass to the full pole sum by local absolute convergence.

## Uniform summation of the partial fractions

For $\lambda\ge 8$ use $(1+x)^{\lambda/2}\ge(1+(\lambda/4)x)^2$. For $|p|\ge3$, $p^2-1\ge8p^2/9$. Monotone integral comparison for the positive odd integers, then reflection, gives
$$
\sum_p\rho_p^\lambda\le2+\frac{3\pi}{4\sqrt2}\frac1{S\sqrt\lambda}.
$$
Therefore $\sum_p w_p\le2+4D_0$, and $V_h=\sum_p\rho_p^{m/(3h)}\le 2+4\sqrt h\le6h$ for $mS^2\ge2/3$ and $h\le m/k$. For each odd $a$ split the sum of $w_q/|q-a|$ at distance $2\lceil2D_0\rceil$. The near terms are bounded by the harmonic sum through $\lceil2D_0\rceil$, and the far ones by $(2+4D_0)/(4D_0)$. Hence $\sum_{q\ne a}w_q/|q-a|\le U$.

In summing (B), the part $a=b$ costs at most $V_h U^{h-1}/(h-1)!$ after omitting $S^{1-h}$. For $b\ne a$, first sum the $h-2$ remaining poles for fixed $a,b$. The sum of $w_a/|a-b|$ over $a\ne b$ is at most $U$ for each $b$, and $\sum_b\rho_b^{m/(3h)}w_b\le V_h$. This gives at most $V_h U^{h-1}/(h-2)!$. Keeping the largest exponent at some pole is important here, since otherwise $V_h$ would depend on $n/k$. The two bounds together are $h V_h U^{h-1}/(h-1)!$.

Put $\eta=2U/(kS)\le1/1000$. Since $h^2\le 4^{h-1}$ and $h^3\le8^{h-1}$,
$$
|R_m|\le \frac{12}{k}\frac{4\eta}{1-4\eta}<\frac1{20k},\qquad
\frac{|R'_n|}{n}\le \frac{30}{k}\frac{8\eta}{1-8\eta}<\frac1{4k}. \tag{C}
$$
All remaining poles and every number of cycles are included.

## Applying the old-root insertion comparison

For $n\ge100$, $nS^2\ge1$ the ordinary single-pole tail obeys $\sum_{p=3,5,\ldots}p\rho_p^n<1/10$, by equation (6) of the [first two-cycle boundary argument](first-lag.md). Thus $|B_n-2\cos(n\theta)|<1/15$ and $|B'_n/n+2\sin(n\theta)|<1/5$. With $1/(2k-1)\le d_n\le1/k$ and (C), the total value error is below $(1/15+1/20)/k$ and the derivative error below $(1/5+1/4)/k$. This gives the integer samples and, at every old zero, $|\cos(n\theta)|<7/60$, $|\sin(n\theta)|>19/20$, and $|F'_n|>n/(2k)$.

At a zero of $F_n$ the normalized insertion contributions are $S F'_n$ and $B_k F_m$ where $m=n+1-k$. If $mS^2\ge2/3$ and $m\ge k$, the absolute sum bound above at $\lambda=m$ yields $|B_m|\le2+3\pi\sqrt3/8< 4.1$. Thus $|F_m|<5/k$. Also
$$
\frac{|B_k|}{nS}\le \frac2{nS}+\frac{3\pi}{4\sqrt{2k}\,nS^2}
\le \frac{2}{2000}+\frac{3\pi}{4\sqrt{4000}}<\frac1{10},
$$
using $n\ge k$, $kS\ge2000$ and $nS^2\ge1$. Consequently $|B_kF_m|<nS/(2k)<S|F'_n|$.

Taking $k\ge2000\sqrt n\,[3+\log(3\sqrt{n/k})]$ suffices for (A) throughout $nS^2\ge1$. This is an explicit effective but conservative condition. It leaves the intermediate threshold regime open. The [front estimate](effective-front.md) supplies the exterior roots. The [combined theorem](effective-threshold.md) counts the roots across the overlap. [Independent agent-assisted review](review-separated-poles.md)
