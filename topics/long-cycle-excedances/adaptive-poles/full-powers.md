# Exact pole-star comparison through aspect 125

Let $E_{n,k}(t)$ count excedances over permutations with minimum cycle length $k$, and put $P_n=E_{n,k}/t$. For $x=n/k$ in an interval in the table, assume $k\ge1000$. At every old real zero with $n\sin^2\theta\ge6/5$ and $A=k\sin\theta$ at least the displayed threshold, the derivative contribution $t(1-t)P_n'(t)$ keeps its sign under either insertion lag sign. The old integer phase samples in this interval have sign $(-1)^j$ for the normalized old $E_{n,k}$ at $\theta=j\pi/n$. In particular, $4\le n/k\le125$ and $n\ge3{,}000{,}000{,}000$ suffice for strict consecutive interlacing. The row cutoffs below give the same conclusion at smaller sizes in the indicated aspect ranges.

| Aspect interval | Minimum $A$ | Sufficient old row size |
| --- | ---: | ---: |
| $4\le x\le5$ | 17 | 10,000 |
| $5\le x\le6$ | 20 | 12,000 |
| $6\le x\le7$ | 23 | 21,601 |
| $7\le x\le8$ | 26 | 36,054 |
| $8\le x\le9$ | 29 | 56,768 |
| $9\le x\le10$ | 32 | 85,334 |
| $10\le x\le12$ | 39 | 182,520 |
| $12\le x\le15$ | 49 | 450,188 |
| $15\le x\le20$ | 66 | 1,452,000 |
| $20\le x\le25$ | 83 | 3,588,021 |
| $25\le x\le32$ | 108 | 9,953,280 |
| $32\le x\le40$ | 138 | 25,392,000 |
| $40\le x\le50$ | 175 | 63,802,084 |
| $50\le x\le64$ | 230 | 180,565,334 |
| $64\le x\le80$ | 294 | 460,992,000 |
| $80\le x\le100$ | 375 | 1,171,875,000 |
| $100\le x\le125$ | 480 | 3,000,000,000 |

## Absolute partial fractions with full minimum powers

Take $0<\theta\le\pi/2$, $t=-\exp(-\pi\cot\theta)$, $S=\sin\theta$, $C=\cos\theta$, $z_p=(C+ipS)^{-1}$, $\rho_p=|z_p|$ with odd integer $p$, and $r=\pi/S$. Put $F_M=r^M E_{M,k}(t)/(M!(1-t)^M)$ and $B_M=\sum_p z_p^M$. The exact product is $\sum_M F_Mu^M=\prod_p D(z_pu)$, where $D=\sum_jd_ju^j$ is the cycle-probability series. Write $D(u)-1=\sum_{s\ge k}b_su^s/(1-u)$, so $\sum_s|b_s|<2/k$ and $1/(2k-1)\le d_j\le1/k$ for $j\ge k$. [Pole expansion and partial fractions][poles] · [Variation bound][variation]

For $x\in[\ell,X]$, the hypotheses imply $(k-1)S^2\ge(999/1000)(6/(5X))$. Bernoulli gives, for every odd $p$,

$$
\rho_p^{k-1}\le w_p
=\left(1+\frac{999}{160000X}(p^2-1)\right)^{-96}.
$$

For $M=n$ or $M=n+1-k$, set $R_M=F_M-d_MB_M$. Choose the distinguished pole $a$ in the partial fraction expansion, with $h\ge1$ additional poles $q\ne a$. In each term the additional numerator degrees $s_q$ satisfy $s_q\ge k$, their sum is $T$, and the distinguished pole retains exponent $M-T\ge k$. The coefficient absolute value is bounded using $d_{M-T}\le1/k$ and the factors

$$
\frac{|b_{s_q}|\rho_q^{s_q-1}}{|q-a|S}.
$$

Thus $k$ times its absolute sum is bounded by $w_a$ times the product of the factors $\alpha w_q/|q-a|$, where $\alpha=2/A$. We keep all $k-1$ powers at every pole. These estimates hold first in finite truncations, and the fixed-degree coefficient and angular derivative have locally absolutely convergent pole sums. The denominators and exponent bounds then permit the infinite positive majorants below.

Define

$$
\begin{aligned}
W&=\sum_a w_a, & W_1&=\sum_a |a|w_a, &
U&=\sup_a\sum_{q\ne a}\frac{w_q}{|q-a|},\\
T_1&=\sum_{a,q\ne a}\frac{w_aw_q}{|q-a|}, &
E_1&=\sum_{a,q\ne a}\frac{\max(|a|,|q|)w_aw_q}{|q-a|}, &
J_1&=\sum_{a,q\ne a}\frac{|q|w_aw_q}{|q-a|}.
\end{aligned}
$$

The case $h=1$ contributes at most $\alpha T_1$ to $k|R_M|$. For $h\ge2$, summing over the distinct poles by the ordered-tuple bound and dividing by $h!$ gives a total no greater than $W(e^{\alpha U}-1-\alpha U)$.

For the angular derivative at $M=n$, one has $|z_p'/z_p|\le|p|$ and the differentiated powers have total exponent at most $n$. At $h=1$, the derivative of all powers divided by $n$ costs at most $\max(|a|,|q|)$, as the normalized exponents sum to at most one. The denominator derivative costs at most $1/(nS)\le1/(\ell A)$. This gives $\alpha(E_1+T_1/(\ell A))$. For $h\ge2$ use $|a|+\sum_q|q|$ in place of the maximum. The distinguished-pole term sums to $W_1(e^{\alpha U}-1-\alpha U)$. Choosing one of the $h$ additional poles for the derivative cancels the factor $h$ from $h!$, so its total is at most $\alpha J_1(e^{\alpha U}-1)$. The denominators contribute at most $h/(\ell A)$ by the same counting, giving $\alpha T_1(e^{\alpha U}-1)/(\ell A)$. In all these estimates the larger sum over arbitrary ordered tuples is an upper bound, even though only distinct poles are occupied.

For $y=\alpha U<1$, write $e_1=y/(1-y)$ and $e_2=y^2/(2(1-y))$. These bound $e^y-1$ and $e^y-1-y$. The two error bounds are consequently

$$
V=\alpha T_1+W e_2,\qquad
J=\alpha(E_1+T_1/(\ell A))+W_1 e_2+\alpha(J_1+T_1/(\ell A))e_1.
$$

Here $k|R_M|\le V$ and $k|R_n'|/n\le J$. These bounds decrease as $A$ increases with fixed slab constants.

## Exact lattice bounds and old-root criterion

The code bounds the lattice sums using the finite poles $|p|\le P$ with $P=2\lfloor3\sqrt X\rfloor+3$. For $K(p)=1+999(p^2-1)/(160000X)$, the weighted tail $\sum_{|p|>P}|p|w_p$ is at most $K(P)^{-95}/(190c)$ with $c=999/(160000X)$. This follows by monotone integral comparison on the spacing-two lattice, followed by reflection. The unweighted tail is at most that bound divided by $P$. The checker verifies the weighted envelope is decreasing for $p\ge P$. For $U$, the truncated sum for $|a|>P$ is maximized at one of $a=\pm(P+2)$, by monotonicity of the distance from every retained pole. The remaining tail can cost at most half its unweighted mass. In each ordered-pair sum, the excess beyond finite pairs is bounded using $|q-a|\ge2$ and including both ways to select an exterior pole. For $T_1$ this costs $W$ times the unweighted tail. For $E_1$ or $J_1$ use $\max(|a|,|q|)\le|a|+|q|$, giving at most $W$ times the weighted tail plus $W_1$ times the unweighted tail. The finite weights and every division are rounded upward with an exact dyadic grid before further summation.

For the old row, the zeroth and first nonprincipal pole errors are respectively below $1/50$ and $1/16$ when $nS^2\ge6/5$. The checker replays these bounds by Bernoulli at exponent 96 and a monotone integral tail. The principal amplitude satisfies $2kd_n>1$. Thus the value error is at most $V+1/50$ and at an old root the normalized derivative magnitude exceeds $\sqrt{1-(V+1/50)^2}-J-1/16$.

In the common insertion normalization the lag is $B_k F_{n+1-k}$. Both $k$ and $n+1-k$ are at least $k$, so $|B_k|,|B_{n+1-k}|\le W$. Hence the lag on the $k/(nS)$ scale is bounded by $I=W(W+V)/(\ell A)$. The checker establishes at each tabulated threshold the strict inequality

$$
(V+1/50)^2+(J+I+1/16+1/100)^2<1.
$$

This gives the sample signs and the strict lag inequality for both insertion signs at every old root in the interval. The proof needs no maximum occupied order in its positive majorants. As before, reciprocity gives the corresponding statements on the other half-axis.

## The exterior join

For $n\ge10000$, the established exterior theorem gives the old roots before phase index $H+1$, where $H=\lfloor7\sqrt n/20\rfloor$, and gives the two insertion signs at these roots. At that index $nS^2>6/5$. Therefore $A>\sqrt{6n/5}/x$. In slab $[\ell,X]$ with threshold $A_0$, a sufficient row cutoff is

$$
\max\left(10000,1000X,\left\lceil\frac56(XA_0)^2\right\rceil\right).
$$

The middle sample brackets and the two exterior groups exhaust the old degree. The signed comparisons and the positive next extreme coefficients then give strict consecutive interlacing, as in the established exterior-middle join. [Exterior theorem][front] · [Root count][count]

Run `python3 -I -B check_full_powers.py` for the [exact arithmetic table](full-powers-output.txt). This result concerns bounded aspects through 125. An order-by-order absolute pole bound cannot extend it to unbounded aspect at fixed $A$. Indeed take $S=A/k$ and $n=\lceil(6/5)k^2/A^2\rceil$. In the two-pole terms, keep $a=1$, $s_q=k$, and odd $3\le q\le\sqrt{k}/A$. Then $\rho_q^{k-1}>1/2$, $b_k=1/k$, and $d_{n-k}>1/(2k)$. Their normalized absolute sum is at least $(4A)^{-1}\sum_q1/(q-1)$, which diverges as $k$ increases. A separate signed or residue comparison is needed at unbounded aspect.

[poles]: ../separated-poles.md
[variation]: ../cycle-probability-variation.md
[front]: ../effective-front.md
[count]: ../effective-threshold.md
