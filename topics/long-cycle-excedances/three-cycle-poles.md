# Old-root insertion bounds through the three-cycle band

Let $E_{n,k}$ count excedances of permutations whose cycles all have length at least $k$, and put $P_n=E_{n,k}/t$. For every $k\ge3$ and $n\ge10{,}000$ with $3k-1\le n<4k$, both signs of the distinguished-cycle term preserve the derivative contribution's sign at every old negative root. The old and positive-insertion new rows have simple negative roots and strictly interlace. At $n=4k-1$, the new row can have four cycles. The proof does not expand that new row.

This extends the two-cycle theorem from the first three-cycle transition. It reaches the $10{,}000$ cutoff of the existing general exterior proof throughout this band. For instance, at $(n,k)=(10000,3000)$ the theorem applies. Neither the two-cycle theorem nor either hypothesis in the existing effective-uniform route applies to that pair. The old and new rows in that example have degrees $9998$ and $9999$. [Two-cycle theorem][two] · [Effective uniform theorem][uniform] · [Tracking issue][issue]

The stronger cutoff $n\ge2{,}200$ uses the pole expansion below, sharper middle estimates and a separate exterior argument. [Stronger theorem and independent review](three-cycle-2200.md)

## Occupied poles

For $t=-\exp(-\pi\cot\theta)$ with $0<\theta\le\pi/2$, put $S=\sin\theta$, $r=\pi/S$, $z_p=(\cos\theta+ipS)^{-1}$, and $\rho_p=|z_p|$ for odd integers $p$. Define $B_j=\sum_p z_p^j$ and $F_j=r^j E_{j,k}(t)/(j!(1-t)^j)$. The exact Eulerian pole expansion gives

$$
\sum_{j\ge0}F_j u^j=\prod_{p\text{ odd}}D(z_p u),\qquad
D(u)=\exp\left(\sum_{j\ge k}\frac{u^j}{j}\right)=\sum_{j\ge0}d_j u^j .
$$

The numbers $d_j$ for $j\ge k$ satisfy $1/(2k-1)\le d_j\le1/k$. Let $g_j=d_j$ for $j\ge k$ and $g_j=0$ below $k$, and put $b_j=g_j-g_{j-1}$. The established variation bound is $\sum_j|b_j|<2/k$. [Product formula and variation input][separated] · [Variation proof][variation]

Put $m=n+1-k$, so $2n/3\le m\le n$. For $M=n,m$ write $F_M=d_MB_M+R_M$. Only occupied sets of sizes $h=2,3$ contribute to $R_M$ since $4k>n$. For a fixed set $I$, expand each nonconstant factor as $(\sum_{s\ge k}b_s z_p^su^s)/(1-z_pu)$. For fixed numerator indices with $\sum s_p\le M$, taking the coefficient gives the following partial fractions, multiplied by $\prod_{p\in I}b_{s_p}$:

$$
\sum_{a\in I}\left(\prod_{p\in I}z_p^{e_p}\right)
  \prod_{q\in I\setminus\lbrace a\rbrace}(1-z_q/z_a)^{-1},
\qquad e_a=s_a+M-\sum_{p\in I}s_p,\quad e_p=s_p\quad(p\ne a).
$$

Every exponent is at least $k$ and they sum to $M$. We have $|1-z_q/z_a|=|q-a|S\rho_q$. Define $w_p=\rho_p^{k-1}$ and, for $h=2,3$, define

$$
U_h=\sum_{|I|=h}\left(\prod_{p\in I}w_p\right)
       \sum_{a\in I}\prod_{q\ne a}\frac1{|q-a|},
\qquad
V_h=\sum_{|I|=h}\left(\max_{p\in I}|p|\right)
       \left(\prod_{p\in I}w_p\right)
       \sum_{a\in I}\prod_{q\ne a}\frac1{|q-a|}.
$$

The products indexed by $q$ run through $I\setminus\lbrace a\rbrace$. Each partial fraction has an absolute bound obtained by keeping $w_p$ at every pole. After summing the numerator weights, this gives

$$
k|R_M|\le\sum_{h=2}^3\frac{2^hU_h}{(kS)^{h-1}}.
$$

For $M=n$, differentiating the powers costs at most $\max_{p\in I}|p|$ after division by $n$, because $|z_p'/z_p|\le |p|\rho_p$ and $\sum e_p/n=1$. The relative derivative cost for each inverse denominator is $\rho_q/S\le1/S$. Thus

$$
\frac{k|R_n'|}{n}
\le\sum_{h=2}^3\frac{2^h}{(kS)^{h-1}}
        \left(V_h+\frac{h-1}{nS}U_h\right).
$$

The estimates also justify the infinite sums and termwise differentiations. On compact subintervals of $\theta>0$, the factors $w_p$ and $|p|w_p$ have summable absolute envelopes proportional to $|p|^{1-k}$ and $|p|^{2-k}$. The indices $M$ and $k$ are fixed in each differentiation.

## Rational pole bounds

Assume $nS^2\ge6/5$. Let $K(p)=1+(p^2-1)/160$. The function $(1+x/n)^n$ increases for fixed $x\ge0$, so for $n\ge192$,

$$
\rho_p^{k-1}\le K(p)^{-23},\qquad
\rho_p^n\le K(p)^{-96},\qquad
\rho_p^m\le K(p)^{-64}.
$$

Here $k>n/4$ implies $(k-1)/2\ge23n/192$ in this range and $m\ge2n/3$. For an envelope $K^{-h_0}$, retain the odd poles with $|p|\le9$. The omitted mass and absolute first moment are bounded respectively by $Q/9$ and $Q$, where

$$
Q=\frac{K(9)^{1-h_0}}{2(1/160)(h_0-1)} .
$$

Indeed the summand $pK(p)^{-h_0}$ decreases for $p\ge9$, and the positive odd lattice beyond nine is bounded by half the corresponding integral from nine. Reflection supplies the other half. Bounding the mass by one ninth of the moment gives the first bound.

For the omitted occupied sets use $|q-a|\ge2$. If $a_0,a_1$ bound total mass and absolute first moment, and $b_0,b_1$ bound the corresponding tails, their contributions to $U_h,V_h$ are at most

$$
\frac{h b_0a_0^{h-1}}{(h-1)!2^{h-1}},\qquad
\frac{h b_1a_0^{h-1}+h(h-1)b_0a_1a_0^{h-2}}{(h-1)!2^{h-1}} .
$$

To see this, replace each unordered set by its ordered lists with the distinguished pole first and drop distinctness after bounding all denominators. Use a union bound over the position of an omitted pole. For $V_h$, bound the maximum by the sum of the absolute pole indices and distinguish whether its chosen index is the tail index. These estimates give the rational bounds

$$
U_2<53/25,\quad V_2<457/100,\qquad U_3<43/100,\quad V_3<7/5.
$$

The same envelopes give $|B_k|<11/4$, $|B_m|<21/10$, and the following old principal-pair errors:

$$
|B_n-2\cos(n\theta)|<1/50,\qquad
|B_n'/n+2\sin(n\theta)|<1/16 .
$$

For the derivative use $|z_p'/z_p|\le |p|$. These are exact rational computations from the finite sums and tail formulas. [Checker](check-three-cycle-poles.py) · [Output](three-cycle-poles-output.txt)

## The comparison at old roots

Put $A=kS$. Our band and $nS^2\ge6/5$ give $A\ge27$, since $k>n/4$ and $n\ge10{,}000$. Also $nS\ge(29/10)A$, since $n\ge3k-1$ and $k\ge10$. The pole bounds give $k|R_M|<8/25$ and $k|R_n'|/n<7/10+9/1000$, where the last summand bounds the inverse-denominator cost.

At an integer sample $\theta=j\pi/n$, the sign of $F_n$ is $(-1)^j$, since $2kd_n\ge1$ and the total scaled value error from $2d_n\cos(n\theta)$ is less than $8/25+1/50=17/50$. At any old root in this region the same bound gives $|\cos(n\theta)|<17/50$. Thus $|\sin(n\theta)|>47/50$, and

$$
\frac{k|F_n'|}{n}>
\frac{47}{50}-\frac1{16}-\frac7{10}-\frac9{1000}
\gt\frac4{25}.
$$

At an old zero, the derivative contribution and lag equal $S F_n'$ and $B_kF_m$ times the same factor $n!(1-t)^{n+1}/(t r^{n+1})$. This is the general insertion normalization from the [central interval][central]. The lag obeys

$$
\frac{k|B_kF_m|}{nS}<
\frac{(11/4)(21/10+8/25)}{(29/10)27}
<\frac9{100}.
$$

This is strictly smaller than the derivative lower bound in the same units. Both signs of the insertion preserve the sign of $x(1-x)P_n'(x)$ at every central old root.

## Joining the exterior and central ranges

The established front-root theorem at $n\ge10{,}000$ gives $H=\lfloor7\sqrt n/20\rfloor$ simple negative roots at each exterior end, the old-root lag inequality at all of them, and separation from the first middle sample of index $H+1$. At that sample $n\sin^2((H+1)\pi/n)>6/5$ by the sine estimate in the effective-threshold theorem. Thus the preceding argument supplies the sample signs and lag inequality through the middle. Reciprocity reflects it to the second half. The samples $H+1,\ldots,n-H-1$ have $n-2H-2$ sign-changing intervals, disjoint from the exterior roots. Together they exhaust the degree $n-2$. At these old roots both insertion signs give alternating signs in the next row. Its constant and leading coefficients equal one for either sign since the lag is supported strictly between the endpoints. The outside intervals and the consecutive old-root gaps therefore supply $n-1$ distinct simple negative next roots. [Exterior theorem][front] · [Sample location][threshold]

The finite complement $n<10{,}000$ in the three-cycle band is left open by this argument. The rational estimate by occupied-set cardinality has a direct extension to any fixed upper bound on $n/k$: retain the additional values of $h$ and enlarge the pole envelopes as needed. With $n/k$ unbounded the number of occupied sets and the tail norms grow, and the above constants do not cover that regime.

## Verification

The written proof and rational estimates received an independent agent-assisted review. Run the checker from this directory using Python 3 and its standard library.

~~~sh
python3 -IB check-three-cycle-poles.py
~~~

Its output must match the [recorded rational bounds](three-cycle-poles-output.txt). The checker certifies the common bounds for the band. It does not enumerate root locations. **Formal verification**　⬜ None. [Independent review](review-three-cycle-poles.md)

[two]: two-cycle-band.md
[uniform]: effective-uniform.md
[central]: central-interval.md
[separated]: separated-poles.md
[variation]: cycle-probability-variation.md
[front]: effective-front.md
[threshold]: effective-threshold.md
[issue]: https://github.com/ProgramComputer/open-math-research/issues/4
