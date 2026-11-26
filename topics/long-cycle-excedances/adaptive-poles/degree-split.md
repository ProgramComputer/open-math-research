# Retaining the distinguished pole at larger aspect

This sharpens the [full-minimum-powers estimate](full-powers.md) for the larger aspect slabs while retaining its smallest-aspect row cutoffs. Fix $x=n/k\in[\ell,X]$ as in the table, $k\ge1000$, and $0<\theta\le\pi/2$, with $t=-\exp(-\pi\cot\theta)$, $S=\sin\theta$, $nS^2\ge6/5$, and $A=kS$. At the integer old phase samples the sign is $(-1)^j$ for $F_n$. At every real old root in this interval the derivative contribution $t(1-t)P_n'(t)$ keeps its sign under either insertion lag sign, at the indicated thresholds for $A$.

| Aspect interval | Minimum $A$ | Sufficient old row size | Bound |
| --- | ---: | ---: | --- |
| $4\le x\le5$ | 17 | 10,000 | Full powers |
| $5\le x\le6$ | 20 | 12,000 | Full powers |
| $6\le x\le7$ | 23 | 21,601 | Full powers |
| $7\le x\le8$ | 26 | 36,054 | Full powers |
| $8\le x\le9$ | 29 | 56,768 | Full powers |
| $9\le x\le10$ | 32 | 85,334 | Full powers |
| $10\le x\le12$ | 39 | 182,520 | Full powers |
| $12\le x\le15$ | 49 | 450,188 | Full powers |
| $15\le x\le20$ | 54 | 972,000 | Degree split |
| $20\le x\le25$ | 43 | 963,021 | Degree split |
| $25\le x\le32$ | 37 | 1,168,214 | Degree split |
| $32\le x\le40$ | 30 | 1,200,000 | Degree split |
| $40\le x\le50$ | 26 | 1,408,334 | Degree split |
| $50\le x\le64$ | 24 | 1,966,080 | Degree split |
| $64\le x\le80$ | 23 | 2,821,334 | Degree split |
| $80\le x\le96$ | 23 | 4,062,720 | Degree split |
| $96\le x\le100$ | 23 | 4,408,334 | Degree split |
| $100\le x\le125$ | 24 | 7,500,000 | Degree split |

## Degree restrictions and derivative weights

Use $F_M,R_M,w_p,W,W_1,U$ as in the [full-minimum-powers estimate](full-powers.md). Write $m=n+1-k$, and take $M=n$ or $m$. In each partial fraction term, let $T$ be the sum of the non-distinguished numerator degrees $s_q$. The distinguished factor retains exponent $M-T\ge k$. We divide the sum into $T\le M/2$ and $T>M/2$ after forming the partial fractions. All the following summations are of absolute values.

The cycle-probability block bound for $b_s$ from the [signed-pole proof][signed] gives

$$
\sum_s s|b_s|\le 2e<6,
\qquad
\sum_s |b_s| e^{s/(4k)}<5/k,
\qquad
\sum_s s|b_s|e^{s/(4k)}<11.
$$

For completeness, $b_k=1/k$ and the maximum of $|b_s|$ on $jk<s\le(j+1)k$ is at most $1/(j!k^2)$ for $j\ge1$. The recurrence $sb_s=-\sum_{i=s-k+1}^{s-1}b_i$ gives the successive factorial decay, after the first block is checked directly. For general $c\ge0$ this bounds the zeroth and first exponentially weighted moments by $e^{c+e^c}/k$ and $e^{c+e^c}(1+e^c)$, respectively. The checker uses rational Taylor bounds at $c=0,1/4$ for the asserted comparisons.

When $T\le M/2$, the distinguished factor retains $M/2$ powers. Since $MS^2\ge(1-1/\ell)nS^2$ and $M/4\ge96$, it has the new envelope

$$
\rho_a^{M/2}\le v_a=
\left(1+\frac{\ell-1}{320\ell}(a^2-1)\right)^{-96}.
$$

Write $V_0=\sum_a v_a$ and $V_1=\sum_a |a|v_a$. These sums use the same monotone integral tail and dyadic rounding as the base checker. For both $M$, this envelope also bounds $|B_M|$ by $V_0$.

Let $d=1/(\ell A)$, $y_s=2U/A$ and $e_s=y_s/(1-y_s)$. The normalized short-degree value contribution is bounded by $V_0 e_s$. For the derivative at $M=n$, a differentiated distinguished power divided by $n$ costs at most $|a|$. A differentiated non-distinguished power starts with exponent $s_q-1$. By retaining that degree factor until summing over $s_q$, it contributes a factor at most $6d|q|w_q/|q-a|$. The bound uses $nS\ge\ell A$ and the unweighted first numerator moment above. Summing the marked $q$ costs at most $V_0 W+V_1 U$, since $|q|\le|q-a|+|a|$. In the denominators each angular derivative costs at most $1/(nS)\le d$. The ordered-tuple bound on the unmarked additional poles then gives the normalized short-degree derivative bound

$$
D_s=V_1 e_s+d\left(6(V_0W+V_1U)+y_sV_0\right)(1+e_s).
$$

In this count, marking an additional pole changes a coefficient denominator $h!$ to $(h-1)!$. The same count handles the derivative of one denominator. Both are upper bounds because repetitions can be retained after taking absolute values.

When $T>M/2$, apply the exponential numerator weight and return a common penalty $e^{-M/(8k)}\le e^{-(\ell-1)/8}$. Let $\epsilon$ be the rational upper bound on the last exponential obtained by reciprocating a positive Taylor partial sum. In this part the distinguished pole retains at least $k$ powers, so use $w_a$ in place of $v_a$. Put $y_l=5U/A$, $e_l=y_l/(1-y_l)$. Before multiplication by $\epsilon$, the value cost is bounded by $We_l$ and the derivative cost by

$$
D_l=W_1e_l+d\left(11(W^2+W_1U)+y_lW\right)(1+e_l).
$$

The derivative formula uses the weighted first numerator moment and is otherwise the same marked-factor count. The estimates only use $y_s,y_l<1$, checked at each chosen threshold. Including all occupied orders as geometric majorants is valid. There is no truncation on their actual count.

## Sign and scalar joins

In the degree-split estimate put

$$
R=V_0 e_s+\epsilon We_l,\qquad D_*=D_s+\epsilon D_l,\qquad
I=W(V_0+R)d.
$$

These give $k|R_M|\le R$, $k|R_n'|/n\le D_*$, and $k|B_kF_m|/(nS)\le I$. The respective old single-pole errors are below $1/50$ and $1/16$. Since $2kd_n>1$, the exact inequality

$$
(R+1/50)^2+(D_*+I+1/16+1/100)^2<1
$$

implies the old sample signs and the strict comparison at every middle old zero. These upper bounds decrease as $A$ increases for fixed interval endpoints. The exterior join and reciprocity give the row cutoff $\max(10000,1000X,\lceil5(XA)^2/6\rceil)$ displayed in the table.

The exact scalar checks also give the following overlaps with a separately established short-cycle criterion of the form $0.89n/k>47+2.5\log n$. For $4{,}062{,}720\le n<4{,}408{,}334$, use the bounded-aspect result for $x\le96$ and the short criterion for $x\ge96$, since $\log(4{,}408{,}334)<15.3$. For $4{,}408{,}334\le n<7{,}500{,}000$, the corresponding boundary is 100, using $\log(7{,}500{,}000)<16$. For $7{,}500{,}000\le n<250000^2$, the boundary is 125, using $\log(250000^2)<25$. The claims about all thresholds additionally require the separate short-cycle criterion in its stated range, the estimate for small $k$ and the all-threshold comparison above $250000^2$.

Run `python3 -B check_degree_split.py` for exact lattice, Taylor and squared-sign comparisons. The [recorded output](degree-split-output.txt) identifies the bound selected in each interval. The actual next row and the opposite insertion sign are both treated by the bounded-aspect result.

[signed]: ../uniform-hilbert/README.md
