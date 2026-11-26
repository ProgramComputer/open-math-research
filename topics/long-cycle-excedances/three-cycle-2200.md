# A lower cutoff for the three-cycle band

For fixed threshold $k$, write $P_n(t)=E_{n,k}(t)/t$ for the excedance polynomial with the forced zero removed. For $k\ge3$ and $n\ge2{,}200$ with $3k-1\le n<4k$, the polynomials $P_n$ and $P_{n+1}$ have simple negative roots and strictly interlace. At every old root both signs of the distinguished insertion term preserve the sign of the derivative contribution $x(1-x)P_n'(x)$. In particular the next row may have four cycles at $n=4k-1$. The proof uses the occupied-pole expansion and root-count argument from the [earlier cutoff at $10{,}000$](three-cycle-poles.md). The exact scalar calculation is in [the checker](check-three-cycle-2200.py) and [its output](three-cycle-2200-output.txt).

## Coefficient envelopes

Write $M=n-1$. For any row of size $N\ge1000$ with $N<4k$, define $\alpha_{N,p}=[t^p]E_{N,k}/p^{N-1}$ for $p\ge1$. Then $\alpha_{N,p}\le21/4$ for every $p$. For the old row one also has $\alpha_{n,p}\ge99/100$ whenever $p\le(103/250)\sqrt M$.

For the lower bound use the single-cycle contribution. Assign each label of a word to its run color. If each color occurs on both halves of the label set, concatenating the sorted color classes gives a descent at every boundary. This yields the lower bound $1-2p\exp(-\lfloor M/2\rfloor/p)$, at least $99/100$ in the stated range. For instance $\lfloor M/2\rfloor/p\ge(6/5)\sqrt M$ and $2p<\sqrt M$ for $M\ge2199$, and $x e^{-6x/5}$ decreases for $x\ge46$. The one-cycle term is at most one since a word determines the permutation's sorted runs.

For $j=2,3$ cycles, write $p_i$ for the positive run counts with sum $p$. Using the word upper bound for each cycle and summing over cycle lengths gives the following upper bound for their contribution to $\alpha_{N,p}$:

$$
\frac1{j!}\sum_{p_1+\cdots+p_j=p}\frac{p}{\prod_i p_i}
\mathbb P\lbrace \text{each of the multinomial counts with probabilities }p_i/p\text{ is at least }k\rbrace.
$$

For a tuple having a run proportion below $1/6$, its corresponding count must exceed its mean by at least $N/12$, since $k>N/4$. The probability is at most $e^{-N/72}$ by Hoeffding. For all tuples, the bare weights sum to at most $H_{p-1}$ for $j=2$ and $H_{p-1}^2/2$ for $j=3$, where $H_b$ is a harmonic number. This follows by writing $p/\prod_i p_i$ as the sum of the $j$ products omitting one reciprocal. Indices $p\ge N$ have zero coefficient. Since $1+\log N\le\sqrt N$ for $N\ge1000$, the combined discarded part is less than $N e^{-N/72}<1/100$. The latter decreases there and follows at $1000$ from $e^3>20$.

For tuples with all proportions at least $1/6$, put $a=\lceil p/6\rceil$. The weight sums are at most $\sum_{j=a}^{p-a}1/j$ and $\frac12\sum_{j=a}^{p-2a}\sum_{l=a}^{p-a-j}1/(jl)$, respectively. They are at most $23/10$ and $19/10$. For $p\le24$ the checker verifies these rational sums. For $p\ge25$, integral comparison gives $6/p+\log 5$ and $(6/p+\log4)^2/2$ as upper bounds. Adding the one-cycle term and the two discarded contributions gives less than $21/4$.

## Exterior roots and the join

Take $H=\lfloor(39/100)\sqrt M\rfloor$ and $1\le h\le H$. Set $\alpha_p=\alpha_{n,p}$, $\rho=\alpha_h/\alpha_{h+1}$, $u=\rho(h/(h+1))^M$, and

$$
F(z)=\frac{E_{n,k}(uz)}{\alpha_h h^M(uz)^h},
\qquad
b_p=\left(\frac ph\left(\frac h{h+1}\right)^{p-h}\right)^M.
$$

The central terms of $F$ are exactly $1,z$. We have $h+1<(103/250)\sqrt M$ and $\rho,\rho^{-1}<R=16/3$ by the coefficient bounds. On either side of the central pair, consecutive ratios of $b_p$ away from it are at most $q=\exp(-M/(h+1)^2)<1/360$. Indeed the right and left bases at the immediate tails are $1-1/(h+1)^2$ and $1-1/h^2$, and all further ratios decrease. The left side is empty for $h=1$. For $q\max(|\rho z|,1/|\rho z|)\le s$, the left and right tails of $F$ at distance $l\ge1$ from their central terms are bounded respectively by $Rs^l$ and $R|z|s^l$.

Use $s=1/50$ on $|z+1|=1/4$, and $s=9/200$ on $|z|=1/2$ or $3$. The bounds $R(1+|z|)s/(1-s)$ for the tail sum are strictly less than $1/4$, $1/2$, and $2$ on the three circles respectively. Apply Rouché to the polynomial $z^{h-1}F(z)$. Its root count is one in the first disk, $h-1$ inside the half-radius circle, and $h$ inside the radius-three circle, since these are the counts for $z^{h-1}(1+z)$. The first disk is contained in the resulting annulus, so its unique root is real by conjugation, simple, and of absolute rank $h$.

At this root write $x=uz$ and $X=|x|$. Differentiation first gives $xE_{n,k}'(x)/(\alpha_h h^M x^h)=hF(z)+zF'(z)$. Since $F(z)=0$, the identity $xE_{n,k}'(x)/(\alpha_h h^M x^h)=zF'(z)-F(z)$ gives central contribution $-1$. The tail terms acquire weights $l+1$ on the left and $l$ on the right. Using $|z|<5/4$ and $s=1/50$ bounds their sum by $R[(9/4)s/(1-s)^2+s/(1-s)]$. Hence

$$
|xE_{n,k}'(x)|>(63/100)\alpha_h h^M X^h.
$$

For the insertion $L=\binom n{k-1}A_{k-1}E_{m,k}$, where $m=n+1-k$, the old and residual polynomials both have at most three cycles and $m\ge 2n/3$. Apply the coefficient bound $21/4$ to $E_{m,k}$ and the word upper bound to $tA_{k-1}$. After dividing by $p^M$, the convolution coefficient of $tL$ is bounded by $(21/4)(n/m)$ times the sum of binomial point masses at $k-1$ for $\mathrm{Bin}(M,j/p)$ over $1\le j<p$.

The factor $n/m$ is $\binom n{k-1}/\binom M{k-1}$. Set $a=(k-1)/M$. The point mass is maximal at parameter $a$. Stirling's upper bound for $M!$ and lower bounds for $(k-1)!$ and $(M-k+1)!$ bound this maximum by $e^{1/(12M)}/\sqrt{2\pi M a(1-a)}$. Here $249/1000<a\le1/3$ and $a(1-a)>18/100$, so the maximum is less than $(95/100)/\sqrt M$. Relative to the maximum, the point mass at parameter $b$ is $e^{-M D(a\Vert b)}\le e^{-2M(a-b)^2}$ by the second derivative of Bernoulli relative entropy in its first argument.

Extend the Gaussian sum to all integers $j$ and set aside the term at a point $j_0/p$ nearest to $a$. Its value is at most one. Each remaining term is at most $p$ times the integral of the Gaussian over the adjacent interval toward $j_0/p$. Throughout that interval the distance to $a$ is at most the distance at the outer endpoint. This holds also for the interval crossing $a$, because $j_0/p$ is a nearest lattice point. The intervals have disjoint interiors, so the full sum is at most $1+\sqrt{\pi/2}\cdot p/\sqrt M$. Thus the coefficient bound for the lag is

$$
[t^p]\bigl(tL\bigr)\le \frac{(21/4)(3/2)(95/100)}{\sqrt M}\cdot p^M
\left(1+\sqrt{\pi/2}\frac p{\sqrt M}\right).
$$

In the scale $\alpha_h h^M X^h$, the weights $p^M X^p$ are bounded by $(100/99)s^l$ on the left ($p=h-l$) and $(100/99)(5/4)s^l$ on the right ($p=h+1+l$), including $l=0$. The factor in parentheses is at most $1+(63/50)(103/250)$ through $h+1$ and grows by less than $3/100$ per step thereafter. The geometric sum with this factor is below $18/5$ as checked. This proves $|xL(x)|<(58/100)\alpha_h h^M X^h$. At an old root $xP_n'(x)=E_{n,k}'(x)$, so $|L|<|x(1-x)P_n'|$ follows.

All $H$ front roots lie before the first middle sample with $\theta_*=(H+1)\pi/n$. Their moduli are less than $(5/4)R(H/(H+1))^M$ and

$$
M\log(1+1/H)-\frac{n}{H+1}
\ge\frac{M}{2(H+1)^2}-\frac1{H+1}
\gt 2\gt \log((5/4)R).
$$

Use $\pi\cot\theta_*<n/(H+1)$ to conclude. With $b=(39/100)\pi\sqrt{n-1}/n<\theta_*$, the checker uses $b^2<2/n$ and $\sin b\ge b-b^3/6$ to obtain $n\sin^2\theta_*>149/100$.

## Sharpened middle comparison

Use the notation and partial fractions of [the companion proof](three-cycle-poles.md). It suffices to describe the changes, all of which apply at every angle with $nS^2\ge149/100$.

First, when $h=2$ every numerator index $s_p$ is at most $M_*-k\le3k-1$, where $M_*$ denotes either $n$ or $m$. For $h=3$ it is at most $M_*-2k\le2k-1$. From $g_k=1/k$ and $d_j=1/j$ for $k\le j<2k$, the absolute numerator mass through $2k-1$ is below $3/(2k)$. Write $c_0=1/k-1/(2k-1)$. The jump at $2k$ has magnitude $c_0/(2k)$ by the cycle recurrence. For $2k<j<3k$, that recurrence gives $j|d_j-d_{j-1}|=|d_{j-k}-d_{j-1}|\le c_0$, using the pointwise bounds in the companion proof. Consequently the absolute mass through $3k-1$ is at most

$$
\frac1k+c_0\left(1+\frac1{2k}+\log(3/2)\right)<\frac7{4k}.
$$

The last inequality uses $c_0<1/(2k)$, $k\ge10$, and $\log(3/2)<5/12$ by the alternating series. Thus the partial fraction bounds use $(7/4)^2$ and $(3/2)^3$ in place of $2^2$ and $2^3$ for their respective summands.

Second, for the occupied set $\lbrace -1,1\rbrace$, the logarithmic derivative of the power product divided by $n$ has absolute value $|e_{1}-e_{-1}|/n\le 1-2k/n<1/2$. Here $z_1=e^{-i\theta}$, $z_{-1}=e^{i\theta}$, both exponents are at least $k$, and their sum is $n$. Use $1/2$ for this set in the derivative moment. All other sets keep the absolute maximum bound from the companion proof.

Finally replace $K(p)$ by $1+(149/100)(p^2-1)/192$. The same envelope exponents $23,96,64$ apply and $A=kS\ge14$, $nS\ge(29/10)A$. Let $E$ and $D$ denote the upper bounds on the scaled value error and scaled derivative error relative to $2d_n\cos(n\theta)$ and $-2d_n\sin(n\theta)$, respectively, including both the occupied-pole and far single-pole terms. Let $J$ bound $k|B_kF_m|/(nS)$. The checker, using the same finite sums through nine and integral tails, gives $1-E^2>(19/100+D)^2$ and $J<16/100$. In particular $E<1$, so the integer sample signs are $(-1)^j$. At an old zero $|\cos(n\theta)|<E$ and $k|F_n'|/n>19/100$, using $2kd_n\ge1$. In the common insertion scaling this exceeds the lag bound $16/100$. Reflection, degree exhaustion, and both outside next intervals finish exactly as in the companion proof.

This leaves the remainder $3k-1\le n<\min(4k,2200)$ for sharper estimates or exact verification.

## Verification

An independent reviewer checked the coefficient envelope, uniform lattice estimate, exterior join, and rational pole bounds. **Formal verification**　⬜ None. [Independent review](review-three-cycle-2200.md)

From this directory, run the standard-library checker with Python 3.

~~~sh
python3 -IB check-three-cycle-2200.py
~~~

Its two lines must match the [recorded output](three-cycle-2200-output.txt).
