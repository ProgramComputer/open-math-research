# Coefficient inequalities at every size for ordered large-block partitions

Give each block of an ordered partition of $[n]$ a common weight $u\ge1$, and give it a further factor $t$ if its size is at least $j\ge2$. Write $P_n(t)=\sum_k a_{n,k}t^k$ for the enumerator. Alexandersson asks for real-rootedness and consecutive interlacing when $u=1$. The inequalities below apply at every size and every threshold. Formal verification is ⬜ None. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

**Theorem.** Let $x=n/j$ and $d=\lfloor x\rfloor$. For every $1\le k<d$,

$$
k(x-k)a_{n,k}^2>(k+1)(x-k+1)a_{n,k-1}a_{n,k+1}.
$$

Thus the sequence $a_{n,k}/\binom{x}{k}$ is strictly log-concave on its support. When $j$ divides $n$, these are the full strict Newton inequalities for the actual degree. For general $n$ the top parameter is $n/j$. The first quadratic row, at $n=2j$, has two distinct negative roots.

For nonnegative coefficient sequences let $U\preceq V$ mean $U_iV_k\ge U_kV_i$ for all $i<k$, using zero padding. With $n\le m\le n+j$,

$$
P'_m\preceq P_n\preceq P_m\preceq tP_n .
$$

For every fixed tilt $t>0$ there is a single coupling of the counts $X_n$ of large blocks, with the tilted law at every size, such that $X_n\le X_m\le X_n+1$ whenever $n\le m\le n+j$. Thus successive jumps have separation at least $j$. This coupling concerns the counts themselves.

Chengyi Fang's Theorem 8 establishes the derivative and likelihood comparisons for **unordered** set partitions using the exponential formula. The ordered family has a reciprocal generating function, and even its unmarked column fails log-concavity for $j\ge3$. We use a compound negative-binomial theorem to control powers of that column. The length-weighted comparison below supplies the extra factor in the fractional Newton inequality. The all-size root and interlacing problem remains open. [Fang, §8, printed pp. 15–16](https://hexagonmath.org/pdf/2611.01129v1#page=15) · [Xia and Lv, Proposition 4.3, printed p. 587](https://doi.org/10.1017/S0269964823000293)

## The length columns

Use ordinary coefficients in $z$ and set

$$
 S=\sum_{1\le h<j}\frac{uz^h}{h!},\qquad
 B=\sum_{h\ge j}\frac{uz^h}{h!},\qquad
 G=(1-S)^{-1},\qquad D=BG.
$$

The sequence of short blocks before, between, and after the $k$ long blocks gives $R_k=B^kG^{k+1}=GD^k$ and $p_{n,k}=[z^n]R_k=a_{n,k}/n!$. Its support is $n\ge kj$. Multiplying a whole row by $n!$ preserves the stated inequalities.

Every $G^h$ for integer $h\ge2$ has log-concave coefficients. Choose $v>0$ small enough that $q=S(v)\in(0,1)$, and take a jump law $f_0=0$, $f_i=v^i[z^i]S/q$ for $i\ge1$. Its positive support is an interval and its coefficients are log-concave. The compound negative-binomial law with shape $h$ and success probability $1-q$ has generating function $(1-q)^hG(vz)^h$. Proposition 4.3 of Xia and Lv gives log-concavity when $(h-1)q f_1^2\ge2f_2$. Here this simplifies to $(h-1)([z]S)^2\ge2[z^2]S$, which holds for $u\ge1$ and also when $j=2$. Positive constants and geometric tilts preserve log-concavity. [Xia and Lv, Proposition 4.3](https://doi.org/10.1017/S0269964823000293)

We use two elementary facts about the likelihood order on the length index. Shifts of an interval-supported log-concave sequence increase in this order as the shift increases. Convolution with such a sequence preserves the order. In both cases the proof uses its lower-triangular Toeplitz matrix. Every two-by-two minor is nonnegative by decreasing successive ratios and zero padding. Cauchy–Binet gives the convolution assertion and proves in the same way that two log-concave sequences with interval support have log-concave convolution. All computations of a fixed coefficient use finite truncations.

## A size-weighted likelihood comparison

For $k\ge1$ and $n\ge(k-1)j$, set $r_k(n)=p_{n,k}/p_{n,k-1}$. We prove that

$$
\frac{r_k(n)}{n-(k-1)j}
\quad\text{is nondecreasing for }n>(k-1)j .
$$

It suffices to prove the length-index order $`(z\,d/dz-(k-1)j)R_{k-1}\preceq R_k`$. Differentiation splits its left side as

$$
k(zS')B^{k-1}G^{k+1}
+(k-1)(zB'-jB)B^{k-2}G^k ,
$$

where the second summand is omitted for $k=1$. For the first summand, $zS'\preceq B$ since the short sizes precede all long sizes. The common factor $B^{k-1}G^{k+1}$ is log-concave by the preceding results, and convolution gives the comparison.

For the second summand write $b_h=u/h!$ for $h\ge j$ and zero below. The support of $zB'-jB$ starts at $j+1$, while that of $z^jB$ starts at $2j$. On their overlap the successive ratio of the sequence $(h-j)b_h/b_{h-j}$ is $(h-j+1)^2/((h-j)(h+1))\le1$. Hence $zB'-jB\preceq z^j B$. The series $B^2G$ is a positive mixture of shifts of $B$ by at least $j$. Log-concavity of $B$ gives $z^j B\preceq B^2G$. Convolution with the log-concave common factor $B^{k-2}G^k$ proves the second comparison. Likelihood determinants are linear in the left sequence, so the sum has the claimed order.

In particular $r_k(n)$ increases strictly once it is positive, and first becomes positive at $kj$. This proves $P_n\preceq P_m$ for all $n\le m$, by multiplying successive ratio comparisons on the common support. Equivalently the entire length-by-count coefficient array has nonnegative minors of order two.

## Averaging over a long block and a short stretch

At a length $m$ with $p_{m,k+1}>0$, place probability $D_i p_{m-i,k-1}/p_{m,k}$ on the duration $i$, writing $D_i=[z^i]D$. This is the length of one specified long block and one specified short stretch among the $k$ long blocks and $k+1$ stretches. Conditional on the total long length $L$, the long lengths are exchangeable, and so are the stretch lengths. Therefore

$$
\mathbb E[i]=\mathbb E[L]/k+(m-\mathbb E[L])/(k+1)>(m+j)/(k+1).
$$

Strictness follows because a long block can have size $j+1$ and short blocks can fill all remaining length, giving positive weight to $L>kj$ when $m\ge(k+1)j$. The same convolution gives $r_{k+1}(m)=\mathbb E[r_k(m-i)]$. Whenever $m-j\le n$, every argument $m-i$ is at most $n$. With $n>(k-1)j$, the preceding monotonicity bounds the integrand by

$$
 r_k(n)\frac{m-i-(k-1)j}{n-(k-1)j}.
$$

At the left endpoint $m-i=(k-1)j$ the integrand is zero. Averaging gives, whenever $n\le m\le n+j$ and $p_{m,k+1}>0$,

$$
 r_{k+1}(m)
 < \frac{k}{k+1}\frac{m-kj}{n-(k-1)j} r_k(n).
$$

At $m=n$ this proves the fractional Newton bound. For $m\le n+j$ the fraction involving the two sizes is at most one. This proves $P'_m\preceq P_n$ by adjacent coefficient ratios, and dropping the factor $k/(k+1)$ gives $P_m\preceq tP_n$. The end coefficients obey the same orders by zero padding, since the later degree exceeds the earlier by at most one. For constant rows the derivative may vanish, which satisfies the determinant definition.

Finally, any positive tilt preserves these comparisons. Likelihood order implies stochastic order by summing the nonnegative two-by-two minors across each degree cut and normalizing. Using the same uniform random variable in the inverse distribution functions for every $n$ gives the simultaneous coupling. Two jumps fewer than $j$ positions apart would yield an increase of at least two in an interval of at most $j$ steps.

## Verification and scope

The checker computes each integer row by removing its first block and independently enumerates ordered labeled partitions through size eight. It checks the length-weighted ratios, fractional Newton bounds and both sides of the likelihood comparisons. The gzip ledger contains every coefficient vector from these 4,617 rows. [Checker](verify.py) · [Exact counts and ranges](checks.json) · [Row ledger](ordered-rows.jsonl.gz)

~~~sh
python3 verify.py
python3 verify.py --ledger ordered-rows.jsonl.gz
~~~

An independent agent-assisted reviewer reconstructed the compound law, checked both length comparisons including the zero-support endpoints, and verified the exchangeability step and the strict fractional Newton constant. The reviewer also checked the common-quantile construction. [Independent mathematical review](review.md) A proof of the higher-order minors needed for full real-rootedness remains open.

On 26 November 2026, searches for “ordered set partitions”, “large blocks”, “likelihood ratio”, “log-concavity” and “Alexandersson”, including the author's GitHub discussions and web-indexed X, located Fang's unordered result and earlier work on Riordan arrays. The author's weight-classification issue discusses both the ordered and unordered families. These searches cannot establish priority exhaustively. [Alexandersson's weight question](https://github.com/PerAlexandersson/RealRooted/issues/2590) · [Fang's manuscript](https://hexagonmath.org/pdf/2611.01129v1) · [Program tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1)
