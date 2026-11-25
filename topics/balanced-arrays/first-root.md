# The first zero of every balanced-array polynomial

Write $P_n(q)=\sum_k a_k(n)q^k$ for labeled $n\times d$ binary arrays of column quota $k$ and row cap $1\le r\le d$. All comparisons below keep $r,d$ fixed. A zero of least modulus is a zero closest to the origin in the complex plane.

**Theorem.** Suppose $d\ge2$ and $nr\ge d$. The zero of least modulus of $P_n$ is unique, simple and negative. Write it as $-b_n$. Then $b_{n+1}<b_n$, and every other complex zero of $P_{n+1}$ has modulus strictly larger than $b_n$. For $d\ge3$, with $M=a_1(n)$, one has $1/M\le b_n<6/(5M)$. The theorem applies at each finite row count, including the interval before eventual real-rootedness takes effect. It leaves the other zeros of a general row undetermined. For $d=1$ the zeros of $(1+q)^n$ repeat.

## A disk on which a polynomial is injective

Let $F(z)=1+Mz+\sum_{k\ge2}c_kz^k$ with $M>0$ and $c_k\ge0$. On $|z|,|w|\le R$ the factorization of $z^k-w^k$ gives
$$
 |z^k-w^k|\le kR^{k-1}|z-w|.
$$
If $\sum_{k\ge2}k c_kR^{k-1}<M$, the linear term separates any two distinct points on the closed disk. The same bound gives $|F'(z)-M|<M$ there. Thus any zero in the disk is unique and simple.

## Counting ordered layers

Assume $d\ge3$. A quota-$k$ array can be split into $k$ ordered quota-one layers in $(k!)^d$ ways by independently ordering the occupied cells of each column. Every layer respects the row cap, and their union recovers the array. Alternatively, extracting just one layer offers $k^d$ choices. With $a_k=a_k(n)$ this proves
$$
 (k!)^d a_k\le M^k,\qquad (k+1)^d a_{k+1}\le M a_k .
$$
At $R=2/M$, the derivative tail divided by $M$ is bounded by $\sum_{k\ge2}k2^{k-1}/(k!)^d$. Its first term is at most $1/2$ and successive terms have ratio $2/[k(k+1)^{d-1}]\le1/9$, giving the bound $9/16$. At $t=6/(5M)$ the terms $a_kt^k$ decrease from $k=1$ onwards. The alternating sum at $-t$ is at most $1-6/5+(6/5)^2/8=-1/50$. At $t=1/M$, its tail beginning with $a_2t^2$ has nonnegative sum. Since $P_n(0)=1$, continuity gives a negative zero in the stated interval. Disk injectivity and the derivative bound establish uniqueness in modulus and simplicity.

## Inserting a row

Put $M'=a_1(n+1)$ and $\Delta a_k=a_k(n+1)-a_k(n)$. This difference counts arrays whose last row is nonempty. In particular $\Delta M=M'-M>0$, since a quota-one array exists and moving one of its ones to a new row produces such an array. At least one ordered layer in a decomposition of an array counted by $\Delta a_k$ uses the last row. Counting all possible distinguished layers gives
$$
 (k!)^d\Delta a_k\le k\,\Delta M\,(M')^{k-1}.
$$
For $0<t\le2/M'$ the absolute tail of $P_{n+1}(-t)-P_n(-t)$ divided by $t\Delta M$ is at most the same $9/16$ as above. Its linear term is $-t\Delta M$, so the difference is strictly negative. In particular $P_n(-b_{n+1})>0$. Both $b_n$ and $b_{n+1}$ are strictly below $2/M$. On that interval $P_n(-t)$ changes sign exactly once from positive to negative. This proves $b_{n+1}<b_n$.

## The other zeros of the next row

Set $N=n+1$, $a'_k=a_k(N)$, and assume $a'_2>0$; otherwise the next row is linear. The log-concavity of $a'_k/\binom Nk^d$ implies, throughout the positive support and for $k\ge2$,
$$
 \frac{a'_{k+1}/a'_k}{a'_2/M'}
 \le \left(\frac{2(N-k)}{(k+1)(N-1)}\right)^d
 \le \left(\frac2{k+1}\right)^d .
$$
This is the single input from the [orientation theorem](orientation-normalization.md). On the larger disk of radius $R=2M'/(5a'_2)$, the first term of the derivative tail divided by $M'$ is $4/5$. The ratio of successive terms is at most $(3/2)(2/5)(2/3)^3=8/45$. The whole tail is at most $36/37<1$. It remains to put $b_n$ in this disk.

For a quota-two array with $N$ rows and last-row load $s$, exactly $2^{d-s}$ choices of a first layer avoid the last row. Deleting that empty row from this layer and keeping the complementary layer gives an ordered pair counted by $MM'$. The pair determines the array and the chosen layer. Averaging over the quota-two arrays, exchangeability gives $\mathbb E s=2d/N$. Since $2^j\ge2j$ for every integer $j\ge0$,
$$
 MM'/a'_2\ \ge\ \mathbb E 2^{d-s}\ \ge\ 2d(1-2/N).
$$
This is at least $3$ for $n\ge3$, and also for $n=2,d\ge5$. For $n=2,d\in\{3,4\}$, the four choices with $a'_2>0$ have the following counts.

| $d$ | $r$ | $M$ | $M'$ | $a'_2$ |
|---|---|---|---|---|
| 3 | 2 | 6 | 24 | 6 |
| 3 | 3 | 8 | 27 | 27 |
| 4 | 3 | 14 | 78 | 36 |
| 4 | 4 | 16 | 81 | 81 |

The table can also be obtained directly by assigning each of the $d$ labeled columns its occupied subset of the two or three rows and testing each row load. Each ratio $MM'/a'_2$ exceeds $3$. Hence $R\ge6/(5M)>b_n$, and injectivity on the larger disk excludes every other zero through modulus $b_n$. Finally $n=1$ requires $r=d$. Here $P_1=1+q$ and $P_2=1+2^dq+q^2$ has one zero on each side of $-1$, since $P_2(-1)<0$ and $P_2$ is positive at zero and sufficiently far to the left.

## Two columns

Write $L_n$ for the Legendre polynomial with $L_n(1)=1$. For $r=1$ one has $P_n(q)=(1-4q)^{n/2}L_n((1-4q)^{-1/2})$. Indeed the generating function in $n$ is $((1-z)^2-4qz^2)^{-1/2}$ by the multinomial formula. For $r=2$ one has $P_n(q)=(1-q)^n L_n((1+q)/(1-q))$ by expanding the Legendre generating function, or the binomial-square identity. On $q<0$ these changes of variable are strictly increasing onto $(0,1)$ and $(-1,1)$, respectively. The largest Legendre zero increases strictly in passing to the next degree and its second largest is smaller than the previous largest. Parity accounts for the positive half of the zeros when $r=1$. Thus the same first-zero conclusion holds, including when a second zero is absent. [NIST DLMF, separation of zeros](https://dlmf.nist.gov/18.2.vi)
