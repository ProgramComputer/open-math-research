# Backward coefficient maps from remote row counts

Let $a_{n,k}=a(n,k,r,d)$ count the labeled arrays in the [balanced-array conjecture of Per Alexandersson](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays), and set $D_n=\lfloor nr/d\rfloor$. For fixed shape $(r,d)$ and $N\ge n$, define the backward map $T_{N,n}$ on polynomials of degree at most $D_N$ by multiplying coefficient $k$ by $a_{n,k}/a_{N,k}$, with zero output above degree $D_n$. For every $k\le D_N$, the denominator is positive. Allocate $dk$ positions consecutively along cyclic row order, with one block of $k$ positions per column. No block repeats a row because $k\le N$, and the maximum row load is $\lceil dk/N\rceil\le r$. The sole quota at $N=0$ has count one.

At $(r,d)=(2,4)$ the following statements concern preservation by the backward map on classes of test polynomials.

- The binomial test $T_{2n,n}((1+q)^n)$ is real-rooted exactly when $0\le n\le10$.
- For every fixed target $n\ge16$ and every sufficiently large source $N$, some degree-$D_N$ polynomial with negative zeros has equally spaced logarithms of absolute root values, with spacing equal to the minimum spacing of the source polynomial. Its image has a nonreal zero after applying $T_{N,n}$. The required source threshold may depend on $n$.

The balanced-array polynomials themselves are real-rooted in this shape by the [four-column theorem](../four-columns/README.md). The obstruction concerns using the backward map as a general preserver, even under the spacing restriction.

## Remote-source limits

For each fixed quota $k$, as $N$ grows,

$$
a_{N,k}\sim\frac{N^{dk}}{(k!)^d}.
$$

Indeed, $(N)_{dk}/(k!)^d$ counts arrays where all column supports are disjoint, and $\binom Nk^d$ counts all arrays with the desired column sums. These lower and upper bounds have the same leading term. With $M=D_N$, the image of $(1+q)^M$ under $T_{N,n}$, after replacing $q$ by $(d/r)N^{d-1}q$, therefore converges coefficientwise to

$$
W_n(q)=\sum_{k=0}^{D_n}(k!)^{d-1}a_{n,k}q^k.
$$

The [cubic-factorial classification](../factorial-weight-four.md) gives a nonreal zero in $W_n$ for $(r,d)=(2,4)$ and $n\ge16$. The limit has degree $D_n$ and leading coefficient strictly positive. Continuity of the multiset of roots in fixed degree implies that the rescaled images, and hence the original images, have a nonreal zero for all sufficiently large $N$.

To restrict the class of allowed inputs, assume $P_N$ is real-rooted for all sufficiently large $N$ and write $P_N(q)=\prod_{i=1}^{M}(1+x_iq)$ with $0<x_1\le\cdots\le x_M$. Define its multiplicative mesh by $Q_N=\min_{1\le i<M}x_{i+1}/x_i$. This is also the minimum ratio of consecutive absolute root values in increasing order. For $M\ge2$,

$$
1\le a_{N,M}=\prod_i x_i\le x_M^M Q_N^{-M(M-1)/2}
\le (N^d)^M Q_N^{-M(M-1)/2},
$$

since $x_M\le\sum_i x_i=a_{N,1}\le N^d$. Thus $0\le\log Q_N\le2d\log N/(M-1)\to0$ at fixed shape.

Put $w_i=Q_N^i$, $E=\sum_{i=1}^M w_i$, and test $T_{N,n}$ on $G_N(q)=\prod_{i=1}^M(1+w_iq)$. Its mesh is exactly $Q_N$. For each fixed $L$ and eventually $M\ge L$, $E/\max_i w_i\ge\sum_{j=0}^{L-1}Q_N^{-j}\to L$, so $\max_i w_i/E\to0$. With $k$ independent draws from the weights $w_i/E$, the probability of all distinct indices is $k!e_k(w)/E^k$, where $e_k$ is the elementary symmetric polynomial. The probability of a collision is at most $\binom{k}{2}\max_i w_i/E$. Therefore the coefficient of $q^k$ in $T_{N,n}(G_N)(N^dq/E)$ converges to $(k!)^{d-1}a_{n,k}$. The same fixed-degree limit now gives a failed test even in the class of degree-$D_N$ negative-rooted inputs with mesh at least $Q_N$. Replacing $Q_N$ by $Q_N^2$ in the test weights gives the same limit and strictly larger mesh when $Q_N>1$. [Independent mesh review](review-remote-mesh.md)

## Doubled source

For $(r,d)=(2,4)$ and $N=2n$, the binomial symbol has coefficients

$$
e_k=\binom nk\frac{a_{n,k}}{a_{2n,k}},qquad 0\le k\le \lfloor n/2\rfloor.
$$

When $n\ge8$, the fourth power sum of the negatives of the reciprocal roots is

$$
e_1^4-4e_1^2e_2+2e_2^2+4e_1e_3-4e_4.
$$

A real-rooted symbol gives a nonnegative value. To check its sign, write $e_1,e_2,e_3,e_4$ as $a/A,b/B,c/C,d'/D$ using the degree-$4k$ quota polynomials $a_{n,k}$ and denominators $k!a_{2n,k}$. The strictly positive common denominator is $A^4B^2CD$. The numerator is

$$
a^4B^2CD-4a^2bA^2BCD+2b^2A^4CD+4acA^3B^2D-4d'A^4B^2C.
$$

After substituting $n=33+t$, exact polynomial arithmetic gives degree 61 with all 62 coefficients strictly negative. This gives a nonreal zero for all $n\ge33$.

For the finite prefix, exact Sturm counts give no nonreal zeros at $0\le n\le10$, two at $11\le n\le23$, and four at $24\le n\le32$. All these polynomials are square-free. The replay obtains the quota polynomials by exact Newton interpolation from the paired-column count, which is derived in the [independent review](review-remote-transfer.md). The degree bound follows by classifying arrays by their sets of nonempty rows, whose cardinalities are at most $4k$. The replay also reproduces the cutoff for the earlier cubic-factorial classification.

The limiting-symbol and doubled-source arguments are by the research team. The paired-column reconstruction and exact independent checks are credited in the [review](review-remote-transfer.md). **⬜ None** for Lean or Rocq. Run the exact replay from the repository root with Python and python-flint.

~~~sh
python -B topics/balanced-arrays/row-deletion/verify_remote_transfer.py
~~~
