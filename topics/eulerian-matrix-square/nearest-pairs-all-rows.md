# The two smallest nonzero Eulerian-square roots at every row

Let $P_n=xH_n$ be the shifted Eulerian-square row. For every $n\ge3$, the two zeros of $H_n$ of smallest modulus are simple and negative. Write their positive moduli as $s_{n,1}<s_{n,2}$. Then
$$
 s_{n+1,1}<s_{n,1}<s_{n+1,2}<s_{n,2}
 <\min\{|z|: H_{n+1}(z)=0,\ |z|>s_{n+1,2}\}.
$$
A proof with explicit constants applies from row 256 onward. A finite exact check covers the preceding rows. Together with the [large-modulus theorem](extreme-pairs-all-rows.md), this gives strict consecutive alternation of the two roots at each end for all $n\ge3$.

## Eulerian rows at positive integer arguments

Put $N=n+1$, $p_i=[x^i]H_n(x)$, $\rho_i=i/\log(1+i)$, and $\rho_0=1$. Let $A_n(t)=\sum_k A(n,k)t^k$ where $A(n,k)$ counts permutations with $k-1$ descents. By the Eulerian pole formula at $t=i+1$, for $i\ge1$
$$
 \left|\frac{A_n(i+1)}{n!\rho_i^N}-1\right|
 \le 2\sum_{m\ge1}\left(1+\frac{4\pi^2m^2}{\log^2(i+1)}\right)^{-N/2}.
$$
For $N\ge2$ this is at most $\log(i+1)/2$, by integrating the decreasing reciprocal quadratic from $0$ to infinity. For fixed $i=1,2$ it is also at most $4(\log(i+1)/(2\pi))^N$, using $\sum_{m\ge1}m^{-N}\le2$. The elementary bound $A(k,i+1)\le(i+1)^k$ then gives
$$
 0\le p_i=\sum_k A(n,k)A(k,i+1)\le A_n(i+1)\le(i+1)n!\rho_i^N .
$$
Here $A(k,i+1)$ is taken to be zero outside its support. Both identities used here follow from the explicit Eulerian formula. [Derivation](endpoint-asymptotics.md)

Write $c_1=\log2$, $c_2=\log3/(2\log2)$, and $q_1=c_1/c_2$. Use the estimates
$$
 2/3<c_1<7/10,\quad c_2<4/5,\quad q_1<9/10,\quad \log3<6/5 .
$$
The lower bound on $\log2$ is immediate from the positive series $\log v=2\sum_{j\ge0}[(v-1)/(v+1)]^{2j+1}/(2j+1)$. The first three terms of that same series give $\log3>109/100$. The upper bound on $\log2$ follows by taking the first four terms of $e^{7/10}>2$. Then $3^5<2^8$ proves $c_2<4/5$ and implies $\log3<(8/5)(7/10)<6/5$. Combining the rational bounds on the logarithms gives $q_1=2\log^2 2/\log3<9/10$.

The coefficient $p_0=n!$. Since $A(k,2)=2^k-k-1$ and the mean column index in the Eulerian row is $(n+1)/2$ by reversal symmetry,
$$
 p_1=A_n(2)-(n+3)n!/2 .
$$
For $k\ge1$ the alternating formula gives $0\le3^k-A(k,3)\le(k+1)2^k$. Applying the pole estimates at 2 and 3 (using $\pi>3$) gives
$$
 \left|\frac{p_j}{n!\rho_j^N}-1\right|\le\delta_j,\qquad
 \delta_1=4(1/8)^N+\frac{n+3}{2}(7/10)^N,\quad
 \delta_2=4(1/5)^N+2(n+1)(4/5)^N.
$$
Here $A_n(2)/(n!\rho_1^N)\le2$ for $n\ge1$, and $\rho_1/\rho_2=c_2$.

## Exact bounds on two circles

For $j=1,2$ put $D_j=\rho_j c_j^j=\rho_{j-1} c_j^{j-1}$ and
$$
 K_{n,j}(u)=\frac{H_n(c_j^N u)}{n!D_j^N}.
$$
Strict log-concavity of $\rho_i$ follows by Hölder's inequality applied to $1/\rho(x)=\int_0^1(1+sx)^{-1}\,ds$. Thus for $i>j$ the consecutive ratios of $\rho_i c_j^i$ are at most $\rho_{j+1}c_j/\rho_j$. For $j=1$ the latter is $q_1<9/10$. For $j=2$ it is $(3/2)c_2^2<24/25$ since $\log4=2\log2$. Put $v_1=9/10$, $v_2=24/25$. On $|u|\le2$ the complete tail of $K_{n,j}$ from degree $j+1$ is bounded by
$$
 T_j=2^j\left[\frac{t_j}{(1-t_j)^2}+(j+1)\frac{t_j}{1-t_j}\right],
 \qquad t_j=2v_j^N<1 \quad(n\ge256).
$$
Indeed sum $(i+1)2^i v_j^{N(i-j)}$ over $i>j$.

For $n\ge256$ this proves
$$
 |K_{n,1}(u)-(1+u)|\le2\delta_1+T_1<1/32,\qquad
 |K_{n,2}(u)-(u+u^2)|\le(9/10)^N+2\delta_1+4\delta_2+T_2<1/32
$$
on $|u|\le2$. The constant term in the second bound uses $D_2^{-1}=q_1$. The rational upper bounds decrease on this range: in particular the ratios of the two terms with a linear prefactor are bounded by $(260/259)(7/10)$ and $(258/257)(4/5)$ respectively. At $n=256$ both strict rational comparisons hold. [Rational check](code/nearest_pair_bounds.py)

On $|u|=2$ the comparison polynomials have modulus at least one and two, respectively. Rouché's theorem therefore gives exactly one zero of $K_{n,1}$ and two of $K_{n,2}$ in their open disks, with none on the circles. At $u=-15/16,-17/16$ each comparison polynomial changes sign and the smaller absolute value is at least $15/256>1/32$. Each scale therefore has a negative simple zero with modulus between $15/16$ and $17/16$ in its own variable. For clarity, in the second disk the first zero already has scaled modulus at most $(17/16)q_1^N<15/16$. This and the second sign change exhaust the count.

It follows that
$$
 (15/16)c_j^N<s_{n,j}<(17/16)c_j^N\quad(j=1,2),
$$
and all other root moduli exceed $2c_2^N$. Since $17c_j<15$ for both $j$, the two moduli decrease with $n$. Moreover $17q_1^N<15c_2$ and $17/16<2c_2$ because $c_2>c_1>2/3$. These inequalities give the stated alternation, including strict separation from every remaining modulus in the next row.

## Finite prefix

For $2\le n\le256$, a standalone verifier reconstructs the Eulerian rows by alternating sums and matches the resulting square to the published coefficient vectors. At each row it checks a full sequence of degree-exhausting sign separators, then checks rational brackets for the first three root moduli, or all the available ranks for smaller rows. The brackets are strictly ordered in the five-term chain for each $3\le n\le255$. At $n=2$ they also prove $s_{3,1}<s_{2,1}<s_{3,2}$. [Prefix verifier](code/nearest_pair_prefix.py) · [Finite certificates](results/nearest-pair-prefix.jsonl.gz)

~~~sh
python -I -O topics/eulerian-matrix-square/code/nearest_pair_bounds.py
python -I -O topics/eulerian-matrix-square/code/nearest_pair_prefix.py --replay
~~~

The independent trureturing project records an earlier exact verification in row 33. The finite prefix here overlaps that case. [Prior row 33 result](https://www.trureturing.org/knowledge/node/4c8d23f92b2193daa1cb796b24022eb3b71548e0ee51ea5323ac87c69dad6058/)
