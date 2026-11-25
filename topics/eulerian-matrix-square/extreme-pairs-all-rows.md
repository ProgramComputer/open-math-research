# The two largest Eulerian-square zeros interlace at every row

Write $P_n=xH_n$ for the shifted row polynomial of the ordinary Eulerian matrix square. For **every** $n\ge3$, the two zeros of $H_n$ of largest modulus are distinct, simple and negative. Write their moduli as $b_{n,1}>b_{n,2}$. Then
$$
 b_{n+1,1}>b_{n,1}>b_{n+1,2}>b_{n,2}>
 \max\{|z|:H_{n+1}(z)=0,\ |z|<b_{n+1,2}\}.
$$
The maximum exists for $n\ge3$. This is an all-row conclusion with an evaluated cutoff for the estimates. It makes a statement about the two largest roots even for any row in the unknown finite gap of the [eventual full-row theorem](eventual.md).

## Uniform endpoint bounds from forty rows onward

Let $e_{n,j}$ count permutations with $j$ descents and $L_n(z)=z^{n-1}H_n(1/z)$. Ordinary matrix multiplication and reversal of descents give
$$
 L_n(z)=\sum_{A,B\ge1,\ A+B\le n+1}
 e_{n,A-1} e_{n+1-A,B-1}z^{A+B-2}.
$$
In particular $e_{n,0}=1$ and $e_{n,1}=2^n-n-1$. Uniformly $e_{m,j}\le(j+1)^m$, since assigning one of $j+1$ ordered runs to each label specifies the permutation once labels are sorted within each run. [Endpoint identities](endpoint-asymptotics.md)

For $n\ge40$ set $Q_n(u)=L_n(2^{-n}u)$ and $F(u)=1+2u+u^2/2$. In the four terms $A,B\in\{1,2\}$ the constant is one, the linear coefficient is $2(1-(n+1)/2^n)$, and the quadratic coefficient is
$$
 \frac12\left(1-\frac{n+1}{2^n}\right)\left(1-\frac n{2^{n-1}}\right).
$$
At $|u|\le8$ the difference between these terms and $F(u)$ is bounded by $[16(n+1)+32(3n+1)]/2^n$.

For the remaining terms, put $f(A)=A/2^{A-1}$. Each term has modulus at most $f(A)^nf(B)^n8^{A+B-2}$ because $B^{1-A}\le1$. For the one-variable sum the terms $A=1,2$ contribute $1+8=9$. The rest contribute at most
$$
 T_n=\frac{64(3/4)^n}{1-8(2/3)^n},
$$
since $f(3)=3/4$ and $f(A+1)/f(A)\le2/3$ for $A\ge3$. Extending the noncentral sum to the full quadrant shows that
$$
 |Q_n(u)-F(u)|\le E_n
 =\frac{16(n+1)+32(3n+1)}{2^n}+18 T_n+T_n^2<\frac1{32}
 \qquad (|u|\le8,\ n\ge40).
$$
All positive summands decrease with $n$ on this range. The last inequality at $n=40$ is a rational comparison reproduced by the verifier below.

On $|u|=8$, $|Q_n(u)-u^2/2|\le17+1/32<32$. Rouché's theorem gives exactly two zeros there in the open disk, counted with multiplicity, and no boundary zero. For $t=1/2,3/4,13/4,7/2$ in that order, the values of $F(-t)$ are $1/8,-7/32,-7/32,1/8$. The strict uniform bound preserves those signs. Thus the two interior zeros of $Q_n$ are simple, real, and have moduli in $(1/2,3/4)$ and $(13/4,7/2)$. Every other zero has modulus strictly greater than eight. Inverting gives
$$
 \frac43\,2^n<b_{n,1}<2\cdot2^n,\qquad
 \frac27\,2^n<b_{n,2}<\frac4{13}\,2^n.
$$
All remaining moduli are below $2^n/8$. Applying the same bounds to $n+1$ orders the five quantities in the theorem, since $1/4<2/7$, $4/13<4/7$, $8/13<4/3$, and $2<8/3$.

## Finite verification

For the 39 adjacent pairs $(H_n,H_{n+1})$, $1\le n\le39$, an exact verifier reconstructs the polynomials from the alternating Eulerian formula. In every pair, the negative Euclidean remainder chain starting with $H_{n+1},H_n$ has positive leading coefficients and drops degree by one at each step until a nonzero constant. This certifies strict interlacing. Indeed, start with the last linear polynomial and constant. If a consecutive pair in reverse order strictly interlaces, evaluate the Euclidean identity at each root of the divisor. The preceding polynomial has the opposite sign of the following polynomial there. Alternation and the positive leading coefficients give one root in each gap including both exterior intervals, exhausting the degree. Every nonconstant row has positive coefficients and nonzero constant term, hence all these real zeros are negative. This gives the stated ordering for every remaining $3\le n\le39$.

~~~sh
python -I -O topics/eulerian-matrix-square/code/extreme_pair_all_rows.py topics/eulerian-matrix-square/results/extreme-pairs.jsonl --replay
~~~

[All finite coefficient vectors and chain degrees](results/extreme-pairs.jsonl) · [Verifier using python-flint](code/extreme_pair_all_rows.py)
