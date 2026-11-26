# Independent review of the remote row-transfer obstructions

Reviewed and signed by the agent-assisted reviewer `four_blind`, 2026-11-26.

**Verdict.** Both obstructions hold. At shape $(d,r)=(4,2)$, every fixed target $n\ge16$ has a bound $N_0(n)$ beyond which all backward binomial test symbols have nonreal zeros. For the doubled source $N=2n$, the symbols have nonreal zeros for every $n\ge11$. Exact Sturm counts establish the latter for $11\le n\le32$, and a negative fourth Newton sum establishes it for $n\ge33$. The doubled symbols for $n=8,9,10$ are real-rooted. These results concern the transfer symbol used to test preservation on all input polynomials. The deterministic balanced-array conjecture remains open.

## Remote-source limit

Let $M_N=\lfloor Nr/d\rfloor$ and $D_n=\lfloor nr/d\rfloor$. For $N\ge n$, the nonzero part of the backward test symbol is

$$
S_{N,n}(q)=\sum_{k=0}^{D_n}\binom{M_N}{k}\frac{a(n,k,r,d)}{a(N,k,r,d)}q^k.
$$

For every feasible $k\le M_N$, allocate $dk$ successive positions cyclically among the $N$ rows, using $k$ consecutive positions for each column. These positions give distinct rows within each column, and maximum row load is $\lceil dk/N\rceil\le r$. This proves positivity of every denominator, including the special case $N=2n$ and $1\le k\le4$ for $n\ge8$.

For each fixed $k$, draw $d$ independent uniform $k$-subsets of the source rows as the column supports. The probability that any two overlap is at most $\binom d2 k^2/N$. Disjoint supports satisfy every cap $r\ge1$, hence $a(N,k,r,d)\sim N^{dk}/(k!)^d$. Also $\binom{M_N}{k}\sim (Nr/d)^k/k!$. Consequently $S_{N,n}((d/r)N^{d-1}q)$ converges coefficientwise to $\sum_k(k!)^{d-1}a(n,k,r,d)q^k$. The constant term is always one, and the limiting coefficient of degree $D_n$ is positive. A fixed-degree coefficient limit of real-rooted polynomials with nonzero limiting leading coefficient is real-rooted by continuity of the multiset of roots. Therefore a strictly nonreal limit implies failure at every sufficiently late source, with a threshold allowed to depend on the target and shape.

## Independent enumeration and certificates

Partition the four columns into two ordered pairs. If the first pair has overlap $i$, choose its intersection, first exclusive part and second exclusive part in

$$
\binom ni\binom{n-i}{k-i}\binom{n-k}{k-i}
$$

ways. The second pair's overlap $j$ must lie in the $n-2k+i$ rows empty in the first pair. Its two disjoint exclusive parts can use any remaining rows except the $i$ rows already occupied twice. Its multiplicity is

$$
\binom{n-2k+i}{j}\binom{n-i-j}{k-j}\binom{n-i-k}{k-j}.
$$

Sum the product over $0\le i,j\le k$, with infeasible binomial choices counted as zero. Each term describes labeled columns and enforces exactly the row-cap condition. Separately, partition valid arrays by their exact set of nonempty rows. The count for a quota $k$ is then a linear combination of $\binom n j$ with $j\le4k$. Thus forward differences at $n=0,\ldots,4k$ determine the actual quota polynomial. Direct evaluations beyond the interpolation range provide an additional implementation check.

For the doubled test symbol, the first four coefficients are $e_k=(n)_k a(n,k)/(k!a(2n,k))$. If the symbol has only real roots, so does the reversed monic polynomial with sign alternation, whose first four elementary symmetric functions are $e_1,\ldots,e_4$. Its fourth root power sum is

$$
e_1^4-4e_1^2e_2+2e_2^2+4e_1e_3-4e_4\ge0.
$$

Positive clearing denominator $A^4B^2CD$ uses $(A,B,C,D)=(k!a(2n,k))_{k=1}^4$. The independently interpolated degree-61 numerator has all 62 coefficients strictly negative after $n=33+t$. For $8\le n\le32$, exact rational Sturm on the square-free part gives full degree at $8,9,10$ and a deficit at every $11\le n\le32$. The deficit is two roots through $n=23$ and four roots from $n=24$ through $32$. None of these earlier failures has a negative fourth power sum.

For the cubic-factorial limit, the same independent quota polynomials give a degree-13 Newton sum with every coefficient strictly negative after $n=76+t$. Exact rational Sturm on the independently counted coefficients gives full square-free degree exactly at $0\le n\le15$ over the remaining range $0\le n<76$.

Run the [independent replay](verify_remote_transfer.py) with Python and `python-flint`. It imports no repository checker or counting routine.
