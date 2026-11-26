# The corank-one boundary for scalar Hessenberg determinants

Let $a_{n,k}$ count labeled balanced arrays with $n$ rows, $d$ columns and row cap $r$. Fix a real exponent $\alpha$ and positive weights $w_k$ independent of $n$. Write $(n)_k=n!/(n-k)!$ and normalize $w_0=w_1=1$ by a constant and a rescaling of $q$. Consider
$$
T_n(q)=\sum_{k=0}^{\lfloor nr/d\rfloor}
\frac{w_k a_{n,k}}{(n)_k^\alpha}q^k .
$$

**Theorem.** Among $1\le r<d$, precisely $r=d-1$ admits such a normalization and a single infinite unit lower triangular matrix $A$ with nonnegative entries for which **both** of the following hold at every size.

1. $T_n=\det(A_n-qU_n)$, where $A_n$ is the leading $n$-section and $U_n$ has ones on its first superdiagonal and zeros elsewhere.
2. $T_n$ is real-rooted.

The positive case follows from the [corank-one theorem](no-full-row.md). In its notation, divide recurrence (3) by $(n!)^{d-1}$ to get a nested unit lower triangular matrix with entries $((j-1)!/i!)^{d-1}((D+L)^{d-1})_{ij}$. Equation (4) there proves real-rootedness for $\alpha=d$, $w_k=1$. The present theorem excludes this entire method beyond corank one even if the quota weights can be chosen freely. Block matrices, row-dependent weights and direct arguments about the original array polynomial are outside its scope. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

## Coefficients, degrees and possible matrix bands

Let $F_{n,k}=a_{n,k}/\binom nk^d$ be the probability that $d$ independent uniform $k$-subsets of the $n$ row labels satisfy the cap. At any fixed $k$, the array count is polynomial in $n$. Indeed, classify the arrays by the number $h\le dk$ of nonempty rows and choose their labels in $\binom nh$ ways. The remaining count on the chosen rows is independent of $n$. Thus $F_{n,k}$ is rational in $n$ and analytic at $1/n=0$, with limit one. Write $e=d-\alpha$ and $h_k=w_k/(k!)^d$. The coefficient $b_{n,k}=[q^k]T_n=h_k(n)_k^e F_{n,k}$ is $n^{ek}$ times a function analytic in $1/n$ at zero. All expansions below concern fixed $k$.

The degree is $D_n=\lfloor sn\rfloor$ with $s=r/d$. For $n>0$, place the $dk$ ones consecutively around the cyclic list of row labels, in $d$ blocks of $k$ for the columns. Each column has distinct row labels since $k\le n$, and each row has at most $\lceil dk/n\rceil\le r$ ones. This attains every allowed $k$. The all-zero array gives $b_{n,0}=1$.

Expansion along the last row forces
$$
T_n=T_{n-1}+\sum_{j=1}^{n-1} A_{n,n-j}q^jT_{n-j-1}. \tag{1}
$$
All coefficients in this recurrence are nonnegative. A positive entry requires $j+\lfloor s(n-j-1)\rfloor\le\lfloor sn\rfloor$. This is impossible if $(1-s)j>1+s$, giving a uniform finite bound on $j$. For each fixed $j$, successive coefficient comparison in (1) shows that $A_{n,n-j}$ is $n^{ej}$ times a function analytic at $1/n=0$. In fact, in the equation for $[q^j]$ all previous products have that same power times analytic functions, including after any fixed shift of $n$. The coefficient of the unknown entry is one. Each nonnegative band is consequently either eventually positive or eventually zero. Repeating the term indexed by an eventually positive $j$ in (1) increases the degree by at least $j$ per $j+1$ rows. Hence every eventual band satisfies
$$
j\le J=\left\lfloor\frac{s}{1-s}\right\rfloor
 =\left\lfloor\frac r{d-r}\right\rfloor .\tag{2}
$$
In the reverse direction, if $j_*$ is the largest eventual band (allowing $j_*=0$ for the term $T_{n-1}$), all terms have degree growth per row at most $j_* /(j_*+1)$. Induction gives $D_n\le j_*n/(j_*+1)+O(1)$. Thus $s=j_* /(j_*+1)$ already follows from the representation alone. In particular $d-r$ must divide $d$.

## First coefficient tending to infinity

Suppose $e>0$. Write $b_n=b_{n,1}$, $b_0=0$. Equation (1) gives $A_{n,n-1}=b_n-b_{n-1}\ge0$ for $n\ge2$. Since $r<d$ we have $b_1=0$. Also $b_n\sim n^e$. For fixed $k$, the $q^k$ coefficient dominates the sum of all products of $k$ increments $b_i-b_{i-1}$ with nonconsecutive, distinct indices $i\le n$. This follows by using only the two terms of jump lengths one and two in (1). Regard the increments divided by $b_n$ as probabilities on these indices. Their largest atom tends to zero since $b_i/b_{i-1}\to1$ and $b_n\to\infty$. For $k$ independent draws, the probability that two indices coincide or are adjacent is at most $3\binom k2$ times this largest atom. Consequently
$$
\liminf_{n\to\infty} k!b_{n,k}/b_n^k\ge1.
$$
If $T_n$ has real roots, its positive coefficients and constant one allow $T_n=\prod_i(1+\lambda_i q)$ with $\lambda_i>0$. Expanding $(\sum_i\lambda_i)^k$ gives the opposite inequality $k!b_{n,k}\le b_n^k$. Since $F_{n,k}\to1$, comparison of the limits forces
$$
w_k=(k!)^{d-1}\qquad\text{for every }k.\tag{3}
$$

For these weights define $u_{n,j}=n^e A_{n,n-j}/(n)_{j+1}^e$. Dividing the $q^k$ relation (1) by $(n-1)_k^e/k!$ yields, for $n>k$,
$$
(1-k/n)^{-e} F_{n,k}-F_{n-1,k}
=\sum_{j=1}^k(k)_j u_{n,j}F_{n-j-1,k-j}.\tag{4}
$$
With each $F$ replaced by one, Newton forward differences in $k$ solve this triangular system. If $\Delta g(k)=g(k+1)-g(k)$, then
$$
u^0_{n,j}=\left.\frac{1}{j!}\Delta^j(1-k/n)^{-e}\right|_{k=0}
 =\frac{e(e+1)\cdots(e+j-1)}{j!n^j}+O(n^{-j-1}).
$$
The last equality uses that $\Delta^j$ annihilates powers below $j$ and sends $k^j$ to $j!$.

A union bound over a row and $r+1$ specified columns gives $F_{n,k}=1+O(n^{-r})$. Its analyticity in $1/n$ implies $F_{n,k}-F_{n-1,k}=O(n^{-r-1})$. The change in the left side of (4) upon restoring $F$ is therefore $O(n^{-r-1})$. Each unperturbed $u^0_{n,j}$ is $O(n^{-1})$, so restoring $F$ in the right side at those same entries gives an error of the same order. Triangular substitution, whose diagonal is $k!$, yields $u_{n,j}-u^0_{n,j}=O(n^{-r-1})$. Taking $j=r$ makes $u_{n,r}$ eventually strictly positive because $e>0$. This contradicts (2) whenever $d-r\ge2$.

## First coefficient bounded

If $e<0$, the positive first coefficient tends to zero, contradicting the nonnegative increments in (1). It remains to handle $e=0$. When $r=1$ and $d-r\ge2$, equation (2) already excludes every positive band. Suppose $r\ge2$ and $d-r\ge2$.

For fixed $k$, the probability that a particular row belongs to at least $r+1$ columns is the binomial tail with parameters $d$ and $k/n$. The probability that two specified different rows both violate the cap is $O(n^{-2r-2})$, since their total number of prescribed incidences is at least $2r+2$. A specified column containing both rows has probability $(k)_2/(n)_2=O(n^{-2})$. Bonferroni bounds over the rows give
$$
F_{n,k}=1-C k^{r+1}n^{-r}+E k^{r+2}n^{-r-1}
          +O(n^{-r-2}),\quad
C=\binom d{r+1},\quad E=(r+1)\binom d{r+2}>0.
$$
Here $2r\ge r+2$ ensures that overlapping row events only affect the remainder. The analyticity already proved permits termwise fixed shifts and first differences.

Set $H(q)=\sum_{k\ge0} h_k q^k$ as a formal series and $\theta=q\partial_q$. At $e=0$, $T_n$ tends coefficientwise to $H$. The coefficient of $n^{-r-1}$ in the difference $T_n-T_{n-1}$ is $r C\theta^{r+1}H$. At the next order it is a linear combination of $\theta^{r+1}H$ and $\theta^{r+2}H$, with coefficient $-(r+1)E\ne0$ on the latter. By triangular substitution all $A_{n,n-j}$ are $O(n^{-r-1})$. Replacing each shifted row by $H$ on the right of (1) thus makes an error $O(n^{-2r-1})$ at each fixed power of $q$, which is smaller than $n^{-r-2}$. By (2) both
$$
P=\theta^{r+1}H/H,\qquad Q=\theta^{r+2}H/H
$$
are polynomials of degree at most $J$. The first is nonconstant, since its constant coefficient vanishes and its linear coefficient is $h_1=1$.

Now $S=\theta H/H=(Q-\theta P)/P$ is rational. The functions $R_m=\theta^mH/H$ satisfy $R_0=1$, $R_{m+1}=\theta R_m+S R_m$. If $S$ were bounded at infinity, then all the $R_m$ would be bounded there, contradicting the nonconstant polynomial $P$. Otherwise $S$ has a pole at infinity of order $M\ge1$. The recurrence gives $R_m$ a pole of order $mM$ because $\theta$ never raises pole order at infinity and the product by $S$ does. Therefore $\deg P\ge r+1>J$, a contradiction. This last part uses only positivity of the matrix and the prescribed degrees.

## At half density the determinant alone fails

For $d=2r$ and $r\ge2$, the representation alone is impossible. The case $e\le0$ already followed above. Suppose $e>0$. Equation (2) permits only the first band eventually. With $c_n=b_{n,2}$ this forces $c_n-c_{n-1}=(b_n-b_{n-1})b_{n-2}$. Put $W=w_2/2^d$. The row probabilities give $b_n=n^e(1+O(n^{-2}))$ and $c_n=W n^{2e}(1-e/n+O(n^{-2}))$. Comparing terms of order $n^{2e-1}$ forces $W=1/2$. At the next order, the analytic expansions then give
$$
(c_n-c_{n-1})-(b_n-b_{n-1})b_{n-2}
=\tfrac12 e(e+1)n^{2e-2}+O(n^{2e-3}),
$$
which cannot vanish eventually. This also gives a determinant-only obstruction for every $r=2,d\ge4$, since (2) rules out $d>4$ immediately.

For $U(2,4)$, the forced weights (3) at $\alpha=0$ produce a real-rooted polynomial exactly through fifteen rows. At every $n\ge16$ they produce nonreal zeros. [Exact fourth-power-sum and finite certificates](factorial-weight-four.md) · [Independent agent-assisted review of the method classification and threshold](review-scalar-determinant.md)

The method classification leaves open the original real-rootedness of balanced arrays outside the previously proved families. It identifies an obstacle for any extension of the corank-one determinant using these scalar states. **⬜ None.** The theorem has a written argument. [Corank-one proof](no-full-row.md) · [Four-column paired refinement](paired-stability.md)
