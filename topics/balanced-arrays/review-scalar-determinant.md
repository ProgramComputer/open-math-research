# Independent review of the balanced-array determinant obstruction

Agent-assisted mathematical review, 2026-11-25.

## Verdict

The reviewed arguments are valid for fixed positive weights with $w_0=w_1=1$. For every $1\le r\le d-2$ and every real $\alpha$, they rule out simultaneous all-row real-rootedness and a nested unit lower triangular entrywise nonnegative scalar representation $T_n(q)=\det(A_n-qU_n)$. For $r=2$, $d\ge4$ the determinant alone is impossible for every real $\alpha$. For general $1\le r\le d-2$, the determinant alone is impossible when $\alpha\ge d$. Whether the original unweighted balanced-array polynomials are real-rooted remains a separate question. [Primary conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

## Degree and analyticity obstruction

For fixed $d,r,k$, let $g_{s,k}$ count the arrays with $s$ ordered nonempty rows and all column sums equal to $k$. Choosing their row positions gives

$$
a(n,k)=\sum_{s=0}^{dk}\binom ns g_{s,k}.
$$

The degree of $T_n$ is $D_n=\lfloor nr/d\rfloor$. The upper bound is the total row capacity. For attainment, place the $dk$ entries as $d$ consecutive blocks of length $k$ in the sequence of row indices taken modulo $n$. Each block uses distinct rows, and each row appears at most $\lceil dk/n\rceil\le r$ times. Positivity of all weights gives the claimed degree. The case $n=0$ gives degree zero.

Write $b_{n,k}=[q^k]T_n$ and $e=d-\alpha$. The polynomial formula and the analytic factors $(1-i/n)^{-\alpha}$ give $b_{n,k}=n^{ek}\beta_k(1/n)$ for a function $\beta_k$ real analytic near zero and all sufficiently large $n$. The last-row determinant expansion is

$$
T_n=\sum_{j=0}^{n-1}A_{n,n-j}q^j T_{n-j-1},
\qquad A_{n,n}=1.
$$

Matching coefficient $j$ determines $A_{n,n-j}$ by subtracting $b_{n-1,j}$ and the terms $A_{n,n-l}b_{n-l-1,j-l}$ for $1\le l<j$ from $b_{n,j}$. Thus $A_{n,n-j}=n^{ej}\gamma_j(1/n)$ by induction. In the induction, a shift from $n$ to $n-u$ replaces $\beta_k(t)$ by $(1-ut)^{ek}\beta_k(t/(1-ut))$, analytic at zero. Each fixed diagonal must therefore be eventually zero or eventually strictly positive.

Set $s=r/d$. An entry at distance $j>(1+s)/(1-s)$ must vanish, since $j+\lfloor(n-j-1)s\rfloor>\lfloor ns\rfloor$ and each determinant recurrence term has nonnegative coefficients. This gives a finite overall bound on the possible diagonals. Once the set $J$ of nonzero diagonals stabilizes, the recurrence for degrees reads $D_n=\max_{j\in J}(j+D_{n-j-1})$, with $0\in J$. Put $\gamma=\max_{j\in J}j/(j+1)$. Induction gives $D_n\le\gamma n+O(1)$ and repeatedly using a maximizing $j$ gives $D_n\ge\gamma n-O(1)$. Consequently $s=\gamma$, so $d-r$ divides $d$. For $r=2$ and $d\ge4$ this leaves only $d=4$.

## Density one half

Suppose $d=2r$ with $r\ge2$. For odd $n\ge3$ the distance-two entry must vanish, since its contribution would have degree $2+\lfloor(n-3)/2\rfloor>\lfloor n/2\rfloor$. Put $b_n=b_{n,1}$, $c_n=b_{n,2}$, and $W=w_2/2^d$. Matching coefficients gives $\Delta b_n\ge0$ and, along odd $n$,

$$
\Delta c_n=\Delta b_n\,b_{n-2}.
$$

For fixed $k$ draw the occupied rows uniformly and independently in each column. A specified row has occupancy distributed as $\operatorname{Binomial}(d,k/n)$. Its forbidden probability gives

$$
\Pr(\mathrm{valid})=1-Ck^{r+1}n^{-r}+Dk^{r+2}n^{-r-1}+O(n^{-r-2}),
\quad C=\binom d{r+1},\quad D=(r+1)\binom d{r+2}.
$$

Indeed, across a pair of distinct forbidden rows one can select a witness of $r+1$ columns per row. A column with $m=1$ or $2$ forced entries has inclusion probability $(k)_m/(n)_m$, so a specified pair contributes $O(n^{-2r-2})$. Summing over pairs gives $O(n^{-2r})$, which is $O(n^{-r-2})$ for $r\ge2$. Here $D>0$. Analyticity of the exact normalized coefficients, including the probability, follows from the polynomial array count and enables termwise first differences.

If $e<0$, $b_n\sim n^e\to0$ contradicts monotonicity and eventual positivity. If $e>0$, the expansions are

$$
\begin{aligned}
\Delta c_n&=W\left(2e n^{2e-1}-2e(2e-1)n^{2e-2}+O(n^{2e-3})\right),\\
\Delta b_n\,b_{n-2}&=e n^{2e-1}-\tfrac12(5e^2-e)n^{2e-2}+O(n^{2e-3}).
\end{aligned}
$$

The leading terms force $W=1/2$. The difference of the next coefficients is $e(e+1)/2>0$, a contradiction. This comparison holds for each fixed $e>0$ even when the displayed powers of $n$ are negative.

If $e=0$, the leading differences force $W=2^{-r-1}$. It follows that $c_n-b_n=W-1+D n^{-r-1}+O(n^{-r-2})$. The odd-index condition becomes $\Delta(c_n-b_n)=\Delta b_n(b_{n-2}-1)$. The left side is $-(r+1)D n^{-r-2}+O(n^{-r-3})$ and the right side is $O(n^{-2r-1})$, again incompatible.

## Original argument with real-rootedness

For $r=2$, $0\le\alpha<d$ and arbitrary positive fixed weights as above, the determinant recurrence implies coefficientwise

$$
T_n\ge T_{n-1}+q\Delta b_n T_{n-2}.
$$

The resulting lower bound for $[q^k]T_n$ sums products of $k$ increments $\Delta b_i$ at pairwise nonadjacent indices. Since $b_i\sim i^e$ and $e>0$, $\Delta b_i/b_i\to0$ on the eventually positive indices. Monotonicity and $b_n\to\infty$ then give $\max_{i\le n}\Delta b_i/b_n\to0$. Sampling indices independently with probabilities $\Delta b_i/b_n$, the chance any two indices coincide or are adjacent is at most $3\binom{k}{2}\max_{i\le n}\Delta b_i/b_n$. The lower bound after division by $b_n^k$ therefore tends to $1/k!$. If $T_n$ has all real roots, its nonnegative coefficients and unit constant imply negative roots. Writing its coefficients as elementary symmetric functions of the positive reciprocals of their absolute values gives the upper bound $[q^k]T_n\le b_n^k/k!$. The normalized coefficient limit is also $w_k/(k!)^d$, so $w_k=(k!)^{d-1}$.

For these factorial weights the previous probability expansion gives, with $C_j=\binom dj$,

$$
\frac{b_{n,k}}{n^{ek}}
=\frac1{k!}\left(\frac{(n)_k}{n^k}\right)^e
\left(1-C_3k^3n^{-2}+3C_4k^4n^{-3}+O(n^{-4})\right).
$$

Taking logarithms of the falling-factorial factor gives coefficients $-e\sum_{i=0}^{k-1}i^j/j$ at $n^{-j}$ for $j=1,2,3$. Substituting into the fourth Newton power sum yields

$$
b_{n,1}^4-4b_{n,1}^2 b_{n,2}+2b_{n,2}^2+4b_{n,1}b_{n,3}-4b_{n,4}
=n^{4e-3}\left(\frac{8e^3-6e^2+e-36C_3e-36C_4}{3}+O(n^{-1})\right).
$$

The coefficient has derivative $\bigl(24e^2-12e+1-36C_3\bigr)/3$, with roots of opposite sign, so its maximum on $[0,d]$ is at an endpoint. At zero it is $-12C_4<0$. At $d$ the value is $-d(15d^3-70d^2+69d-20)/6$, whose parenthesis has coefficients $96,229,110,15$ in ascending powers of $d-4$. The eventual negative fourth power sum contradicts all real roots for these factorial weights whenever $0\le e\le d$, including $e=0$.

For the original $d=4$, $\alpha=4$ argument with arbitrary weights, real-rootedness gives $c_n\le b_n^2/2$. The limits $c_n\to w_2/16$ and $b_n\to1$ force $w_2\le8$. Direct counts give $a(2,1)=6$, $a(3,1)=54$, $a(4,1)=204$ and $a(4,2)=90$, hence $A_{4,2}=5w_2/1152-25/512\le-65/4608$.

## Extension to every cap at most $d-2$

The argument forcing factorial weights when $e>0$ applies for every $1\le r<d$. It uses only $b_{n,k}\sim w_k n^{ek}/(k!)^d$ for fixed $k$, which follows since the validity probability $F_{n,k}$ is $1+O(n^{-r})$. With the forced weights, $b_{n,k}=(n)_k^e F_{n,k}/k!$. Define $u_{n,j}=n^eA_{n,n-j}/(n)_{j+1}^e$. Dividing the matched coefficient by $(n-1)_k^e/k!$ yields

$$
(1-k/n)^{-e} F_{n,k}-F_{n-1,k}
=\sum_{j=1}^k(k)_j u_{n,j} F_{n-j-1,k-j}.
$$

The reference equation with all validity probabilities replaced by $1$ is the Newton expansion in the falling factorial basis. Its coefficients are $u^0_{n,j}=\Delta_k^j(1-k/n)^{-e}|_{k=0}/j! = e(e+1)\cdots(e+j-1)/(j!n^j)+O(n^{-j-1})$. At fixed $k$, the left side differs from the reference by $O(n^{-r-1})$ by analyticity at $1/n=0$. The factors on the right differ from $1$ by $O(n^{-r})$, and $u^0_{n,j}=O(n^{-1})$ for $j\ge1$. At each new $k$ the final factor $F_{n-k-1,0}=1$ and its scalar coefficient is $k!$. Induction thus gives $u_{n,j}-u^0_{n,j}=O(n^{-r-1})$ for fixed $j$. In particular $A_{n,n-r}>0$ for all sufficiently large $n$. The corresponding degree jump gives asymptotic slope at least $r/(r+1)$, which exceeds $r/d$ for every $r\le d-2$.

When $e<0$ the same linear-coefficient monotonicity argument applies to every cap. It remains to check $e=0$. The degree obstruction excludes $r=1$ when $d\ge3$. For $2\le r\le d-2$, every diagonal at distance greater than $J=\lfloor r/(d-r)\rfloor$ is eventually zero, since any eventual positive diagonal would impose slope at least $j/(j+1)$. Set $h_k=w_k/(k!)^d$, $H=\sum_k h_kq^k$ as a formal series, and $\theta=q\partial_q$. The expansion for $F_{n,k}$ in the density-one-half proof holds here with the same $C,D>0$. Thus the coefficients of $n^{-r-1}$ and $n^{-r-2}$ in $T_n-T_{n-1}$, taken coefficientwise in $q$, are respectively

$$
rC\theta^{r+1}H
\quad\text{and}\quad
\frac{r(r+1)}{2}C\theta^{r+1}H-(r+1)D\theta^{r+2}H.
$$

Triangular matching gives $A_{n,n-j}=O(n^{-r-1})$ for fixed $j$ and these entries are analytic in $1/n$. The shifted $T_{n-j-1}$ differs from $H$ by $O(n^{-r})$ coefficientwise. In the determinant recurrence their product error is $O(n^{-2r-1})$, beyond both displayed orders since $r\ge2$. Hence those orders on the right are each $H$ times a polynomial of degree at most $J$. It follows that $P=\theta^{r+1}H/H$ and $Q=\theta^{r+2}H/H$ are polynomials of degree at most $J$. The series for $P$ starts with $h_1q$, so $P$ is nonconstant. The identity $Q=\theta P+P\theta H/H$ gives $S=\theta H/H=(Q-\theta P)/P$ as a rational function. Every $R_m=\theta^mH/H$ is rational by $R_0=1$ and $R_{m+1}=\theta R_m+SR_m$. If $S$ is bounded at infinity, this recurrence makes every $R_m$ bounded there, contradicting nonconstant $R_{r+1}=P$. If $S\sim c q^M$ at infinity with $M\ge1$, the recurrence gives $R_m\sim c^m q^{mM}$. This makes $\deg P\ge r+1>J$, also a contradiction.

## Independent exact check at $d=4$, $r=2$, $\alpha=0$

For factorial weights, the companion script counts arrays by sorted margin vectors and uses a primitive integer Sturm sequence on each polynomial for $0\le n\le75$. The check gives real-rootedness exactly when $n\le15$ in this range. At $n=16$ and $n=17$ the degree is eight and six roots are negative, with squarefree polynomials. It also computes the polynomial fourth power sum using the counts $g_{s,k}$ for $k\le4$ and $s\le16$. All fourteen coefficients in powers of $n-76$ are strictly negative, which rules out all real roots whenever $n\ge76$. Run the check with `python3 topics/balanced-arrays/code/rank-two-review-exact.py`.

No Lean or Rocq verification was part of this review.
