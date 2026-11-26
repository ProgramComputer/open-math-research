# An effective far-left edge for strict Catalan peaks

For each $n\ge3$, the strict-peak polynomial $C_n(t)$ has a simple negative zero whose modulus strictly exceeds that of every other zero, including nonreal zeros. For every even $n\ge4$, its modulus lies strictly below the largest modulus in each of rows $n-1,n+1$, and strictly above the modulus of every other zero in those two odd rows. This gives the outermost consecutive alternation in every size. It leaves the inner ranks outside the scope of this result. The prior eventual theorem gives fixed-index outer alternation with an existential cutoff. [Alexandersson's conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjCatalanWordPeaks) · [Prior eventual result, §3](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/alexandersson-catalan-peaks/EVENTUAL-ZEROS.md)

## Exact coefficient ratios

Write $n=2m+\delta$, $\delta\in\{1,2\}$. Let $a_{n,j}=[u^j]C_n(1+u)$, $u_j=a_{n,m-j}/a_{n,m}$, and use the coordinate $z=u_1/(1-t)$ for $m\ge1$. A nonzero multiple of the reciprocal polynomial in $z$ is
$$
F_{m,\delta}(z)=\sum_{j=0}^m (-1)^j r_j z^j,
\qquad r_j=u_j/u_1^j.
$$
Here $r_0=r_1=1$. All zeros of $C_n$ correspond to nonzero zeros of $F_{m,\delta}$ since $t=1$ is not a zero and the constant term in $F_{m,\delta}$ is one.

The factorial coefficient formula gives, for $1\le j\le m$ and
$D_j=(\delta+2j)(\delta+2j-1)^2(\delta+2j-2)$,
$$
\frac{u_j}{u_{j-1}}
=(m-j+1)\prod_{i=1}^3(m+2\delta+3(j-1)+i)\,
        \frac{m+\delta+j-1}{(m+\delta+j+1)D_j}.
\tag{1}
$$
For $m\ge20$, the resulting bounds are
$$
\begin{array}{c|cc}
 & r_2 & r_j/r_{j-1} \ (j\ge3)\\
\hline
\delta=1 & <7/100 & <11/500\\
\delta=2 & <4/25 & <1/15 .
\end{array}
\tag{2}
$$

For the first column of (2), the exact value of $r_2$ is $(D_1/D_2)N(m)/B(m)$ for the products
$$
\begin{aligned}
N(m)&=(m-1)(m+\delta+1)(m+\delta+2)
                \prod_{i=4}^6(m+2\delta+i),\\
B(m)&=m(m+\delta)(m+\delta+3)\prod_{i=1}^3(m+2\delta+i).
\end{aligned}
$$
For $\delta=1$ and $\delta=2$, respectively, $D_1/D_2$ is $1/20$ and $3/25$. The polynomial $140B(m)-100N(m)$ for $\delta=1$ has positive coefficients on substituting $m=20+s$, as does $4B(m)-3N(m)$ for $\delta=2$. This proves the first column. For the second, (1) yields
$$
\frac{r_j}{r_{j-1}}\le
  \left(1+\frac2{m+\delta}\right)\frac{D_1}{D_3}
  \left(1+\frac{3(j-1)}{m+2\delta+1}\right)^3
  \left(\frac{\delta+6}{\delta+2j}\right)^4.
$$
In deriving this inequality use $m-j+1\le m$ and $D_j/D_3\ge[(\delta+2j)/(\delta+6)]^4$. The last two factors together decrease for real $j\ge3$: their logarithmic derivative is
$$
\frac9{m+2\delta+3j-2}-\frac8{\delta+2j}<0.
$$
The resulting bound at $j=3$ decreases in $m$, and substitution of $m=20$ gives the stated rational bounds.

## Isolation and consecutive order

On $|z|=8$ for the odd row, (2) bounds the difference between $F_{m,1}(z)$ and $1-z$ in absolute value by
$$
\frac{(7/100)8^2}{1-(11/500)8}<7\le |1-z|.
$$
On $|z|=3/2$ for the even row the analogous bound is
$$
\frac{(4/25)(3/2)^2}{1-(1/15)(3/2)}<1/2\le |1-z|.
$$
Rouché's theorem gives one simple real zero inside the respective circle. The root lies in $(1,5/4)$ in both cases. Indeed, at $z=1$ the tail starting at $j=2$ alternates with strictly decreasing magnitudes and starts positive. At $z=5/4$ the same tail is at most $r_2(5/4)^2<1/4$, so the polynomial is negative there.

Denote $u_1$ in the two parities by $U_{\mathrm o}(m),U_{\mathrm e}(m)$. Formula (1) gives
$$
U_{\mathrm o}(m)=\frac{m(m+1)(m+4)(m+5)}{12},\qquad
U_{\mathrm e}(m)=\frac{m(m+2)(m+5)(m+6)(m+7)}{72(m+4)}.
$$
For $m\ge20$ these are larger than $40$. The isolated root is a negative real zero with $|1-t|>4u_1/5$, hence $|t|>4u_1/5-1$. All other roots satisfy $|1-t|<2u_1/3$, hence $|t|<2u_1/3+1<4u_1/5-1$. The odd row's stronger isolation gives $|1-t|<U_{\mathrm o}(m)/8$ for every other root.

The two comparisons with a fixed even row follow from
$$
\frac{U_{\mathrm o}(m)}{U_{\mathrm e}(m)}
 =6\,\frac{m+1}{m+2}\frac{m+4}{m+6}\frac{m+4}{m+7},
\qquad
\frac{U_{\mathrm o}(m+1)}{U_{\mathrm e}(m)}
 =6\,\frac{(m+1)(m+4)}{m(m+7)}.
$$
Both lie in $(4,6)$ for $m\ge20$. In the first expression the factors increase in $m$ and are less than one. For the second, use $(m+1)(m+4)<m(m+7)$ for $m>2$ and the lower bound $6(m+4)/(m+7)$. Each isolated odd root then has $|1-t|>(4/5)4U_{\mathrm e}(m)$, whereas the even one has $|1-t|<U_{\mathrm e}(m)$. All other odd roots obey $|1-t|<(3/4)U_{\mathrm e}(m)$. Since $U_{\mathrm e}(m)>40$,
$$
(3/4)U_{\mathrm e}(m)+1<(4/5)U_{\mathrm e}(m)-1.
$$
Thus the ordering in ordinary modulus holds against all roots of either odd row, with no need for those other roots to be real.

The analytic pair result begins with even $n=42$. For the finite prefix the checker reconstructs rows $3$ through $43$, counts their roots on the positive axis after $t\mapsto-t$, and isolates the largest one or two roots by exact rational Sturm bisection. Disjoint dyadic brackets establish both odd-neighbor comparisons for each even row $4$ through $42$. In pairs with a single root per row the inequalities involving other zeros are vacuous.
