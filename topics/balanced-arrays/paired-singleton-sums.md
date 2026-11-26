# Pairing adjacent uniform singleton slices

In the uniform four-column cap-two array, the quota polynomial restricted to exactly two or exactly four singleton rows has only negative nonzero roots, all simple, for $n\ge3$ labeled rows. These roots strictly interlace in consecutive rows. The argument gives a criterion for combining any two slices with $4r-2$ and $4r$ singleton rows.

Use $h=\lceil s/2\rceil$ and $U_s(q)=q^{-h}T_s(q)$ from [the uniform comparison note](uniform-bessel-comparison.md). The slice for $2s$ singleton rows is
$$
(n)_{2h+s}q^h\sum_{j\ge0}(n-2h-s)_{2j}[q^j]U_s(q)\,q^j
$$
if $n\ge 2h+s$, and is zero otherwise. Here $(a)_b$ is the falling factorial. The paired slices $s=2r-1,2r$ have the same $h=r$, and their minimum occupied row counts are $4r-1$ and $4r$.

## Comparing the entire functions for two and four singletons

Set $u=z^2$, $a(u)=U_1(-u)$, $b(u)=U_2(-u)$,
$A=J_0(2z)=F(-u)$, $B=J_1(2z)=zG(-u)$, and $R=G(-u)/F(-u)$. Off the poles,
$$
a(u)=2G(-u)A^2(3-uR^2),
\qquad
\frac{b(u)}{A^3}=\frac{16-12R+3R^2-R^3}{6}+(2R-8)uR^2.
$$
These are the explicit two- and four-singleton formulas in [the fixed-count note](four-singletons.md). There are no zeros of $a$ at the poles of $R$. At a positive zero of $a$, the ratio $B/A$ is one of $-\sqrt3,0,\sqrt3$. The value of $b/A^3$ at level zero is $8/3$. At either other level it is
$$
\frac{-R^3+3R^2+24R-128}{6}<0.
$$
For the negative level, the first positive pole has already been passed. Its $z$ coordinate is greater than $1$ by the alternating series for $F(-u)$ on $0\le u\le1$. Hence $R>-\sqrt3>-2$. For the positive level $R>0$. The cubic has derivative $-3(R-4)(R+2)$, and its values at $-2$ and $4$ are negative, so the claimed sign holds on $[-2,\infty)$.

On the positive axis the ratio $B/A$ increases from zero to $+\infty$ before its first pole, and from $-\infty$ to $+\infty$ in each pole gap. This follows from the paired partial fractions in the uniform comparison note. The sign of $A$ flips at each pole. At the first zero of $a$, where $B/A=\sqrt3$, we have $b<0$. The subsequent signs of $b$ at the zeros of $a$ alternate. Within each pole gap the three levels are $-\sqrt3,0,\sqrt3$, with the middle sign opposite to each outside sign. Passing a pole from level $\sqrt3$ to $-\sqrt3$ also reverses the sign of $b$.

Since $b(0)>0$, there is a zero of $b$ before the first zero of $a$, and one between each pair of successive zeros of $a$. These zeros exhaust the count. Take a circle in $z$ with radius the $j$th positive zero of $B$, for arbitrarily large $j$. By the even comparison in the uniform note, $b(z^2)$ has the same zero count inside as $A(A^2-3B^2)$. With $z>0$, the latter has one pole of $B/A$ and one crossing of each of the levels $\pm1/\sqrt3$ in each of the first $j$ gaps cut out by $B$, including the initial gap from zero. There are therefore $3j$ positive comparator zeros inside the circle. There are exactly $3j$ positive zeros of $a(z^2)$ up to and including the positive radius, from the three levels $\pm\sqrt3,0$. Their alternating signs for $b$ give at least $3j$ positive zeros of $b(z^2)$ strictly inside, and their negatives supply the entire comparison count. Thus the positive zeros of $a$ and $b$, written as $\alpha_j$ and $\beta_j$ in the $u$ variable, satisfy
$$
0<\beta_1<\alpha_1<\beta_2<\alpha_2<\cdots
$$
and all are simple.

## From entire functions to labeled polynomials

Suppose $a(u)=U_{2r-1}(-u)$ and $b(u)=U_{2r}(-u)$ have the alternating positive zeros just stated and no others. Both functions have order at most $1/2$, since the finitely many products from the fixed-count formula have that bound. Thus their entire factorizations have genus zero. Truncate those products to the same number of factors. The ratio of the two truncated polynomials has negative residues at the zeros of the denominator, and is a real constant plus its simple partial fractions. The sign follows by substituting each $\beta_j$ into the numerator and the denominator derivative. Hence the ratio has positive imaginary part on the upper half-plane. The truncated products converge locally uniformly, and
$$
\left(\frac ab\right)'(0)
=\frac{a(0)}{b(0)}\sum_j\left(\frac1{\beta_j}-\frac1{\alpha_j}\right)>0.
$$

For an integer $N\ge0$ define $\Gamma_N$ on entire functions by multiplying the coefficient of $u^j$ by $(N)_{2j}$, interpreted as zero for $2j>N$. This is a real-rootedness preserver on polynomials. Its exponential generating polynomial $\sum_j(N)_{2j}q^j/j!$ has only negative zeros. Indeed its reflected reciprocal $x^N\sum_j(N)_{2j}(-x^{-2})^j/j!$ is $H_N(x/2)$, with $H_N$ the physicists' Hermite polynomial. Hermite orthogonality gives real zeros, and reflection gives negative zeros of the exponential generating polynomial. The multiplier-sequence criterion then applies. [Pólya and Schur, 1914](https://doi.org/10.1515/crll.1914.144.89)

The equal-length factor truncations of $a$ and $b$ form a real-rooted pencil by the partial fractions. Applying $\Gamma_N$ and taking the limit shows that $D_1+tD_2$ is real-rooted whenever it is nonzero, for all real $t$, where $D_1=\Gamma_N a$ and $D_2=\Gamma_N b$. When $N\ge2$, the ratio $D_1/D_2$ has derivative $(N)_2(a/b)'(0)>0$ at zero. Since $D_2$ has only real roots and the pencil is real-rooted, the nonconstant ratio cannot take a real value in the upper half-plane. Its imaginary part is positive there by the sign of its derivative at zero. The slice argument in the fixed-count note, applied to the even entire product $b(z^2)$, gives simple positive roots of $D_2$.

Factoring out $(n)_{4r-1}q^r$ from the sum of the labeled slices and putting $N=n-(4r-1)$, the remaining polynomial at $q=-u$ is
$$
D_1(u)+N D_2(u)-2uD_2'(u).
$$
In fact $(n)_{4r}(N-1)_{2j}=(n)_{4r-1}(N)_{2j}(N-2j)$, with zero terms included. When $N=0$ the second slice is empty and when $N=1$ both reduced polynomials are constant.

For $N\ge2$, division by $D_2$ gives a function with positive imaginary part in the upper half-plane. In addition to $D_1/D_2$, each root $\rho>0$ of $D_2$ contributes $2u/(\rho-u)$, which has positive imaginary part. This excludes nonreal roots by conjugation. At any pole $\rho$, the residue from $D_1/D_2$ is nonpositive, and the residue from the second term is $-2\rho<0$. Thus the polynomial has no zeros at the poles. Off the poles its zeros are simple because the derivative of the ratio on the real axis is strictly positive. This follows by expanding the rational function $D_1/D_2$ into its nonpositive-residue partial fractions and differentiating. There is no zero with $u\le0$, since the original polynomial in $q$ has nonnegative coefficients and a positive constant after removing the forced factor. Therefore all the nonzero roots of the original sum are simple and negative. The reduced polynomial has degree $\lfloor N/2\rfloor$, since the earlier-starting slice alone has a positive coefficient at each admissible degree.

## Strict consecutive interlacing

For $M\ge0$ define the reflected polynomials
$$
f_M(x)=x^M(\Gamma_M a)(x^{-2}),\qquad
g_M(x)=x^M(\Gamma_M b)(x^{-2}),\qquad
H_M(x)=f_M(x)+xg_M'(x).
$$
The last expression is $x^M$ times the reduced paired quota polynomial at $q=-x^{-2}$. Both $f_M$ and $g_M$ are Appell sequences. Hence for $M\ge1$,
$$
H_M'=M(H_{M-1}+g_{M-1}),\qquad g_M'=Mg_{M-1}.
$$
The reduced quota polynomial has degree $d=\lfloor M/2\rfloor$ with nonzero coefficient at that degree. Therefore $H_M$ has a zero of multiplicity $M-2d$, which is zero for even $M$ and one for odd $M$. The $d$ positive zeros correspond exactly to the $d$ negative quota roots, and parity gives $d$ matching negative zeros. The origin zero for odd $M$ is introduced by the reflection and is not a root of the reduced quota polynomial.
At a positive root $t$ of $H_M$, the preceding pole calculation gives $g_M(t)\ne0$. The function $H_M/g_M$ is the strictly increasing quotient in the $u$ variable, now evaluated at $u=x^{-2}$. In particular $H_M'(t)/g_M(t)<0$. Also
$$
\begin{aligned}
\frac{M H_{M-1}(t)}{g_M(t)}
&=(H_M/g_M)'(t)-(\log|g_M|)'(t)\\
&=(f_M/g_M)'(t)+t(\log|g_M|)''(t)<0.
\end{aligned}
$$
The first term in the last line is nonpositive since $f_M/g_M$ is the quotient $D_1/D_2$ evaluated at $x^{-2}$. The second is strictly negative since $g_M$ is a nonconstant real-rooted polynomial and $(\log|g_M|)''=-\sum_\rho (x-\rho)^{-2}$ with real roots $\rho$ counted with multiplicity.

Thus $H_{M-1}$ has the sign of $H_M'$ at every positive root of $H_M$. Its roots occupy every gap between those positive roots. For even $M=2d$, the old degree in $q$ is $d-1$ and the new degree is $d$, so the gaps account for all the old roots. For odd $M=2d+1$ with $d>0$, the degrees in $q$ are both $d$ and there is one remaining old root. It lies to the left of the first positive new root because the signs of $H_{M-1}$ at the largest positive new root and at positive infinity are both positive. The map $x\mapsto-x^{-2}$ is strictly increasing for $x>0$, so these are the same interlacing orders in $q$. The rows with $N=0,1$ are constant after removal of $q^r$, so the first consecutive pair has two empty root lists. The next pair has an empty old list and one new root. A row with $n<4r-1$ contains neither slice and is the zero polynomial, outside the assertion. The condition on alternating zeros of the two entire functions has been checked above for $r=1$ and remains open for higher pairs.

## Exact reconstruction

The [integer labeled-row checker](code/verify_singleton_slices.py) independently reconstructs each slice by adding one of the 11 allowed row types to a four-column state, with the cardinality of the singletons tracked separately. Its [record](results/singleton-slices.json) contains all 52 uniform slices for $n=0,\ldots,12$ with zero, two, four or six singleton rows, 27 weighted fixed-distribution slices, and nine weighted two-singleton slices. The proof of the root counts above is independent of these checks.
