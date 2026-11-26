# The paired-margin enumerator is stable exactly through five rows

For an array with four labeled columns and at most two ones per row, let $c_{n,i,j}$ count the $n$-row arrays with margins $(i,i,j,j)$. Define $F_n(x,y)=\sum c_{n,i,j}x^iy^j$. Its equal-exponent diagonal is the original $U(2,4)$ polynomial. The result below concerns the two-variable polynomial before taking that diagonal. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**Proposition.** $F_n$ is real stable exactly for $0\le n\le5$. Here stability means nonvanishing whenever both imaginary parts are positive. At six rows the original diagonal is $1+1170q+20610q^2+1860q^3$ and has three negative real roots.

## Why stability would have sufficed

Let $F(x,y)=\sum c_{ij}x^iy^j$ be real stable with nonnegative coefficients and total degree $N$. Then $\sum k!c_{kk}q^k$ and $\sum c_{kk}q^k$ each have only nonpositive real roots whenever they are nonzero.

Indeed, the homogenization $H(x,y,z)=z^NF(x/z,y/z)$ is real stable by Borcea, Brändén and Liggett, Theorem 4.5. For $m\ge1$, $1-xy/m$ is stable since two numbers in the open upper half-plane cannot have positive real product. Multiplication by this polynomial preserves stability. Its Fischer–Fock dual $1-\partial_x\partial_y/m$ also preserves stability by Borcea and Brändén, Theorem 1.11. Taking $m$ iterates and then a coefficientwise limit gives the same property, up to the zero polynomial, for $\exp(-\partial_x\partial_y)$. Specializing $x=y=0$ yields the real-rooted polynomial
$$
\sum_k (-1)^k k!c_{kk} z^{N-2k}.
$$
For any nonzero root $w$ of the first claimed polynomial, every solution of $-1/z^2=w$ must therefore be real. This forces $w<0$. Applying the multiplier $1/k!$ gives the second assertion. This implication uses bivariate stability and nonnegative coefficients. [Homogenization, Theorem 4.5](https://doi.org/10.1090/S0894-0347-08-00618-8) · [Fischer–Fock duality, Theorem 1.11](https://doi.org/10.1112/plms/pdp049) · [Elementary factorial multiplier proof](no-full-row.md#return-to-the-original-polynomials-and-strict-interlacing)

## The first seven nonempty sizes

In a pair of columns supported on disjoint rows the common quota has polynomial
$$
f_j(x)=\sum_{2k\le j}\binom{j}{2k}\binom{2k}{k}x^k.
$$
Select the $h$ rows containing both ones in the same pair of columns. Each such row is $1100$ or $0011$. On the remaining rows the two pairs have independent disjoint supports, so
$$
F_n(x,y)=\sum_{h=0}^n\binom nh(x+y)^h f_{n-h}(x)f_{n-h}(y).
$$
Its total degree is $n$, with coefficient one at $x^n$.

This decomposition also gives a positive partial theorem. Each individual nonzero $h$-slice has a real-rooted diagonal, even after multiplying its $k$th coefficient by $k!$. Indeed $f_j$ is the cap-one polynomial for two columns and has negative real zeros. Thus $(x+y)^h f_{n-h}(x)f_{n-h}(y)$ satisfies all the hypotheses of the preceding implication. The slices do not retain this property under arbitrary positive mixing. At $n=4$ the $h=0,4$ diagonal polynomials are $1+144q+36q^2$ and $6q^2$. Giving the second weight $1000$ produces discriminant $-3408$. The sum prescribed by the array definition uses weight one on every slice. [Cap-one proof](finite-linear-reduction.md)

Set $p_n(t,s)=F_n(t+s,t-s)$. Its leading coefficient in $t$ is positive and independent of $s$. The discriminant with respect to $t$ is a polynomial $D_n(s^2)$ by symmetry. Signed Euclidean sequences give the following exact data. The last two columns are the sign variations of the Sturm sequence of $D_n$.

| $n$ | Distinct real roots of $p_n(t,0)$ | $V(0)$ | $V(+\infty)$ |
|---:|---:|---:|---:|
| 1 | 1 | 0 | 0 |
| 2 | 2 | 0 | 0 |
| 3 | 3 | 1 | 1 |
| 4 | 4 | 2 | 2 |
| 5 | 5 | 4 | 4 |

In each row $D_n(0)>0$. Hence $D_n$ has no root on $[0,\infty)$ and all the $t$-roots stay real and distinct at every real $s$. Homogenize $F_n$ to degree $n$ and choose the direction $(1,1,0)$. On a line whose third coordinate is nonzero, scaling by that coordinate and translating $t$ gives one of the tested line families. At third coordinate zero the conclusion follows by continuity, since the leading coefficient stays positive. The homogenization is therefore hyperbolic in this nonnegative direction, so Theorem 4.5 above gives stability. The empty case is $F_0=1$.

At $n=6$, choose $s=16$. The resulting polynomial is
$$
3584t^6+29952t^5-1623660t^4-11046640t^3+
210341460t^2+941322312t-6258872319.
$$
Its Sturm chain has degrees $6,5,4,3,2,1,0$ and leading signs $+,+,+,+,+,+,-$. The variations at $-\infty$ and $+\infty$ are five and one, respectively. At $n=7$ the same calculation with $s=20$ gives five real roots of a degree-seven polynomial. In both cases there is a nonreal conjugate pair. A root $t$ in the open upper half-plane places both arguments $t+s,t-s$ there.

## The obstruction at every higher row count

On $y=0$ write $S_n(x)=F_n(x,0)=\sum_i\binom ni^2 x^i$. Setting the other two columns to zero leaves two independent $i$-subsets. The standard binomial expansion of the Legendre polynomial $L_n$ gives $S_n(x)=(1-x)^n L_n((1+x)/(1-x))$. Its zeros are simple, negative and strictly interlace those of $S_{n-1}$. With positive leading coefficients this implies $S_{n-1}(r)/S_n'(r)>0$ at each root $r$ of $S_n$. [Legendre recurrence](https://dlmf.nist.gov/18.9) · [Zeros](https://dlmf.nist.gov/18.16)

Let $G_n=[y]F_n$. If the two quota-one columns occupy the same row, the other pair must avoid that row. If they occupy two distinct rows, each of these two rows forbids the other pair from occupying both positions. Inclusion–exclusion in those rows gives
$$
G_n=nS_{n-1}+n(n-1)(S_n-2xS_{n-1}+x^2S_{n-2}).
$$
The Legendre recurrence gives $nS_n=(2n-1)(1+x)S_{n-1}-(n-1)(1-x)^2 S_{n-2}$. Evaluating at $S_n(r)=0$ therefore yields
$$
\frac{G_n(r)}{n S_{n-1}(r)}
=\frac{1-2nr+(6n-4)r^2+r^3}{(1-r)^2}.
$$
For $r=-R$ and $R\ge6n-3$ the numerator is at most $1+2nR-R^2<0$ for $n\ge 2$. Thus the analytic root of $F_n(x,y)$ through $(r,0)$ has positive derivative $-G_n(r)/S_n'(r)$ in $y$. At $y=i\epsilon$ with $\epsilon>0$ sufficiently small this root has positive imaginary part, disproving stability.

Write $R_j$ for the positive moduli of the zeros of $S_n$. Its two highest nonleading coefficients give
$$
\sum R_j=n^2,\qquad \sum R_j^2=n^2(n^2+2n-1)/2.
$$
Their quotient is a weighted average of the $R_j$. Thus $\max R_j\ge(n^2+2n-1)/2\ge6n-3$ for $n\ge10$. At $n=8$ and $9$, respectively, $S_8(-48)=-577709571071$ and $S_9(-55)=391474884215196$. Both signs are opposite the sign at $-\infty$, giving roots of sufficient modulus. This completes the classification.

The checker constructs all margins twice, from labeled row choices and from the paired formula, for $0\le n\le7$. It reproduces each Sturm count and the two integer boundary signs. With python-flint 0.9.0 installed, run

~~~sh
python -I -B topics/balanced-arrays/code/verify_paired_stability.py
~~~

**⬜ None.** This auxiliary classification has an exact computational certificate and a written argument. The general four-column diagonal remains open. Stability of the full paired enumerator would be stronger than needed. The remaining candidate is the univariate factorial-weighted diagonal above, which would suffice by itself. [Verification code](code/verify_paired_stability.py) · [Source and prior work](no-full-row-literature.md)
