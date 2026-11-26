# Four columns with prescribed singleton rows

Take four labeled columns of common sum $k$. Empty rows have weight one,
singleton rows in column $i$ have weight $v_i>0$, and pair rows $ij$ have
weight $w_{ij}>0$. All rows are labeled. The coefficient of $q^k$ is
the sum of the products of the row weights.

**Theorem.** Fix the numbers of singleton rows of each of the four
colors. Whenever the prescribed singleton counts are attainable, all nonzero
zeros of the corresponding polynomial are simple and negative. The reduced polynomials obtained by
removing the forced power of $q$ strictly interlace at consecutive
numbers of rows, with the longer row supplying the rightmost zero.
The same statements hold when there are exactly **two singleton rows**
and their colors are unrestricted. The edge and singleton weights may
be chosen independently in both statements.

### Three independent edge counts

Write $a_i$ for the prescribed singleton counts. Their sum must be even,
say $2s$, because the total number of ones is $4k$. Use the three pairs
of opposite edges $12|34$, $13|24$, $14|23$. For $ab|cd$ put
$\delta_{ab}=s-a_a-a_b$ and $g_{ab}=w_{ab}w_{cd}$. Comparing the incidences
at $a,b$ with those at $c,d$ shows that the difference between the
two edge multiplicities is $\delta_{ab}$. Consequently they are
$$
  t_{ab}+\max(\delta_{ab},0),\qquad
  t_{ab}+\max(-\delta_{ab},0),\qquad t_{ab}\ge0 .
$$
Conversely these three differences make the four column totals equal.
Their common minimum is $k_0=(s+\sum|\delta_{ab}|)/2$.
It is an integer, since modulo two the sum of the three differences is
$s-2a_1$. Increasing any $t_{ab}$ by one raises every column sum by one.
At baseline there are $L=s+2k_0$ nonempty rows. For $n<L$ the slice
is empty. For $n\ge L$ put $N=n-L$ and
$$
 C(q)=\prod_{ab|cd}\left(\sum_{j\ge0}
       \frac{(g_{ab}q)^j}{j!(j+|\delta_{ab}|)!}\right)
     =\sum_{j\ge0}c_j q^j .
$$
After dividing by $q^{k_0}$ and a positive scalar, the row polynomial is
$$
 S_N(q)=\sum_{2j\le N}(N)_{\underline{2j}} c_jq^j.                 \tag{1}
$$
Indeed the multinomial count of row types is the falling factorial of
the number of used rows divided by each row type's factorial. The
falling factorial splits as $(n)_{\underline L}(N)_{\underline{2j}}$.
The discarded scalar is $(n)_{\underline L}\prod_i v_i^{a_i}/a_i!$
times $\prod_{ab|cd}w_{ab}^{\max(\delta_{ab},0)}w_{cd}^{\max(-\delta_{ab},0)}$.

### Why the consecutive rows interlace

Put $\Phi(z)=C(-z^2)$. Each factor, of order $h=|\delta_{ab}|$,
is $J_h(2\sqrt g\,z)/(\sqrt g\, z)^h$, interpreted continuously at
zero. Its convergent product has infinitely many real nonzero roots.
It is the locally uniform limit of real-rooted polynomials obtained by
truncating that product. [Bessel series](https://dlmf.nist.gov/10.2.E2) · [Bessel product](https://dlmf.nist.gov/10.21.E15)

With $D=d/dx$, define
$$
 Q_N(x)=\Phi(D)x^N=x^N S_N(-x^{-2}).
$$
All resulting polynomials are real-rooted. To see simplicity, reserve
$N-1$ nonzero real linear factors from the product for $N\ge2$. Apply
the remaining product to $x^N$, using coefficientwise convergence of
the resulting degree-$N$ polynomials. Their leading coefficient is a
fixed nonzero number. The operation $p\mapsto p-bp'$ for a real
$b\ne0$ preserves real-rootedness. Each old zero of multiplicity $m$
retains multiplicity $m-1$, and the new zeros are simple. Indeed
$p'/p$ is strictly decreasing between its poles, takes every real
value in each interior gap, and takes $1/b$ once in an exterior
interval. Applying the reserved factors therefore leaves only simple
zeros. This also proves the preservation used on the finite products.

Since $Q_{N+1}'=(N+1)Q_N$, Rolle’s theorem gives strict interlacing.
The even and odd symmetries put the zero at the origin only in odd
degree. Map the positive roots by the increasing map $x\mapsto -x^{-2}$.
These give every zero of $S_N$. The larger positive root of $Q_{N+1}$
supplies the rightmost zero of $S_{N+1}$ whenever both rows are
nonconstant. Constant cases are vacuous.

### Two singleton rows with unrestricted colors

For each opposite pair $j=ab|cd$ put
$$
 F_j(q)=\sum_{r\ge0}\frac{(g_jq)^r}{(r!)^2},\qquad
 G_j(q)=\sum_{r\ge0}\frac{(g_jq)^r}{r!(r+1)!},\qquad
 A_j=v_av_b w_{cd}+v_cv_d w_{ab}.
$$
Let $B=\tfrac12\sum_i v_i^2\prod_{a<b,\ i\notin\{a,b\}}w_{ab}$.
Two singletons in distinct columns $a,b$ force the opposite edge
$cd$ at the minimum quota one. Two in column $i$ force the triangle
on the other three columns at minimum quota two and have a factorial
denominator $2!$. Thus the entire coefficient series, before
assigning row labels and after removing one factor of $q$, is
$$
 U(q)=\sum_{j=1}^3 A_jG_j(q)\prod_{l\ne j}F_l(q)
        +qB\prod_{j=1}^3G_j(q).                                   \tag{2}
$$
Every array at quota $k$ has $2k+1$ occupied rows. For $n\ge3$ its
polynomial, after dividing by $(n)_{\underline3}q$, is (1) with
$N=n-3$ and $c_j=[q^j]U$.

For $`\mathrm{Im}\,z>0`$ set
$M_j=J_0(2\sqrt{g_j}\,z)/J_1(2\sqrt{g_j}\,z)$.
These numbers have strictly negative imaginary parts. In fact
$J_1/J_0=-J_0'/J_0$ has positive imaginary part by summing the
logarithmic derivatives of the paired real factors of $J_0$.
In particular neither Bessel denominator vanishes there.
[Derivative identity](https://dlmf.nist.gov/10.6.E3) · [Bessel product](https://dlmf.nist.gov/10.21.E15)

At $q=-z^2$, the ratio $F_j/G_j$ is $\sqrt{g_j}\,zM_j$. A zero in
(2) would therefore satisfy
$$
  c_{12}M_1M_2+c_{13}M_1M_3+c_{23}M_2M_3=B,
$$
where each $c_{lm}=A_j\sqrt{g_lg_m}>0$ and $j$ is the omitted index.
Solving for $M_3$ gives
$$
 M_3=\frac{B}{c_{13}M_1+c_{23}M_2}
     -\frac{c_{12}}{c_{13}/M_2+c_{23}/M_1}.
$$
Both summands have positive imaginary part, a contradiction. Conjugation
excludes zeros in the other open half-plane. Hence $U(q)$ has only
negative real zeros. It has positive constant term and positive coefficients
at every degree. The series for $F_j,G_j$ give growth at most
$O((1+|q|)\exp(K\sqrt{|q|}))$ for a constant $K$. Hadamard
factorization at order at most $1/2$ now gives a convergent genus-zero
product with infinitely many zeros. Applying the reserved-factor and
derivative argument above to $U(-z^2)$ proves the second assertion.
[Hadamard factorization](https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr01.pdf)

**Scope.** The original polynomial sums over every possible number of
singleton rows. The theorem handles every individual color profile and
one nontrivial sum of profiles for arbitrary positive weights. The five-row
weighted triangle obstruction shows that unrestricted summation over
profiles can introduce nonreal roots. Determining the effect of the
equal singleton and pair weights in the original problem remains the
main question. [Weighted obstruction](triangle-weight-gap.md) · [Original problem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**⬜ None.** This result has a written proof. The Bessel product and
constant-coefficient differential operators are classical. We make no
priority claim for those ingredients or for the general Jensen-polynomial
principle.
