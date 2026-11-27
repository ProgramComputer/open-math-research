# Uniform certificates for cubic and quartic ordered-partition rows

Let $`O_{n,j}(t)`$ count ordered partitions of $`[n]`$ by the number of blocks of size at least $`j`$, for $`j\ge2`$. The partial theorem gives strict directed interlacing for every pair $`(n,n+1)`$ with $`3j\le n<5j`$. All roots of both polynomials are simple and negative. In increasing modulus the new row starts, then the two lists alternate, with a final new root when the degree increases. The earlier result for linear and quadratic old rows covers $`n<3j`$, including the transition into the first cubic row. [Alexandersson's conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Earlier reviewed theorem](https://github.com/ProgramComputer/open-math-research/pull/242)

The certificate treats the whole interval of scaled sizes at once. In degree three it applies for $`j\ge64`$, and in degree four for $`j\ge128`$. The remaining pairs use exact integer coefficient rows and symmetric matrices of order three or four.

## Normalization

Fix old degree $`d\in\{3,4\}`$. Write $`c=n/j`$, $`h=1/j`$, and $`\lambda=\log 2`$. Let $`G(z)=(2-e^z)^{-1}`$ and $`B(z)=\sum_{r\ge j}z^r/r!`$. Expanding about mark one gives

$$
O_{n,j}(t)/n!=\sum_{k\ge0}(t-1)^k[z^n]B(z)^kG(z)^{k+1}.
$$

Indeed the ordinary sequence of ordered blocks has exponential generating function $`1/(2-e^z-(t-1)B(z))`$. Define

$$
H(z)=2\lambda G(\lambda z),\qquad u_b=\frac{j!\lambda^b}{(j+b)!},\qquad
U=\sum_{b\ge0}u_b,\qquad V(z)=U^{-1}\sum_{b\ge0}u_bz^b.
$$

At the common coordinate $`x=(1-t)jU\lambda^j/(2\lambda j!)`$, multiplication of the row by $`2\lambda^{n+1}/n!`$ gives $`P_n(x)=\sum_k(-1)^k A_k x^k`$, where

$$
 A_k=h^k[z^s]V^kH^{k+1},\qquad s=n-kj .
$$

Coefficients at negative indices are zero. This coordinate and the positive factor $`2\lambda^{n+1}/n!`$ apply at every size independently. Write $`B_k=j(A_k(n+1)-A_k(n))`$ for the signed-difference polynomial's coefficients before alternating signs; $`B_k`$ here is a scalar. Only the change in the coefficient index distinguishes the two sizes.

## Analytic bounds behind the interval calculation

Write $`L_{p,r}=[w^r](w/(1-e^{-w}))^p`$, and put

$$
 T_p(s)=\sum_{r=0}^{p-1} L_{p,r}\lambda^r\binom{s+p-1-r}{p-1-r}.
$$

The binomial on the right is its polynomial extension, including negative integer top arguments. For every integer $`s`$ and $`1\le p\le5`$,

$$
 \left|[z^s]H(z)^p-T_p(s)\right|\le2^{-s}.
$$

For $`s\ge0`$ this subtracts the principal part at $`z=1`$, since $`(1-z)H(z)=w/(1-e^{-w})`$ with $`w=\lambda(1-z)`$. Its other poles have modulus greater than four. On $`|z|=4`$ put $`a+ib=\lambda(z-1)`$. We have $`e^a\ge1/32`$, $`|b|<\pi`$ and $`|a+ib|\ge3\lambda`$. From $`|1-e^{a+ib}|^2=(1-e^a)^2+2e^a(1-\cos b)`$ and $`1-\cos b\ge2b^2/\pi^2`$, one gets $`|1-e^{a+ib}|\ge|a+ib|/32`$. Thus $`|H|\le32/3<11`$. The principal part on this circle is bounded by $`\sum_r |L_{p,r}|\lambda^r`$, since $`|1-z|\ge3`$. Cauchy's bound on the analytic remainder is consequently at most $`2^{32}4^{-s}`$, sufficient for $`s\ge32`$.

For $`s=-b`$ with $`b\ge32`$, each binomial has absolute value at most $`b^{p-1-r}/(p-1-r)!`$. The sum of these bounds with its factors is below $`2^{32}`$ at $`b=32`$ and grows by a factor at most $`(33/32)^{p-1}<2`$ per step. For $`-32\le s\le32`$ the program bounds all quantities by exact rationals. It computes the unrestricted coefficients from the defining series of $`G`$ and obtains a rational interval of width $`10^{-30}`$ for $`\lambda`$ from the positive series for $`2\,\mathrm{arctanh}(1/3)`$. All $`L_{p,r}`$ used in the proof are positive as the finite series check verifies.

The normalized sequence $`H_2(s)=[z^s]H^2`$ also satisfies

$$
 H_2(s+1)-H_2(s)\ge \frac{H_2(s)}{4(s+1)},\qquad s\ge0 .
$$

For $`s\ge10`$ this follows from $`T_2(s)=s+1+\lambda`$ and the preceding error bound. For smaller $`s`$ the checker uses the exact coefficients of $`G^2`$ and a rational lower bound for $`\lambda`$. Convolving with any nonnegative sequence preserves this difference bound: at a contributing index $`s-i`$ its denominator is at most $`s+1`$, and the term newly entering at $`i=s+1`$ is nonnegative. In particular for $`k\ge1`$ the coefficient sequence $`V^kH^{k+1}`$ satisfies it. For the top index this gives $`B_d\ge A_d/(4(c-d+h))`$.

To bound $`[z^s]V^kH^{k+1}`$, let $`Y`$ have generating function $`V^k`$. For the claimed cutoff $`J`$, put $`q=\lambda_{\mathrm{upper}}/(J+1)`$. The single-excess weights are bounded by $`q^b`$, since $`U\ge1`$. Consequently

$$
 \mathbb E [2^Y]\le(1-2q)^{-k},\qquad
 0\le \mathbb E\binom Y\ell\le
 \binom{k+\ell-1}{\ell}q^\ell(1-q)^{-k-\ell}\qquad (\ell\ge1).
$$

The pointwise error in replacing the coefficient by $`\mathbb E[T_{k+1}(s-Y)]`$ is at most $`2^{-s}\mathbb E[2^Y]`$, including the terms with $`Y>s`$. Its forward difference has error at most $`3\,2^{-s}\mathbb E[2^Y]/2`$. For $`0\le r\le k`$ define

$$
 E_r=\sum_{\ell=0}^r L_{k+1,r-\ell}\lambda^{r-\ell}(-1)^\ell\mathbb E\binom Y\ell .
$$

Vandermonde's identity with a negative shift in the coefficient index, or the Taylor polynomial of $`z^Y`$ in $`1-z`$, gives $`\mathbb E[T_{k+1}(s-Y)]=\sum_r E_r\binom{s+k-r}{k-r}`$. For clarity, for an integer $`Y`$ the identity for each binomial follows by comparing degree-$`m`$ coefficients in $`(1+w)^{s+m}(1-w/(1+w))^Y=(1+w)^{s+m-Y}`$. The same identity applies when $`s-Y<0`$.

After multiplication by $`h^k`$, the term indexed by $`r`$ is

$$
 E_r h^r \frac{\prod_{i=1}^{k-r}(c-k+ih)}{(k-r)!}.
$$

For the normalized forward difference it is $`E_r h^r\prod_{i=2}^{k-r}(c-k+ih)/(k-r-1)!`$, with $`r<k`$. The checker bounds $`E_r`$ using the factorial-moment inequalities and the rational bounds for $`\lambda`$. It verifies that these coefficient bounds are nonnegative, so products can be bounded at the rectangle endpoints. The errors above are multiplied by $`h^k`$ and $`h^{k-1}`$ respectively. At $`k=0`$ the forward difference is bounded separately by $`2J\,2^{-dJ}`$, with the exponent allowed to be clipped to 80. This follows from the error at $`s=n`$ and the decrease of $`j2^{-dj}`$. At the possible degree increase the additional $`B_{d+1}`$ belongs to $`[0,(2\lambda)^{d+2}h^d]`$, since its only new term has $`s=0`$ and $`V(0)\le1`$. Away from $`c= d+1-h`$ it is zero. The table allows this upper bound across any rectangle that could meet the degree increase.

## Rational root brackets and the unbounded root

For a coefficient vector $`C`$ of order $`D`$, evaluate the projective polynomial $`\sum_{k=0}^D(-1)^k C_k v^k(1-v)^{D-k}`$ with $`v=x/(1+x)`$. Use order $`d`$ for the old row and $`d+1`$ for the normalized difference, padding with zeros. Their signs for $`0\le v<1`$ give the signs before this positive change of scale.

The certificate is a partition of $`[d,d+1]\times[0,1/J]`$ into closed rational rectangles with disjoint interiors. For an ordinary bracket $`[a,b]`$ at root index $`i\in\{1,\dots,d\}`$, the checker verifies old endpoint signs $`(-1)^{i-1}`$ and $`(-1)^i`$ and a strict difference sign $`(-1)^i`$ throughout the bracket. Its bounds use interval evaluation term by term, respecting the sign of each coefficient. The $`d`$ brackets are pairwise disjoint and ordered.

A final bracket may end at $`v=1`$ on a rectangle that cannot contain a degree increase. At that endpoint the old polynomial has sign $`(-1)^d`$ because $`A_d>0`$. At its root let $`w=(1-v)/v`$ and $`w_0=(1-a)/a`$. The reversed old equation gives $`A_d\ge w H_0`$ with

$$
 H_0=A_{d-1}^{\mathrm{lower}}-\sum_{k<d-1} A_k^{\mathrm{upper}}w_0^{d-1-k}.
$$

All lower-index terms of the reversed difference polynomial have total modulus at most $`wK`$, where $`K=\sum_{k<d}|B_k|^{\mathrm{upper}}w_0^{d-1-k}`$. The checker verifies $`H_0>4(c_{\mathrm{upper}}-d+h_{\mathrm{upper}})K`$. The preceding top-coefficient growth bound forces $`B_d>wK`$, which supplies sign $`(-1)^d`$ at that root.

There are exactly $`d`$ distinct positive old $`x`$-roots by the degree and the endpoint signs. At those roots the later row has signs $`(-1)^i`$. Its value at zero in the $`x`$-coordinate is positive. The intermediate value theorem supplies the new roots successively before and between the old ones, with the remaining root after the last one when the later degree is $`d+1`$. These brackets exhaust the degree. Every real root in the original coordinate is strictly negative by the positive constant and nonnegative coefficients. The common affine coordinate $`x`$ increases with the modulus of each negative original root, giving the claimed orientation.

## Exact finite range

For each remaining pair choose the first block of any labeled partition. A first block of size $`s`$ contributes $`\binom ns t^{[s\ge j]}O_{n-s,j}`$. The verifier computes the exact polynomials by this recurrence with $`O_{0,j}=1`$. For old row $`P`$ and new row $`Q`$, replace $`Q`$ by its remainder $`R`$ modulo $`P`$, up to a positive scalar. Form the negative of the symmetric Bézout matrix with kernel

$$
 \frac{P(x)R(y)-P(y)R(x)}{x-y}.
$$

The checker uses integer fraction-free elimination to certify that all leading principal minors of this negative matrix are positive. If a nonreal $`z`$ were a zero of $`P`$, the corresponding Hermitian quadratic form at $`(1,z,\ldots,z^{d-1})`$ would vanish by evaluating at $`(\bar z,z)`$. A repeated real root would likewise give zero by taking $`x=y=z`$. At every simple real root $`\rho`$ the value is $`-P'(\rho)R(\rho)>0`$. Thus $`Q/P`$ has strictly negative residues there. With the positive leading and constant coefficients this gives a new root nearer zero than the nearest old root, one in every intervening gap, and a final root at the far end when the degree increases.

The cubic finite check covers 1,953 equal-degree pairs and 62 degree increases. The quartic finite check covers 8,001 equal-degree pairs and 126 increases at thresholds $`2\le j<128`$. The ledger option emits every complete pair of coefficient vectors in the order used by its recorded SHA-256.
