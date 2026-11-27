# An explicit threshold that allows the degree to grow

Let $`O_{n,j}(t)`$ enumerate ordered partitions of $`[n]`$ by the number of blocks of cardinality at least $`j`$. Set $`d=\lfloor n/j\rfloor`$. For $`d\ge2`$ put

$$
J_d=(64(d+2))^{32768(d+2)^7}.
$$

**Theorem.** If $`j\ge J_d`$, the two original rows at sizes $`n`$ and $`n+1`$ have simple negative zeros and strictly interlace. In order of increasing modulus, the new row supplies the first zero. It also supplies the last zero when the degree increases. In particular the threshold is effective for unbounded old degree, with $`\log J_d=O(d^7\log(d+2))`$. For any specified maximum degree one can now bound the residual sizes and thresholds before inspecting any rows. This bound is extremely large. Smaller certified cutoffs are available in low degrees. The full all-size conjecture remains open. [Original claim](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Uniform eventual theorem](../uniform-eventual/README.md) · [Practical low-degree cutoffs](../bounded-degree/README.md)

## Approximate both consecutive rows

Write $`h=1/j`$, $`c=n/j=d+s`$, $`0\le s<1`$, and $`\lambda=\log 2`$. Use the common affine coordinate from the low-degree proof. For clarity, put $`u_b=j!\lambda^b/(j+b)!`$, $`U=\sum_{b\ge0}u_b`$, $`V(z)=U^{-1}\sum u_bz^b`$, and $`H_0(z)=2\lambda/(2-e^{\lambda z})`$. In the coordinate $`x=(1-t)jU\lambda^j/(2\lambda j!)`$, the positive multiple $`2\lambda^{n+1}O_{n,j}(t)/n!`$ equals $`P_n(x)=\sum_k(-1)^k A_k(n)x^k`$, where

$$
A_k(n)=h^k[z^{n-kj}]V(z)^k H_0(z)^{k+1},\qquad B_k=j(A_k(n+1)-A_k(n)).
$$

This follows from the ordered sequence of labeled blocks, whose generating function is $`(2-e^z-(t-1)\sum_{b\ge j}z^b/b!)^{-1}`$. For $`0\le k\le d`$ set $`f_0=1`$, $`f_k=(c-k)^k/k!`$ for $`k\ge1`$, and $`g_k=\partial_s f_k`$. Put $`f_{d+1}=g_{d+1}=0`$. The following bounds hold uniformly in the strip, including a transition to degree $`d+1`$:

$$
 |A_k-f_k|\le C_d h,\qquad |B_k-g_k|\le C_d h,\qquad
 C_d=(d+2)^2(2^{d+1}8^{d+2}+2)(2d+4)^{d+1}.
$$

Here $`A_k=A_k(n)`$. To prove the estimates put $`W=V^k((1-z)H_0)^{k+1}`$, so $`W(1)=1`$. On $`|z|=2`$, the geometric bound $`u_b\le(\lambda/(j+1))^b`$ and $`\lambda<3/4`$ give $`|V|\le2`$. For $`a+ib=\lambda(z-1)`$ we have $`e^a\ge1/8`$ and $`|b|<\pi`$. The identity $`|1-e^{a+ib}|^2=(1-e^a)^2+2e^a(1-\cos b)`$, the mean value theorem and $`1-\cos b\ge2b^2/\pi^2`$ give $`|1-e^{a+ib}|\ge|a+ib|/8`$. Thus $`|(1-z)H_0|\le8`$. The functions are analytic through the closed disk after removal of the pole at $`1`$, since the other poles of $`H_0`$ are $`1+2\pi i\ell/\lambda`$ with nonzero integer $`\ell`$. The coefficients of $`E=(W-1)/(1-z)`$ have modulus at most $`M_k2^{-i}`$ in degree $`i`$, with $`M_k=2^k8^{k+1}+1`$.

For $`k\ge1`$, $`m=n-kj\ge0`$, expand

$$
 V^kH_0^{k+1}=(1-z)^{-k-1}+E(1-z)^{-k}.
$$

The error over the main coefficient $`\binom{m+k}{k}`$ is at most $`2M_k\binom{m+k-1}{k-1}`$. For $`k\ge2`$ the forward difference has main coefficient $`\binom{m+k}{k-1}`$ and error at most $`2M_k\binom{m+k-1}{k-2}`$ by multiplying by $`1-z`$ and taking index $`m+1`$. Multiplying the first estimate by $`h^k`$ and the second by $`h^{k-1}`$ gives the desired bounds. Indeed each scaled binomial product has factors $`mh+ih`$ with $`1\le i\le k`$ and all factors at most $`2d+4`$. Replacing the factors by $`mh`$ costs at most $`k(k+1)h(2d+4)^{k-1}`$ in the first product, with the same bound for the shorter product. The two scaled errors cost at most $`2M_k h(2d+4)^{k-1}`$ each. At $`k=1`$ the forward error instead is $`[z^{m+1}]E`$ and $`m\ge j`$. At $`k=0`$ the two errors are bounded by $`M_0 2^{-n}`$ and $`2M_0j2^{-n}`$, using $`n\ge2j`$. Finally $`B_{d+1}`$ is zero except at a degree increase, where $`0\le B_{d+1}\le (2\lambda)^{d+2}h^d`$. The old coefficient $`A_{d+1}`$ is zero.

We also use the following all-degree upper-end inequality from the earlier proof:

$$
 B_d\ge \frac{A_d}{4(s+h)}.
$$

Indeed $`[z^m]H_0^2`$ increases by at least its current value divided by $`4(m+1)`$. Convolution with the nonnegative coefficients of $`V^dH_0^{d-1}`$ preserves the inequality and $`m=n-dj=sj`$. The auxiliary inequality and its small scalar checks have a separate exact derivation. [Coefficient increment lemma](../bounded-degree/proof.md)

## Effective margins for the limiting roots

Use the projective coordinate $`y=x/(1+x)`$ and integer polynomials

$$
 F(s,y)=d!\sum_{k=0}^d(-1)^k f_k y^k(1-y)^{d-k},\qquad
 G(s,y)=(1-y)\partial_sF(s,y).
$$

The limit polynomial is the partition function of unit hard rods evaluated at a negative activity. The finite-volume root theorem proves that its roots are simple and that every finite positive $`x`$-root decreases strictly with increasing $`s`$, with nonzero derivative. This includes the finite roots at the integer endpoints. At $`s=0`$ the extra projective root $`y=1`$ is also simple, since $`f_d=0`$ and $`f_{d-1}=1/(d-1)!`$. At $`s=1`$ all $`d`$ roots have finite $`x`$. The resulting $`d`$ roots $`y_1<\cdots<y_d`$ lie in $`(0,1]`$ on the closed interval. The polynomial leading coefficient in $`y`$ has absolute value $`d!\sum f_k\ge1`$. At an ordinary root $`G(s,y_i)`$ has sign $`(-1)^i`$: use $`F_s=-F_y y_i'`$ and the sign of $`F`$ at zero. [Finite-volume simplicity and strict root motion](../proportional-window.md)

Let $`H=(64(d+2))^{16(d+2)}`$, $`D=4(d+1)^2`$, $`T=H^{8(d+1)}`$ and $`\gamma=T^{-8D}`$. Use the sum of the absolute integer coefficients as the norm of a polynomial in any number of variables. It is submultiplicative. The norms of $`F,G,F_y,F_s,G_y,G_s`$ are bounded by $`H`$. Indeed the norm of $`F`$ is at most $`d!(d+1)(d+1)^d2^d`$, and the derivatives and the factor $`1-y`$ cost at most $`4(d+2)^2`$. Also $`d!(d+2)C_d\le H`$. For this last bound, use $`d!\le(d+2)^d`$, $`2^{d+1}8^{d+2}+2\le32^{d+2}`$ and $`2d+4=2(d+2)`$. The two actual projective polynomials formed from $`A`$ in order $`d`$ and $`B`$ in order $`d+1`$, both multiplied by $`d!`$, therefore differ from $`F`$ and $`G`$ by at most $`H/j`$ on the unit square. Each term $`y^k(1-y)^{e-k}`$ has absolute value at most one there.

The two integer resultants $`R_1=\mathrm{Res}_y(F,F_y)`$ and $`R_2=\mathrm{Res}_y(F,G)`$ have degree at most $`D`$ in $`s`$ and norm at most $`T`$. This follows by expanding each Sylvester determinant of order at most $`2d+1`$, bounding the norm by $`(2d+1)!H^{2d+1}`$. The first resultant never vanishes for $`s\in[0,1]`$. The second never vanishes on $`(0,1]`$. In fact all the roots of $`F`$ there are finite ordinary roots where $`G`$ has strict sign. Put $`m=\mathrm{ord}_0 R_2\le D`$. Then $`R_2/s^m`$ is an integer polynomial with no zeros on $`[0,1]`$.

Any integer polynomial $`P`$ of degree at most $`D`$ and norm at most $`T`$ which never vanishes on $`[0,1]`$ has $`|P|\ge\gamma`$ there. At an endpoint its absolute value is at least one. A nonzero interior critical value is a zero of the nonzero integer polynomial $`\mathrm{Res}_s(P',P-z)`$ in $`z`$. For nonconstant $`P`$ this resultant is nonzero because for generic $`z`$ no zero of $`P'`$ is a zero of $`P-z`$. A nonzero constant $`P`$ already satisfies the bound. The determinant bounds the resultant norm by $`(2D)!(2DT)^{2D}\le T^{6D}`$. Divide out any power of $`z`$. The constant coefficient that remains is a nonzero integer. The reciprocal Cauchy root bound now gives modulus at least $`1/(1+T^{6D})\ge\gamma`$ at every nonzero root. Consequently

$$
 |R_1(s)|\ge\gamma,\qquad |R_2(s)|\ge\gamma s^D\quad(0\le s\le1).
$$

Define the rational margins

$$
 \eta=\gamma H^{-2d-2},\quad L=2H\eta^{-d},\quad b=H^{-2d-2},\quad
 \sigma=\frac{b}{1024 H^5L},\quad \beta=\gamma\sigma^D b,\quad
 \tau=\frac{\beta\eta}{16H^4}.
$$

Every pair of roots of $`F`$ is separated by at least $`\eta`$. Use the product for $`|R_1|`$ as the $`(2d-1)`$st power of the absolute leading coefficient times the squared pairwise differences. Each difference is at most one and the leading coefficient is at most $`H`$. In particular $`|F_y|\ge\eta^{d-1}`$ at every root. The implicit function theorem, including one-sided derivatives at the endpoints, bounds each $`|y_i'|`$ by $`L`$.

For $`s\ge\sigma`$ the product for $`|R_2|`$ gives $`|G(s,y_i)|\ge\beta`$ at every root. All other evaluations and the leading coefficient are bounded by $`H`$ and the degree of $`G`$ in $`y`$ is at most $`d+1`$. At $`s=0`$ the integer polynomial $`F(0,y)/(1-y)`$ and $`G(0,y)`$ have no common zero. Their nonzero integer resultant gives $`|G(0,y_i)|\ge b`$ for every $`i<d`$ by the same product estimate, since dividing by $`1-y`$ preserves the absolute leading coefficient. Along each root, $`G(s,y_i(s))`$ changes at speed at most $`H(1+L)`$. Therefore for $`0\le s\le\sigma`$ all roots except the last satisfy $`|G(s,y_i)|\ge b/2\ge\beta`$. The last satisfies $`1-y_d(s)\le L\sigma`$.

## Transfer to the original rows

It suffices to take $`j\ge J^*=8H(2/\eta)^d/\tau`$. The old actual polynomial has one simple root $`v_i`$ within $`\tau`$ of each $`y_i`$. To see this, use the disjoint intervals with endpoints $`y_i\pm\tau`$, clipped to $`[0,1]`$. At each unclipped endpoint the product formula gives $`|F|\ge\tau(\eta/2)^{d-1}>H/j`$. At a clipped endpoint the signs of the actual polynomial are positive at zero and $`(-1)^d`$ at one, since $`A_0,A_d>0`$. Clipping can concern only the first or last root by the separation. Opposite endpoint signs give $`d`$ distinct roots and exhaust the old degree. All lie in $`(0,1)`$.

Where $`|G(s,y_i)|\ge\beta`$, the true projective difference at $`v_i`$ has sign $`(-1)^i`$ because $`H\tau+H/j<\beta`$. The only remaining case has $`s\le\sigma`$ and $`i=d`$. There is then no degree increase, since a carry would require $`s=1-h\ge1/2`$. Here $`w=(1-v_d)/v_d\le2(L\sigma+\tau)\le1/(16H^3)`$. Every $`A_k`$ and $`|B_k|`$ is at most $`H`$ by the coefficient bounds, and $`A_{d-1}\ge1/(d-1)!-C_d/j\ge1/(2H)`$. The reversed old root equation yields

$$
 A_d\ge wH_1,\qquad
 H_1=A_{d-1}-\sum_{k<d-1} A_k w^{d-1-k}
      \ge\frac1{2H}-dHw>\frac1{4H}.
$$

The terms of lower degree than $`d`$ in the reversed difference have total modulus bounded by $`wdH`$. Since $`h\le\sigma`$ and $`4(s+h)dH\le8\sigma dH<1/(4H)`$, the inequality $`B_d\ge A_d/(4(s+h))`$ gives $`B_d>wdH`$. The actual difference therefore also has sign $`(-1)^d`$ at the last old root.

The new polynomial has positive value at zero in the $`x`$ coordinate and sign $`(-1)^i`$ at each old root. The intermediate value theorem supplies a new root before the first old root and between every two consecutive old roots. If the degree increases, its leading sign supplies another new root beyond the last old root. These account for its entire degree. Positive coefficients and positive constant term in the original mark exclude nonnegative real roots, so every root just obtained corresponds to a strictly negative original zero. The common affine coordinate increases with its modulus.

## Simplifying the cutoff

Put $`M=d+2`$, $`B=2d+2`$, $`P=64(d+1)D`$, $`K=P+B`$, $`S=B+6+dK`$, and $`U=P+DS+B`$. Substituting the margins gives exactly

$$
 J^*=2^{7+d+11D} H^{5+U+(d+1)K}.
$$

For $`M\ge4`$, $`D\le4M^2`$, $`P\le256M^3`$, $`K\le258M^3`$, $`S\le261M^4`$, and $`U\le1052M^6`$. Thus $`5+U+(d+1)K\le1320M^6`$ and $`7+d+11D\le50M^2`$. Substituting $`H=(64M)^{16M}`$ proves $`J^*\le(64M)^{32768M^7}`$ as claimed. These sizes are only effective upper bounds. They do not give a practical exhaustive search through the exceptional set.
