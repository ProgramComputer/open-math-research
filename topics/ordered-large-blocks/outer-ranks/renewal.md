# Outer roots when the threshold grows faster than the degree

Write $`n=mj+s`$, $`0\le s<j`$. For any fixed number of exterior ranks, along every sequence $`m,j\to\infty`$ with $`j/m\to\infty`$, the largest-modulus roots of $`O_{n,j}`$ are simple and negative and alternate strictly with those of $`O_{n+1,j}`$ in the direction appropriate to the change of degree. The statement concerns the roots ordered among all complex zeros.

Let $`a_r,b_r`$ be the old and new moduli in descending order, indexed from one. If the degree stays fixed, $`a_r>b_r>a_{r+1}`$. At a degree carry, $`b_r>a_r>b_{r+1}`$. For any prescribed finite range of $`r`$ the proof includes the adjacent comparator ranks.

## Positive coefficient estimates

Let $`S_j(x)=\sum_{a=1}^{j-1}x^a/a!`$ and choose the positive $`\rho_j`$ with $`S_j(\rho_j)=1`$. Define

$$
T(z)=\frac1{1-S_j(\rho_j z)},\qquad U(z)=\sum_{a\ge0}\frac{j!(\rho_j z)^a}{(j+a)!},
\qquad C_p(e)=[z^e]T(z)^{p+1}U(z)^p .
$$

Here and below all implicit constants in the coefficient estimates are absolute for sufficiently large $`j`$. The normalized old reversed coefficients are

$$
d_h=(j!)^{-(m-h)}\rho_j^{-(s+hj)} C_{m-h}(s+hj),\qquad 0\le h\le m.
$$

They are the coefficients of $`t^m O_{n,j}(1/t)/n!`$ by the ordered sequence decomposition into small blocks and single large blocks. In particular a root $`-y`$ of the reversed polynomial corresponds to the root $`-1/y`$ of the original.

The function $`A(z)=(1-z)T(z)`$ is analytic and nonzero on a fixed disk $`|z|\le R>1`$, and so is $`U`$. Their derivatives and inverses are bounded there uniformly in $`j`$, after reducing $`R`$ slightly. Indeed $`\rho_j\to\rho=\log2`$, the divided differences $`(1-S_j(\rho_j z))/(1-z)`$ converge locally uniformly to $`(2-e^{\rho z})/(1-z)`$, whose only possible zeros on $`|z|\le2`$ are removable at $`1`$, and $`U\to1`$ locally uniformly. Put $`a=A(1)`$, $`b=aU(1)`$, both bounded above and below away from zero. The coefficient sequences of $`T/a`$ and $`TU/b`$ equal $`1+O(R^{-e})`$ at index $`e`$, by subtraction of their simple poles. Every entry is positive and uniformly bounded below, by convergence at the finitely many small indices.

For $`p\ge0`$ and $`e\ge0`$ one has

$$
\log \frac{C_p(e)}{a b^p\binom{e+p}{p}}
   =O\left(1+\frac{p^2}{e+p+1}\right).
\tag{1}
$$

Divide by $`a b^p`$ and average the product of the $`p+1`$ coefficient factors over all weak compositions of $`e`$ into $`p+1`$ parts. For any specified $`h\le p`$ parts $`v_i`$, the mass of a specified vector is at most $`\binom{e+p-h}{p-h}/\binom{e+p}{p}\le(p/(p+e))^h`$. Hence the expectation of $`R^{-\sum v_i}`$ on these parts is at most $`(p/((1-R^{-1})(e+p)))^h`$. For $`h=p+1`$ the product equals $`R^{-e}`$. Expanding an upper majorant $`\prod (1+C R^{-v_i})`$ proves (1) when $`e`$ exceeds a sufficiently large constant times $`p+1`$, including the last term $`C^{p+1}R^{-e}`$. At smaller $`e`$ the bounded factors give $`O(p+1)`$, sufficient in that range. For the lower bound, each logarithm is at least $`-C R^{-v_i}`$, and Jensen's inequality gives (1). The case $`p=0`$ follows directly from $`[z^e]T/a=1+O(R^{-e})`$.

For all sufficiently large $`j`$, every coefficient of $`(1-z)T^2`$ is positive. After subtracting $`a^2/(1-z)`$ the remainder is uniformly bounded in a disk of radius greater than one. Thus all sufficiently high coefficients are uniformly positive. For the finite set of low indices use convergence to $`(1-z)/(2-e^{\rho z})^2`$, whose strictly positive coefficients are proved in the [bounded proportional window](../proportional-window.md). Put $`q=\lfloor(p+1)/2\rfloor`$. For $`p\ge1`$, $`(1-z)^qT^{p+1}U^p`$ has nonnegative coefficients. It follows by convolution with $`(1-z)^{-q}`$ that $`C_p`$ is nondecreasing and that

$$
\delta_p(e):=C_p(e+1)/C_p(e)-1\ \ge\ (q-1)/(e+1).
\tag{2}
$$

Convolution indeed uses the binomial ratio $`1+(q-1)/(v+1)`$ at indices $`v\le e`$, with one additional nonnegative term. At $`p=0`$ one has $`|\delta_0(e)|=O(R^{-e})`$.

The logarithmic derivative yields sharper uniform bounds. Set $`L=(p+1)A'/A+p U'/U`$, with coefficients $`|L_i|\le C p R^{-i}`$ when $`p\ge1`$. At $`F=T^{p+1}U^p`$ we have $`(1-z)F'=(p+1)F+L(1-z)F`$. Equating coefficients, with $`C_p(-1)=0`$, gives

$$
(e+1)\delta_p(e)=p+
   \frac{\sum_{i=0}^{e}L_i(C_p(e-i)-C_p(e-i-1))}{C_p(e)}.
$$

Monotonicity first gives $`0\le\delta_p(e)\le C p/(e+1)`$. For $`i\le e/2`$, $`e\ge2`$, substitute this upper bound at $`e-i-1`$ in the difference. For the remaining indices sum the geometric tail. We obtain

$$
\delta_p(e)=\frac{p}{e+1}
  \left(1+O\left(\frac{p}{e}+R^{-e/2}\right)\right)\qquad(e\ge2).
\tag{3}
$$

## Pure powers at a balance

Fix any nonnegative integer $`L`$. Write $`u=s/j`$, $`y_L=d_L/d_{L+1}`$, and $`B_t=d_t y_L^{t-L}/d_L`$. We show that the contribution of $`t\ne L,L+1`$ at this balance is exponentially small, uniformly for $`1/2\le |y/y_L|\le2`$. It is enough to pass to any subsequence on which $`u\to u_0\in[0,1]`$.

For $`t\ge1`$, or also $`t=0`$ if $`u_0>0`$, the logarithm of $`d_t`$ equals a function linear in $`t`$ plus

$$
f(t)=(m-t)\log(j(u+t))-\log((m-t)!)+O(1+m^2/j).
$$

The error follows from (1) and the comparison of $`\binom{e+p}{p}`$ with $`e^p/p!`$. It is uniform for all indicated $`0\le t\le m`$, and is $`o(m)`$. For clarity use $`f`$ without the error term below. Its successive increments, for $`t<m`$ and $`u+t>0`$, are

$$
f(t+1)-f(t)=\log(m-t)-\log(j(u+t+1))+(m-t)\log(1+1/(u+t)).
$$

They decrease. At any fixed pair of adjacent increments with $`u+t`$ bounded below, the decrease is bounded below by a positive multiple of $`m`$: the difference of the two logarithms multiplying $`m`$ tends to a strictly positive constant. The extension of the chord from $`L`$ to $`L+1`$ therefore exceeds $`f(t)`$, for all other $`t`$, by at least $`c_Lm`$ times the distance to the nearer of $`L,L+1`$. The logarithmic coefficient errors in this chord comparison are $`o(m)(1+|t-L|)`$. Consequently the sum of $`2^{|t-L|} B_t`$ off the central pair is exponentially small in $`m`$.

If $`u_0=0`$, the exceptional entry $`t=0`$ has the upper bound obtained from (1) by replacing $`u`$ in the comparison for its power by $`C(s+m)/j`$, including the exponential error in $`C^m`$. Relative to the chord based at any fixed $`L\ge1`$, this gives

$$
B_0\le (C_L(s+m)/j)^m.
\tag{4}
$$

To see this explicitly, the terms involving $`j^{m-t}`$ and the linear normalization cancel on extrapolating the chord. For fixed $`L`$, the factorial quotient $`(m-L)!^{L+1}/(m!(m-L-1)!^L)`$ is at most one and the factors $`(u+t)`$ in the two anchor terms supply at most $`C_L^m`$. The coefficient errors are absorbed in that same constant. At $`L=0`$ the slope $`\log(d_1/d_0)`$ therefore exceeds the slope $`\log(d_2/d_1)`$ by $`\omega(m)`$ (apply (4) at $`L=1`$). From $`t=1`$ onward the previous decreasing-increment argument gives a geometric upper bound at the actual first balance as well.

In all cases consecutive fixed balances have $`y_{L+1}/y_L\ge e^{c_Lm}`$ eventually. On $`|y|=y_L/2`$ and $`|y|=2y_L`$ the dominant terms of the reversed polynomial have indices $`L`$ and $`L+1`$, respectively. Rouché's theorem gives exactly those disk counts with multiplicity. The opposite real signs give one simple negative root of modulus $`y_L(1+o(1))`$: the normalized function after dividing by the $`L`$th monomial differs from $`1+y/y_L`$ by an exponentially small amount throughout the indicated annulus. These are the consecutive innermost ranks in the reversed polynomial.

## The signed change in a row

Set $`\gamma_t=1+\delta_{m-t}(s+tj)`$ and $`D(y)=\sum_t d_t y^t`$. Ignoring a common positive factor for the moment, the new coefficients at the same original degree are $`d_t\gamma_t`$. For any fixed $`L`$ with $`u_0+L>0`$, (3) gives

$$
(\gamma_L-\gamma_{L+1})j/m\ \longrightarrow    (u_0+L)^{-1}-(u_0+L+1)^{-1}>0.
$$

For $`u_0=0,L=0`$, (2) gives a difference much larger than $`m/j`$. For every $`t\ge1`$, $`|\gamma_t-1|\le C m/j`$, including $`t=m`$ by the analytic bound for $`p=0`$. This estimate also holds at $`t=0`$ if $`u_0>0`$. At an old root $`-y`$ in the $`L`$th annulus subtract $`\gamma_{L+1}D(-y)=0`$. The surviving central contribution has sign $`(-1)^L`$ and magnitude $`d_L y^L(\gamma_L-\gamma_{L+1})`$. The other terms are $`o((m/j)d_L y^L)`$ by the exponentially small tails. When $`L\ge1,u_0=0`$, use (4) for the exceptional term $`t=0`$, since

$$
(1+j/(s+1))(C_L(s+m)/j)^m\longrightarrow0.
$$

Indeed $`j/(s+1)\le m j/(s+m)`$. Thus the sign of the sum with the new coefficients at this old zero is $`(-1)^L`$. Separating the change in coefficients before estimating its remainder matters even if $`j`$ grows exponentially in $`m`$.

At equal degrees the new balances differ from the corresponding old balances by the factors $`\gamma_L/\gamma_{L+1}`$, bounded above and below by polynomial factors in $`m`$ from (2), (3) and the case $`p=0`$. They are much closer than distinct old balances. Thus all comparisons except the matching rank follow from the exponentially separated scales. The sign just proved places the old reversed zero before the matching new zero in modulus, since the new polynomial is positive at zero. This gives the required strict alternation.

At a carry $`s=j-1`$ the normalized new reversed row is $`d^\ast+\rho_j^{-1}y\sum d_t\gamma_t y^t`$ with $`d^\ast=(j!)^{-m-1}`$. The extra constant satisfies

$$
\frac{\rho_j d^\ast}{y_0d_0}
=\frac{C_{m-1}(2j-1)}{C_m(j-1)^2}
\le \frac{m}{j}(C m/j)^m=o(m/j).
$$

This follows from (1) at $`j-1,2j-1`$ and the binomial estimates above. At every fixed $`L`$ the dominant-term bound $`d_L y_L^L\ge (1-o(1)) d_0`$ follows from the same tail estimate (it is equality at $`L=0`$). Since $`y_L\ge y_0`$ eventually, the added constant cannot change the sign comparison at any old root. The sign at that root therefore becomes $`(-1)^{L+1}`$, owing to the extra negative factor. The new row has an additional smallest reversed balance $`\rho_j d^\ast/(\gamma_0 d_0)=o(y_0)`$. All its other balances match the old balances up to the factors $`\gamma_L/\gamma_{L+1}`$. The one-row disk counts apply also to the new row, whose residue is zero. These signs and ranks place the old reversed root strictly between the new roots of ranks $`L`$ and $`L+1`$ (using rank zero for the smallest). Taking reciprocals recovers both asserted exterior orderings.
