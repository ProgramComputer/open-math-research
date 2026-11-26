# Bernstein Bézout matrices for the shared cycle weight

Write $p(x,u)=Q_{n,k}(x,u)$ and $q(x,u)=Q_{n+1,k}(x,u)$ for the common cycle weight with the first cycle unmarked. The proposed all-size certificate asks for positive definiteness of every Bernstein coefficient matrix of

$$
\frac{q(x,u)p(z,u)-p(x,u)q(z,u)}{x-z}.
$$

Exact positive definiteness holds for 225 consecutive pairs through old size 34 and for the independent-weight witness pair $(48,21)$. The general condition fails at $(n,k)=(5376,2560)$ and for all sufficiently large integers $m$ along $n=21m$, $k=10m$. The middle degree-two Bernstein coefficient matrix is indefinite. The calculation isolates a direction without changing the cycle weight between the rows.

## A trailing-block limit

Both rows are affine in $u$, since they allow at most two cycles. Their ordinary degrees in $x$ differ by one. Each is reciprocal by permutation inversion. Reversing the monomial basis in the Bézout matrix gives the kernel

$$
\frac{xp(x,u)q(z,u)-q(x,u)zp(z,u)}{x-z}.
$$

For a fixed rank $r\ge1$, put $b_{n,r}(u)=[x^{r-1}]p(x,u)/r^n$. For any fixed $1\le r\le11$, the decreasing-run encoding gives a coefficientwise limit $b_r(u)$ for both old and new normalized rows. In the encoding, the excedance boundaries are valid whenever every color occurs in both halves of the word, an event of probability tending to one. A cycle containing $j$ colors receives a fraction tending in probability to $j/r$ of the letters. Thus in the limit the admissible color permutations are exactly those with every cycle length strictly greater than $10r/21$. None of these comparisons is at equality for $r\le11$. Each admissible permutation of $r$ colors contributes $u^{c-1}/r!$. [Run encoding and fixed-rank coefficients](independent-cycle-weights.md)

For odd $r\le11$, the minimum color cycle length is $(r+1)/2$, so only a full cycle occurs. For even $r\le10$, the minimum is $r/2$, and two cycles must have equal lengths. There are $(r-1)!$ full cycles and $r!/[2(r/2)^2]$ unordered equal-length cycle pairs. Consequently

$$
r b_r(u)=1+2\eta_r u,
\qquad
\eta_r=
\begin{cases}
1/r& r\text{ even},\\
0& r\text{ odd}.
\end{cases}
$$

Use the first eleven coordinates of the reversed basis, indexed by $r=1,\ldots,11$, and scale coordinate $r$ by $r^{1-n}$. To see the limit of entry $(r,s)$, let $A=xp$ and $B=q$. The kernel entry before scaling is the sum of $A_a B_b-B_a A_b$ over $a+b=r+s-1$ and $a\ge\max(r,s)$. The first product uses coefficient ranks $a,b+1$. At $a=\max(r,s)$ their product of ranks is $rs$. Every other summand has a strictly smaller product of ranks, including every second product, whose ranks are $a+1,b$. Terms involving zero ranks vanish. Since the normalized fixed-rank coefficients are bounded by one, all terms with smaller products of ranks vanish exponentially after scaling. The leading term has the additional factor $\min(r,s)$ from the new row's extra letter. The scaled entry thus tends coefficientwise to $\min(r,s)\,(rb_r(u))(sb_s(u))$.

The middle Bernstein coefficient of $c_0+c_1u+c_2u^2$ is $c_0+c_1/2$. Accordingly the scaled middle matrices converge on this block to

$$
K_{rs}=\min(r,s)(1+\eta_r+\eta_s).
$$

With the integer vector

$$
v=(12,-16,23,-17,20,-16,17,-14,14,-10,4),
$$

the exact quadratic form is $v^TKv=-5/2$. This gives a negative direction for the middle coefficient matrix for all sufficiently large $m$. The full coefficient matrix also has a positive direction, for instance the diagonal entry indexed by the highest power in the unreversed basis, which is identically one by monicity. The claim is an obstruction to the Bernstein matrix condition. It leaves open positive definiteness of the evaluated Bézout matrix throughout $[0,1]$ and strict interlacing at each common weight.

## Why the different-weight exterior sign argument does not transfer directly

In the unreversed monomial basis, an entry indexed by $r,s$ has dominant product of ranks $(\max(r,s)+1)\min(r,s)$. Scaling coordinate $r$ by $[r(r+1)]^{-n/2}$ leaves nonzero diagonal limits, while each off-diagonal scaling factor decays exponentially. The diagonal difference of the two leading products is asymptotic to $b_r(u)b_{r+1}(u)$ because the weight is shared and the new-row rank multipliers differ by one. Every Bernstein coefficient of this limit is positive because its ordinary coefficients are nonnegative and its constant coefficient is positive. This gives positive definiteness for every fixed low-degree block in this asymptotic regime. The obstruction is in the reversed block, where the dominant off-diagonal factors do survive normalization. The threshold for allowing equal color-cycle splits there changes between even and odd ranks.

The low-degree block conclusion can be made uniform in $3\le k\le n$, without a fixed limit of $n/k$. For each fixed number of colors $r$, couple the two words by appending one random color and use the same color permutation. The probability that some color fails to occur in both halves of either word is exponentially small in $n$. Apart from that event, a proper color cycle can change its threshold acceptance only if its count before the appended letter was $k-1$. For a cycle on $j<r$ colors this count is binomial with parameter $j/r$, whose maximum mass is $O_r(n^{-1/2})$. A full color cycle is accepted in both rows. Thus the difference of the two normalized fixed-rank coefficient vectors tends to zero uniformly in $k$, and their constant terms are uniformly bounded away from zero, by the full-color-cycle event. Converting an ordinary coefficient of $u^a$ to any Bernstein coefficient at fixed ambient degree multiplies it by a number between zero and one. For any fixed block size the scaled diagonal errors are therefore uniformly small at every Bernstein index, and the scaled off-diagonal terms are uniformly exponentially small. Diagonal dominance proves positive definiteness of these fixed unreversed blocks for sufficiently large $n$.


## Exact finite witness

For $(n,k)=(5376,2560)$ take the same vector $v$ and use integer coordinates $z_r=v_r(27720/r)^{n-1}$ in the first eleven positions of the reversed basis, with all other coordinates zero. Here $27720$ is a common multiple of all eleven indices. The checker evaluates the quadratic form of twice the middle Bernstein matrix on $z$ and obtains a strictly negative integer. This scaling is equivalent to the limiting scaling above up to one positive common factor. The check uses the first 22 coefficients of the rows, found from the Eulerian finite-difference formula and the two-cycle expansion. It requires no root finding or floating-point arithmetic.

## Positive finite certificates

A stronger possible invariant uses the full symmetric Bézout matrix. For old and new monic polynomials $p(x,u)$ and $q(x,u)$, let $H(u)$ be the matrix of the kernel

$$
\frac{q(x,u)p(z,u)-p(x,u)q(z,u)}{x-z}
$$

in the monomial bases of degree below $\deg_x q$. Set $M=\deg_u p+\deg_u q$. Expand $H(u)$ in the degree-$M$ Bernstein basis on $[0,1]$. Positive definiteness of every coefficient matrix ensures positive definiteness throughout the interval, since the Bernstein basis functions are nonnegative and sum to one. A shared root $x$ would make the corresponding kernel evaluation at $x$ zero identically in $z$, making $H(u)$ singular. Thus the positive coefficient matrices suffice for the collision criterion. At weight zero the Eulerian rows strictly interlace, and the original variable polynomials remain monic at all weights. The matrix criterion therefore gives strict consecutive interlacing throughout the interval.

The exact check gives positive definite coefficient matrices for all 225 pairs $6\le n\le34$, $3\le k\le\lfloor n/2\rfloor$, and separately for $(n,k)=(48,21)$. The latter is the pair with a known failure for independent weights. In this affine case the middle Bernstein matrix is the average of the two crossed-weight Bézout matrices, one of which is indefinite by the independent-weight Wronskian witness. Its exact positive definiteness shows that the two crossed terms can restore the desired sign after averaging. The computation constructs the two rows by the smallest-cycle recurrence, forms the Bézout coefficient matrices by bilinearity, and converts to Bernstein coefficients using

$$
u^j=\sum_{i=j}^{M}\frac{\binom ij}{\binom Mj}\binom Mi u^i(1-u)^{M-i}.
$$

For the symmetric matrices scaled by $M!$, fraction-free elimination checks every leading principal minor is positive. The middle-coefficient counterexample above shows that the certificate fails in larger rows. [Earlier scalar Bernstein resultant test](cycle-marking.md) · [Independent-weight witness](independent-cycle-weights.md)

## Replay and verification status

Run from the repository root with Python 3.10 or later. The checker verifies every matrix sign above, including the exact finite negative witness and rational limiting form.

~~~sh
python3 -I -B topics/long-cycle-excedances/verify_bernstein_bezout.py
~~~

**Formal verification** ⬜ None. These are written arguments and exact Python checks. The all-size shared-weight interlacing question and the [original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) remain open.
