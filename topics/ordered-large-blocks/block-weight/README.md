# The first loss of real-rootedness under a common block weight

Let $F_{n,j}(t,u)$ enumerate ordered partitions of the labeled set $[n]$, with a factor $u>0$ for every block and a factor $t$ for each block of size at least $j$. All block sizes are allowed. Alexandersson's conjecture sets $u=1$. Its general weight-classification question also asks which choices of block weights preserve real-rootedness. This note gives an obstruction to an all-positive-weight proof of the ordered conjecture. Formal coverage is ⬜ None. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Author's weight-classification question and earlier obstructions](https://github.com/PerAlexandersson/RealRooted/issues/2590)

**Theorem.** Write $F_{2j,j}(t,u)=c_0+c_1t+c_2t^2$ and $\Delta=c_1^2-4c_0c_2$. For each fixed $1<\lambda<9/4$, the polynomial at $u=\lambda^{-j}$ has a nonreal conjugate pair for every sufficiently large $j$. For every $\lambda\ge9/4$, it has two distinct negative roots for all sufficiently large $j$. On the diagonal $u=2^{-j}$ the change takes place exactly at $j=13$ among thresholds $j\ge2$.

The smallest positive block weight $u_{\ast}(j)$ at which the two roots coalesce exists for every sufficiently large $j$. Put $C=\binom{2j}{j}$, $A=4^j-2-C$ and $w=A^2/(4\cdot9^j C)$. There is an absolute $\eta<1$ such that $u_{\ast}(j)=w(1+O(\eta^j))$. In particular,

$$
u_{\ast}(j)\sim \frac{\sqrt{\pi j}}4\left(\frac49\right)^j.
$$

The discriminant changes from positive to negative at this crossing. At $u=x\sqrt j(4/9)^j$ for fixed $x>0$, one has $\Delta/c_1^2\to 1-4x/\sqrt\pi$. These statements describe the small-weight end of the parameter range. The original all-size, unit-weight conjecture remains open.

## Counts by occupied boxes

An ordered partition into $b$ blocks is an onto map to $b$ labeled boxes. In size $2j$, two large boxes must both have size $j$. Consequently $c_2=C u^2$. Exactly two boxes contribute $A u^2$ to $c_1$. One box contributes $u$ to $c_1$. Write $\beta_j=C/4^j\sim1/\sqrt{\pi j}$.

For fixed $h\ge3$, the number of assignments with all $h$ boxes occupied and short is $h^{2j}(1+O(\eta_h^j))$ for some $\eta_h<1$. The fraction with an empty box is at most $h((h-1)/h)^{2j}$. For a given box and $\ell\ge j$, the unnormalized number with occupancy $\ell$ is $\binom{2j}{\ell}(h-1)^{2j-\ell}$. Multiplying the summands by $(h-1)^{\ell-j}\ge1$ bounds their sum by $[4(h-1)]^j$. Union over the boxes gives the second exceptional fraction $h[4(h-1)/h^2]^j$.

For the one-large-box coefficient at $b\ge2$, choosing its box and applying the same sum bound gives at most $b[4(b-1)]^j$ assignments. For $b\ge3$, bounding each binomial coefficient by $C$ and summing the remaining geometric series improves this to $2bC(b-1)^j$. Both upper bounds allow empty boxes.

## The transition on the exponential scale

Take $u=\lambda^{-j}$ and set $r_b=4(b-1)/\lambda^b$ for $b\ge2$. If $1<\lambda<2$, a maximum $R=r_{s+1}$ has $s\ge2$, since $r_3>r_2$. The one- and two-box rates $\lambda^{-1}$ and $r_2$ are strictly below $R$. Therefore $c_1=O_\lambda(\beta_jR^j)$, using

$$
\sum_{b\ge3}b r_b^j\le R^{j-1}\sum_{b\ge3}b r_b.
$$

Use $h=2s$ short boxes alone for $c_0$. The identity $(h^2/\lambda^h)(4/\lambda^2)=R^2$ gives $c_0c_2\ge(1-o(1))\beta_j R^{2j}$. Thus $c_1^2/(c_0c_2)\to0$.

For $2\le\lambda<9/4$ one has $r_b\le r_2$ for all $b\ge2$ and $\lambda^{-1}<r_2$. The first marked-box bound and the same summable comparison give $c_1=O_\lambda(r_2^j)$. Taking three short boxes gives $c_0c_2/r_2^{2j}\ge(1-o(1))\beta_j(9/(4\lambda))^j$, which tends to infinity.

For $\lambda\ge9/4$ the sequence $h^2/\lambda^h$ decreases for $h\ge3$. All short boxes require $h\ge3$. Hence $c_0=O((9/\lambda^3)^j)$, with a constant uniform on this range, by summing the ratios to the maximum at power one. The lower bound $c_1\ge A u^2$ now gives $c_0c_2/c_1^2=O(\beta_j(9/(4\lambda))^j)$. This tends to zero even at the boundary. Positivity of the three coefficients gives the asserted signs of the real roots.

## Locating the first double root

The weight $w$ has exponential rate $4/9$. Uniformly for $w/2\le u\le2w$, write $v=u^{1/j}$, so $v\to4/9$. The short-box term $b=3$ gives $c_0=9^j u^3(1+O(\eta^j))$. Indeed the preceding occupancy estimate handles this term. For $b\ge4$ the normalized rates relative to three boxes are $d_b=(b/3)^2v^{b-3}$. At $v=4/9$, $d_4=64/81<1$ and $d_{b+1}/d_b\le(5/4)^2v<1$. Both inequalities hold uniformly on a compact neighborhood. This bounds the sum of the omitted terms even after multiplying by $b$.

Similarly $c_1=A u^2(1+O(\eta^j))$. Relative to $4^j u^2$ the one-box rate is $1/(4v)<1$, and the $b\ge3$ rates are $e_b=(b-1)v^{b-2}$. Their first value $2v$ and subsequent ratios $bv/(b-1)$ are uniformly below one near $v=4/9$. The occupancy bounds carry a prefactor $b$, which is summable with the same geometric decay after a further factor $b$. One may take a common $\eta<1$ slightly larger than these bounds. The comparison also gives $c_0\le9^j u^3(1+O(\eta^j))$ throughout $0<u\le2w$, since every omitted term after division by $u^3$ has nonnegative coefficients in $u$.

Put $R(u)=4c_0c_2/c_1^2$. For $0<u\le w/2$, the preceding upper bound and $c_1\ge A u^2$ give $R(u)\le(u/w)(1+O(\eta^j))<1$. On $[w/2,2w]$ we have $R(u)=(u/w)(1+O(\eta^j))$. Acting by $`u\,d/du`$ weights a $b$-box term by $b$. The bounds with that extra factor give $u c'_0/c_0=3+O(\eta^j)$ and $u c'_1/c_1=2+O(\eta^j)$. Since $u c'_2/c_2=2$, we have $uR'/R=1+O(\eta^j)>0$. This proves existence, uniqueness up to $2w$, and the error claimed for the first crossing. The same uniform estimates hold between any two fixed positive multiples of $w$, yielding the stated limit for every fixed $x>0$.

## An exact diagonal

At $\lambda=2$ the three-box estimate gives $c_0\ge(9/8)^j-3-3/2^j$. The coarse one-large-box bound gives $c_1\le2^{-j}+\sum_{b\ge2}4b(b-1)/2^b<17$, since $4(b-1)/2^b\le1$. The central binomial coefficient is largest in its row, hence $c_2=\beta_j\ge1/(2j+1)$. At $j=100$, $4((9/8)^j-4)>17^2(2j+1)$ follows from $(9/8)^{10}>3$. This inequality persists since $9/8>(2j+3)/(2j+1)$ there and thereafter. Thus the discriminant is negative for all $j\ge100$.

Two integer computations independently count each of the 198 rows with $2\le j\le100$ and weights $1$ and $2^{-j}$. The first removes the first block. The second uses surjection counts and the number of ways of distinguishing a large fiber. On the weighted diagonal both give positive discriminant for $2\le j\le12$ and negative discriminant for $13\le j\le100$. At weight one every tested discriminant is positive. The output includes the exact primitive coefficient vector and discriminant at $(n,j,u)=(26,13,1/8192)$. [Checker](verify.py) · [Exact output](output.txt)

From this directory run

~~~sh
python3 verify.py
~~~

## Sources and scope

An independent agent reconstructed the box-count estimates, checked the transition in each regime and the first-crossing derivative, and reproduced the finite sign change from the original first-block recurrence. The repository checker additionally uses an independent surjection count.

Alexandersson's issue #2590 documents earlier failures with gaps in block sizes and changes in selected block weights. The common weight treated here keeps every size available. On 26 November 2026 we checked the author's issue and its discussion, the independent ordered-partition investigation, and web-indexed GitHub and X queries for “ordered set partitions”, “block weights”, “real-rooted”, and “Alexandersson”. These searches did not locate the diagonal transition above. The web index gives incomplete X and GitHub coverage. [Author's discussion](https://github.com/PerAlexandersson/RealRooted/issues/2590) · [Independent ordered-partition investigation](https://github.com/1337isnot1337/solved-conjectures/issues/108)
