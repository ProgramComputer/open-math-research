# An absolute polynomial row bound for balanced arrays

**Theorem.** There is an absolute $`C>0`$ such that, for every integer $`d\ge2`$, every $`1\le r\le d`$, and every integer $`n\ge C d^4\log(d+1)`$, the balanced-array polynomial $`P(q)=\sum_{k=0}^D a_k q^k`$, $`D=\lfloor nr/d\rfloor`$, has exactly $`D`$ simple negative zeros. Its coefficients count labeled $`n`$ by $`d`$ binary arrays with all column sums $`k`$ and all row sums at most $`r`$. For $`d=1`$, $`P(q)=(1+q)^n`$.

Thus any counterexample to the original real-rootedness conjecture must have $`n<Cd^4\log(d+1)`$, uniformly over the cap. The constant is existential. A fixed-dimensional threshold of unspecified growth, and a threshold uniform in dimension at each fixed cap, were previously known. The new bound restricts the growth of the largest possible exceptional row count as the dimension increases. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Fixed-cap theorem](https://github.com/ProgramComputer/open-math-research/tree/f7e10f84dd21fec44ca58c60bae0879d12ebd89b/topics/balanced-arrays/fixed-cap)

## Reduction and angular levels

Failure for every $`C`$ would give a sequence with $`n/(d^4\log(d+1))\to\infty`$. Bounded $`d`$ is excluded by the fixed-cap theorem, as finitely many caps are then involved. The full cap $`r=d\ge2`$ has simple negative roots by the binomial multiplier theorem. Fix the absolute near-saturation threshold $`h_0`$ from the upper saddle estimate first. The interior estimate then has fixed positive deficit parameter $`\eta=h_0`$, and its cutoff constant can be chosen after $`h_0`$ is fixed. Pass to $`d\to\infty`$ and $`r<d`$. Put $`T=nr/d`$, $`D=\lfloor T\rfloor`$, $`b=d^2/n`$ and $`\nu=(d-1)/2`$. We have $`b\to0`$ and $`D/d\to\infty`$. Every integer quota between 0 and $`D`$ is feasible. For instance, split $`dk`$ slots among the $`n`$ rows in groups of at most $`r`$ and fill the slots successively with the repeating sequence of columns $`1,\ldots,d`$. [Full-cap result](https://github.com/ProgramComputer/open-math-research/blob/f7e10f84dd21fec44ca58c60bae0879d12ebd89b/topics/balanced-arrays/finite-linear-reduction.md)

At row tilt $`w>0`$ put $`H(w)=\sum_{s=0}^r\binom ds w^s`$, with normalized size law $`S`$, mean $`\mu`$, variance $`V`$, and $`h=r-\mu`$. Write $`w_x`$ for the tilt with $`y(w_x)=x`$, where $`y=n\mu/d`$. This covers $`0<x<T`$ since $`\partial_{\log w}\mu=V>0`$. For $`t_*=\pi/d`$ and $`G(s)=s(d-s)/(d(d-1))`$, define

$$
\lambda_t=\frac{\mathbb E[G(S)e^{itS}]}{\mathbb E e^{itS}},
\qquad \Psi(w)=n\arg H(we^{it_{\ast}})-\nu\arg\lambda_{t_{\ast}}.
$$

At $`0\le t\le t_*`$ both positive-weight characteristic sums lie in the closed sector from zero angle to $`rt<\pi`$, so the arguments continued from zero exist. The limiting values of $`\Psi`$ at zero and infinity are $`-\nu t_*`$ and $`T\pi`$. The lower limit uses the first nonzero degree of the $`G`$-weighted polynomial, and the upper limit uses $`G(r)>0`$. For $`1\le k<D`$ define $`v_k`$ as the first radius attaining $`\Psi=k\pi`$. Continuity gives strictly increasing $`v_k`$.

The following estimate controls the locations of the levels with an unbounded cap:

$$
|\Psi(w)/\pi-y|\le C_1 d+\frac{C_1}{\sqrt d}\min(y,T-y).
\tag{1}
$$

For a coordinate indicator $`X_1`$ and $`p=\mu/d`$, exchangeability gives $`V=d\,\mathrm{Cov}(S,X_1)=dp(1-p)(\mathbb E[S\mid X_1=1]-\mathbb E[S\mid X_1=0])`$. Given $`X_1=1`$ or $`X_1=0`$, the number of other successes has the same $`(d-1)`$-trial tilted binomial law truncated at $`r-1`$ or $`r`$, respectively. The former truncation has smaller mean, so the conditional difference for $`S`$ is at most one and $`V\le\mu(1-\mu/d)\le d/4`$. Also $`V\le m(1+m)`$ for $`m=\mu`$ and for $`m=h`$. To see this for any nonnegative integer variable $`X`$ with log-concave mass on $`[0,r]`$ and mean $`m`$, write $`F_j=\mathbb P(X\ge j)`$. Its ratios $`F_{j+1}/F_j`$ decrease since $`F_j/\mathbb P(X=j)`$ is the sum of products of consecutive decreasing mass ratios. Hence $`F_{i+j}\le F_iF_j`$ and

$$
\mathbb E[X(X-1)]/2=\sum_{i,j\ge1}F_{i+j}\le m^2 .
$$

Apply this to $`S`$ and $`r-S`$. Combining the two variance bounds at $`m=\sqrt d`$ gives $`V\le C\sqrt d\min(\mu,h)`$. Now $`|\mathbb E e^{it(S-\mu)}-1|\le V t^2/2`$ by Taylor with centered linear term. This is $`O(1/d)`$ on $`[0,t_*]`$, whence $`|\arg H(we^{it_*})-\mu t_*|\le C V/d^2`$. Finally $`|\arg\lambda_{t_*}|\le\pi`$ by the sector property. Substituting gives (1). [Uniform interior saddle and variance bound](very-tall-interior-saddle.md)

Consequently, at $`w=v_k`$, bounded $`k/d`$ implies $`y=O(d)`$, and bounded $`(D-k)/d`$ implies $`T-y=O(d)`$. If both indices divided by $`d`$ tend to infinity, so do $`y/d`$ and $`(T-y)/d`$, by applying (1) to either hypothetical bounded subsequence.

## The determinant phase at the ends

Suppose $`k/d\to c`$ with $`0<c<\infty`$. By (1), $`\mu=O(b)`$ at the crossing. The size law then has $`\mathbb E|S-\mu|^3=O(\mu)`$, and the law reweighted by $`G`$ has expected distance $`O(\mu)`$ from size one. Indeed $`dw=O(\mu)`$, $`p_s\le(dw)^s/s!`$, $`p_1\asymp\mu`$, and $`G(s)/G(1)\le s`$. Thus $`\arg\lambda_{t_*}=t_*+O(\mu t_*)`$. The centered characteristic argument at $`t_*`$ is $`O(\mu t_*^3)`$ by the vanishing linear term and the third absolute moment. Since $`n\mu t_*^3=O(y/d^2)=o(1)`$, the level equation gives $`y(v_k)=k+1/2+o(1)`$.

Suppose instead $`(D-k)/d\to c`$ with $`0<c<\infty`$. We have $`h=O(b)`$ at the crossing. For $`J=r-S`$ let $`p'_j=\mathbb P(J=j)`$. By log-concavity all forward ratios are at most $`p'_1/p'_0\le h/(1-h)`$. It follows that $`\mathbb E|S-\mu|^3=O(h)`$, and that the $`G`$-weighted mean distance from $`r`$ is $`O(h)`$, using $`G(r-j)/G(r)\le1+j`$. We obtain $`\arg\lambda_{t_*}=O(h t_*)`$ and a centered characteristic argument $`O(h t_*^3)`$. Thus $`y(v_k)=k+o(1)`$.

At real $`x`$ within bounded distance of either such $`k`$, the variance is asymptotic to $`dx/n`$ at the lower end and to $`d(T-x)/n`$ at the upper end. At the lower end this follows from the small-mean factorial moments. At the upper end it follows from the geometric domination of $`J`$, which gives $`\mathbb E J(J-1)=O(h^2)`$. Differentiation yields $`\frac{\mathrm d}{\mathrm dx}(d\log w_x)=b/V_x`$, tending to $`1/c`$ uniformly on each bounded window. Integrating from $`k`$ to $`y(v_k)`$ gives the two expansions

$$
d\log v_k=d\log w_k+d/(2k)+o(1)\quad(k/d\to c),
\qquad d\log v_k=d\log w_k+o(1)\quad((D-k)/d\to c).
\tag{2}
$$

## Signs and degree

Write $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$ and $`\Gamma_k=a_k^2/(a_{k-1}a_{k+1})`$. In either finite positive overlap above, endpoint coefficient estimates show that $`\log\Gamma_{k+j}\to1/c`$ for every fixed integer $`j`$ and $`\log t_k=d\log v_k+o(1)`$. The lower endpoint proof compares with independent columns. The upper endpoint proof conditions on the complete row-size profile, including at exact saturation. At distances with $`k/d\to0`$ or $`(D-k)/d\to0`$, they show $`\Gamma_k\to\infty`$. [Nearly empty rows](very-tall-nearly-empty.md) · [Nearly saturated coefficients](very-tall-upper-quota.md)

By the orientation inequality the $`a_k`$ are strictly log-concave at internal quotas. If $`\Gamma_k>4`$, the centered normalized alternating polynomial at $`t_k`$ is at least $`1-2/\sqrt{\Gamma_k}>0`$ because the two tails beginning at distance two alternate with decreasing magnitudes. In the finite positive overlaps, for $`x=t_k`$ or $`v_k^d`$, the terms at each fixed distance $`j`$ from the center converge after normalization to $`e^{-j^2/(2c)}`$. Indeed the terms at distance one have the required relative magnitudes by the definition of $`t_k`$ and (2), and the consecutive logarithmic differences follow from $`\log\Gamma_{k+j}`$. Beyond any large fixed distance $`L`$, log-concavity bounds the outward ratios by a geometric factor $`<1`$ uniformly, using the ratio at $`L`$. Taking $`L\to\infty`$ therefore yields

$$
\frac{(-1)^kP(-x)}{a_kx^k}\longrightarrow
\sum_{j\in\mathbb Z}(-1)^j e^{-j^2/(2c)}
=\sqrt{2\pi c}\sum_{m\in\mathbb Z}e^{-2\pi^2 c(m+1/2)^2}>0.
$$

Here the last identity is Poisson summation. [Orientation inequality](https://github.com/ProgramComputer/open-math-research/blob/f7e10f84dd21fec44ca58c60bae0879d12ebd89b/topics/balanced-arrays/orientation-normalization.md)

If $`k/d,(D-k)/d\to\infty`$, set $`w=v_k`$. Then $`n\mu/d^2,nh/d^2\to\infty`$ from (1). On the product-negative torus, character integration of the $`n`$th power of the row generating function gives $`P(-w^d)`$, as only the common column exponents survive. The two principal contributions have phase $`\pm\Psi(w)`$ and equal positive amplitude. Their sum differs from the exact polynomial by $`o(1)`$ times the amplitude of one contribution. This conclusion covers every tilt: use the small-mean proof for $`\mu\le1/10`$, the near-full proof for $`h\le h_0`$ with fixed absolute $`h_0>0`$, and the interior proof for $`\mu\ge1/10`$, $`h\ge h_0`$. All three estimates use the branch of the quadratic determinant obtained from the positive real tilt. At the first crossing $`\cos\Psi(w)=(-1)^k`$, giving the desired strict sign. [Nearly empty rows](very-tall-nearly-empty.md) · [Near-full angular estimate](growing-cap-upper-saddle.md) · [Interior angular estimate](very-tall-interior-saddle.md)

For $`k\le d`$ or $`D-k\le d`$ use $`t_k`$, and at all other internal quotas use $`v_k^d`$. Inside their respective ranges the points increase by strict log-concavity and by continuity at the first crossings. At either join the adjacent geometric logarithms differ by $`(\log\Gamma_k+\log\Gamma_{k+1})/2\to1`$; replacing one geometric radius by the corresponding phase radius changes its logarithm by $`o(1)`$ by the overlap estimates. The endpoints are zero and positive infinity, with signs $`1`$ and $`(-1)^D`$. A subsequence with any failed interior sign has a further subsequence with limits of $`k/d`$ and $`(D-k)/d`$ in $`[0,\infty]`$. Their sum tends to infinity. The arguments above exclude a zero limit, a positive finite limit and two infinite limits. Thus the signs alternate at every one of these ordered points. By continuity the reflected polynomial has $`D`$ distinct positive zeros, exhausting its degree. This gives the stated simplicity and negativity and rules out the assumed sequence of counterexamples.
