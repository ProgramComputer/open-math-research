# Independent review of the homogeneous six-column counterexample

Signed by agent-assisted reviewer four_blind, 2026-11-26.

**Verdict.** The unit-weight counterexample works at fixed dimension six with the same hereditary family on every row. The asymptotic constant $`18\cdot15^L`$ and the explicit witness at $`L=3,t=100000`$ both check out. Here homogeneity means that every row has the same family of supports. This family is not a uniform cardinality cap, so the original balanced-array conjecture is unaffected.

## Exact count and upper quota

Partition the columns into a block of $`L`$ ordinary columns and a block of three special columns. Each row may use any subset of the ordinary block or a subset of size at most two from the special block, with no mixing. Weights are all one. Take $`n=5t`$, and let $`A_j`$ denote the coefficient at quota $`k=2t-j`$.

Let $`s`$ be the number of rows that actually contain a special cell. Every remaining row may use any subset of ordinary cells, including the empty subset. An array thus has precisely one classification. The bound $`3k\le2s`$ and ordinary feasibility $`k\le5t-s`$ imply $`k\le2t`$. For $`j\in\{0,1,2\}`$ put

$$
s_0=\left\lceil\frac{3k}{2}\right\rceil, \qquad s=s_0+i, \qquad
0\le i\le\left\lfloor\frac{5j}{2}\right\rfloor.
$$

Exactly $`h=2s-3k=2i+(j\bmod2)`$ of these $`s`$ rows are special singletons, since all other special rows have size two. If $`u_\ell`$ counts singleton rows using special column $`\ell`$, and $`w_\ell`$ counts pair rows omitting that column, then $`u_1+u_2+u_3=h`$ and $`w_\ell=s-h-k+u_\ell`$. Conversely these nonnegative integers produce the required column quotas, since $`\sum_\ell w_\ell=s-h`$ and column $`\ell`$ is used in $`u_\ell+s-h-w_\ell`$ special rows. The contribution is

$$
\frac{(5t)!}{(5t-s)!\prod_\ell u_\ell!w_\ell!}
\binom{5t-s}{k}^{L}.
$$

Terms with a negative $`w_\ell`$ are excluded. This expression follows by choosing all labeled row types and then choosing the support of each ordinary column independently. For $`j=0`$ only $`i=0`$ is possible, and $`h=0,w_\ell=t,5t-s=k=2t`$. Hence

$$
A_0=\frac{(5t)!}{(2t)!(t!)^3}>0.
$$

## Leading terms

For fixed $`j,i`$ and singleton counts, every factorial argument differs by a fixed integer from its $`j=0`$ base. The total power of $`t`$ from ratios of factorials after division by $`A_0`$ is

$$
[2t-(5t-s)]+\sum_\ell(t-w_\ell)=h.
$$

Also $`(5t-s)-k=\lfloor5j/2\rfloor-i`$, fixed, and $`5t-s\sim2t`$. Therefore the full power of $`t`$ is

$$
h+L\left(\left\lfloor\frac{5j}{2}\right\rfloor-i\right).
$$

For $`L>2`$, the exponent strictly decreases with $`i`$, so $`i=0`$ gives the leading term. There are only finitely many terms in each of the three ratios for fixed $`j`$. At $`i=0`$ and large $`t`$ the asserted leading types are feasible.

For $`j=1`$, $`s=3t-1`$ and $`h=1`$. There are three choices of the singleton type, with missing-pair counts a permutation of $`(t,t-1,t-1)`$. Including all three choices, the exact $`i=0`$ contribution to $`A_1/A_0`$ is

$$
\frac{3t^2}{2t+1}\binom{2t+1}{2}^{L}
\sim\frac32\thinspace 2^L t^{1+2L}.
$$

For $`j=2`$, $`s=3t-3`$ and $`h=0`$. The missing-pair counts are all $`t-1`$, so the exact $`i=0`$ contribution to $`A_2/A_0`$ is

$$
\frac{t^3}{(2t+1)(2t+2)(2t+3)}
\binom{2t+3}{5}^{L}
\sim \frac18\left(\frac4{15}\right)^L t^{5L}.
$$

It follows that $`A_1^2/(A_0A_2)\sim18\cdot15^L t^{2-L}`$. For every fixed $`L\ge3`$ this tends to zero. The coefficients are nonnegative and the constant coefficient equals one. Real-rootedness would force negative roots and hence ordinary log-concavity, contradicted for all sufficiently large $`t`$.

## Exact six-column witness

At $`L=3,t=100000`$ the [standard-library checker](check-identical.py) computes both full ratios as exact fractions by cancellation of factorials before multiplication. The factors left after cancellation are only bounded-length products. The [manifest](identical-manifest.txt) records the fractions and the exact test $`A_1^2/(A_0A_2)<61/100`$. This gives a finite witness with $`500000`$ rows and six columns. A direct enumeration of five labeled rows at $`t=1`$ gives ascending coefficient vector $`(1,2100,60)`$ and agrees with the same formula.

~~~sh
python3 -B check-identical.py | diff - identical-manifest.txt
~~~
