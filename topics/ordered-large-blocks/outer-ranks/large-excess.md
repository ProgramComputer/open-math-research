# Outermost zeros when the block threshold dominates the squared degree

Let $`O_{n,j}(t)`$ count ordered partitions by the number of blocks of size at least $`j`$. Put $`n=jm+s`$, $`0\le s<j`$. Suppose $`m\to\infty`$ and $`j/m^2\to\infty`$. Each of the following conclusions is uniform under its stated hypotheses.

- At the carry $`s=j-1`$, both rows have a unique largest-modulus zero, simple and negative, and the next row's zero has larger modulus.
- Along noncarry pairs with $`s/m^2\to\infty`$, both rows have a unique largest-modulus zero, simple and negative, and the old row's zero has larger modulus.
- The same noncarry conclusion holds for each fixed $`s\ge0`$.

These results order just the largest-modulus zeros. The method also identifies an obstruction to taking the fixed-threshold exponential-section limit uniformly. The dominant singularity of the short-block generating function persists in the coefficients of excess degree at least $`j`$.

## Coefficients when the excess is large

Write

$$
 S_j(z)=\sum_{1\le a<j}z^a/a!,\quad
 C_j(z)=\sum_{a\ge j}z^a/a!,\quad
 T_j=(1-S_j)^{-1},\quad L_j=j!z^{-j}C_j .
$$

The reciprocal ordered-block EGF gives, for $`A_{n,k}=[t^k]O_{n,j}(t)`$,

$$
 A_{n,k}/n!=(j!)^{-k}[z^{n-jk}]\thinspace T_j(z)^{k+1} L_j(z)^k.
$$

Put $`\rho=\log 2`$, $`c=(2\rho)^{-1}`$, and

$$
 a_k(e)=[z^e]T_j(\rho z)^{k+1}L_j(\rho z)^k,\qquad D=j!\rho^{-j}.
$$

Thus for any row of degree $`M`$ and residue $`s`$, its normalized reversed coefficients are

$$
 b_h=\frac{A_{jM+s,M-h}}{A_{jM+s,M}}
     =D^h\frac{a_{M-h}(s+jh)}{a_M(s)},\qquad 0\le h\le M.
$$


For $`0\le k\le m+1`$, $`e\le j(m+2)`$, and $`e/m^2\to\infty`$, uniformly,

$$
 a_k(e)=(1+o(1))c^{k+1}\binom{e+k}{k}
       =(1+o(1))c^{k+1}\frac{e^k}{k!}.
 \tag{1}
$$

Also, for $`k\ge1`$ in the same range with $`e+1\le j(m+2)`$,

$$
 \frac{a_k(e+1)}{a_k(e)}=1+(1+o(1))\frac{k}{e+1}.
 \tag{2}
$$

For $`k=0`$, the difference from 1 in (2) is $`O(R^{-e}+e C_j(\rho))`$ for some fixed $`R>1`$; with $`e\ge s`$, $`s/m^2\to\infty`$, this is $`o(m/s)`$.

To prove (1) and (2), first replace $`T_j`$ by $`T_\infty=(2-e^z)^{-1}`$. In the rescaled variable,

$$
 T_\infty(\rho z)=\frac c{1-z}+R_1(z)
$$

where $`R_1`$ is analytic on a fixed disk of radius larger than 1. Let $`A`$ be its coefficient absolute-sum norm on the unit disk. Expand the $`(k+1)`$-st power with $`r`$ terms $`R_1`$. For $`1\le r\le k`$ the magnitude of the coefficient of degree $`e`$ is at most

$$
 \binom{k+1}{r}c^{k+1-r}A^r
     L_j(\rho)^k\binom{e+k-r}{k-r}.
$$

Indeed the coefficient after convolution is bounded by the largest of the nonnegative coefficients of the pole power up to degree $`e`$, times the absolute-sum norm of the other factors. Divide by the principal coefficient. The binomial ratio is at most $`(k/(e+1))^r`$, so summing these terms costs $`O(k(k+1)/e)`$ relatively. The term with $`r=k+1`$ has no pole, and Cauchy's inequality on a fixed radius $`R>1`$ bounds its ratio by $`C^{k+1}R^{-e}`$ for an absolute $`C`$. The same radius bounds $`L_j(\rho z)^k`$, since $`L_j(u)\le(1-u/(j+1))^{-1}`$ for nonnegative $`u<j+1`$. For the principal term the factor $`L_j^k`$ changes its coefficients by relative $`O(k/j)`$, using the same largest-coefficient estimate and $`L_j(\rho)^k=1+O(k/j)`$.

For the difference $`a_k(e+1)-a_k(e)`$, multiply the generating function by $`1-z`$ and extract degree $`e+1`$. Now the principal coefficient is $`c^{k+1}\binom{e+k}{k-1}`$. Apply the same estimate to the singular terms with $`r\le k-1`$. The terms with $`r\ge k`$ are analytic on the fixed larger disk, with the same exponentially small bound up to a constant. The quotient of the principal difference and the principal coefficient of degree $`e`$ is $`k/(e+1)`$.

To pass back to $`T_j`$, the identity $`T_\infty-T_j=T_\infty T_j C_j`$ and nonnegativity give coefficientwise

$$
 0\le T_\infty^{k+1}L_j^k-T_j^{k+1}L_j^k
 \le (k+1)C_j T_\infty^{k+2}L_j^k .
$$

The same coefficient-norm argument bounds the coefficient of degree $`e`$ of the right side in the rescaled variable by

$$
 O(1)(k+1)C_j(\rho)c^{k+2}\binom{e+k+1}{k+1}.
$$

The estimate uses $`C_j(\rho)`$ as a coefficient absolute-sum factor for the singular terms. For the analytic term one may instead use $`C_j(\rho R)`$ on the fixed larger disk, so its contribution is $`O(C^{k+2}R^{-e} C_j(\rho R))`$ relative to the principal coefficient. The ratio of the displayed singular bound to the old principal coefficient is $`O((e+k+1)C_j(\rho))`$. For differences the absolute error is at most the sum of the errors at degrees $`e`$ and $`e+1`$. Even after division by $`k/(e+1)`$, the error vanishes uniformly because $`C_j(\rho R)\le 2(\rho R)^j/j!`$ for large $`j`$ and $`e\le j(m+2)`$. The $`k=0`$ estimate follows directly by the analytic remainder and the same truncation bounds. This proves (1) and (2).

## Isolating the largest zero

For $`s/m^2\to\infty`$, set $`u=s/j`$. From (1), uniformly over $`h`$,

$$
 b_h=(1+o(1))(D/(cj))^h(m)_h\thinspace \frac{(u+h)^{m-h}}{u^m}.
$$

Hence for $`h\ge2`$, $`b_h/b_1^h\le 2^{h+1}(\sqrt3/2)^{mh}`$ for all sufficiently large $`m`$. To see this, discard the factors $`(m)_h/m^h\le1`$ and $`((u+1)/(u+h))^h\le1`$. The base
$`u^{h-1}(u+h)/(u+1)^h`$ increases with $`u>0`$: the derivative of its logarithm is $`h(h-1)/(u(u+h)(u+1))>0`$. At $`u=1`$ it is $`(h+1)/2^h\le(\sqrt3/2)^h`$. The factor $`2^{h+1}`$ absorbs the uniform asymptotic errors.

For fixed $`s`$, $`a_m(s)=O_s(m^s)`$ and the numerator $`a_{m-h}(s+jh)`$ still obeys (1) for $`h\ge1`$. The same coefficient estimate thus gives

$$
 \frac{b_h}{b_1^h}\le 2^{h+1}
 \left(a_m(s)c^{-(m+1)}(2m/j)^m\right)^{h-1},
 \qquad h\ge2.
$$

Indeed $`(s+jh)/(s+j)\le h`$, $`h\le2^{h-1}`$, $`s+j\ge j`$, and $`(m-1)!^h/(m-h)!\le m^{m(h-1)}`$. This argument also covers the new row at the carry by using its own degree $`M=m+1`$ and $`s=0`$.

In either case the normalized reversed polynomial is $`1+x+\sum_{h\ge2}(b_h/b_1^h)x^h`$. The tail goes to zero uniformly on $`|x|\le2`$, and is exponentially small in $`m`$. Rouché on $`|x|=2`$ gives just one zero counted with multiplicity there. On each fixed small circle about $`-1`$, Rouché gives its convergence to $`-1`$. Conjugation gives a real negative simple zero. Reversing proves the largest-modulus assertion, with modulus asymptotic to $`b_1`$.

## Ordering the actual pair

At the carry $`s=j-1`$, formula (1) gives $`b_1^{\rm old}\sim(D/(cj))m2^{m-1}`$, whereas the degree increases and $`b_1^{\rm next}\sim D c^{m+1}j^m/m!`$. Their ratio tends to infinity, giving the required strict order.

For the same-degree step with bounded $`s`$, take the coefficient of degree $`s`$ in $`T_j(w/m)L_j(w/m)^mT_j(w/m)^m`$. Local convergence to $`e^w`$ gives $`a_m(s)\sim(\rho m)^s/s!`$ after rescaling by $`\rho`$. Formula (2) at $`e=s+j`$ gives $`b_1^{\rm next}/b_1^{\rm old}\sim (s+1)/(\rho m)`$. This again separates the actual roots.

For $`s/m^2\to\infty`$ and $`s\le j-2`$, a relative root approximation alone is insufficient, since the separation can be much smaller than the reversed tail. Put

$$
 \gamma_h=\frac{a_{m-h}(s+jh+1)}{a_{m-h}(s+jh)}.
$$

The same expansion gives $`\gamma_0-\gamma_1\ge m/(3s)`$ eventually, since the principal difference is $`m/(s+1)-(m-1)/(s+j+1)`$ and $`s<j`$. Also $`\max_h|\gamma_h/\gamma_0-1|=O(m/s)`$. Use the old scaling $`b_1`$ for both reversed polynomials. At the old zero $`x=-1+o(1)`$, the difference of the new and old normalized reversed values is

$$
 (\gamma_1/\gamma_0-1)x
 +\sum_{h\ge2}(\gamma_h/\gamma_0-1)(b_h/b_1^h)x^h .
$$

The first term is positive of order $`m/s`$; the tail is $`o(m/s)`$ by the exponential bound. The next reverse polynomial is therefore positive at the old reciprocal zero. Both reversed polynomials have one simple negative zero in $`|x|<2`$ also on this shared scale, since $`\gamma_1/\gamma_0\to1`$ and the normalized tail is small. The value at $`x=0`$ is positive, so the next reciprocal zero lies strictly to the left of the old reciprocal zero. Reversing gives the required old-largest-first order without a lower bound on the absolute separation.

At $`s=0`$ the old fixed-threshold limit would place $`b_1`$ on the scale $`(\alpha m)^j`$, with $`\alpha=1+1/(j+1)`$. Here $`b_1\sim D c^m j^{m-1}/(m-1)!`$. The extra $`j!\rho^{-j}`$ scale cannot be absorbed uniformly as $`j/m^2\to\infty`$. In fact the singleton term gives the exact inequality $`b_1\ge j!`$ at $`s=0`$. Thus $`b_1/(\alpha m)^j\ge(j/(e\alpha m))^j\to\infty`$ whenever $`j/m\to\infty`$. Consequently this joint regime requires a different leading coefficient mechanism. The [renewal argument](renewal.md) handles every residue when $`j/m\to\infty`$. The [comparable-threshold argument](comparable.md) handles bounded $`j/m`$.

## Provenance and scope

The primary question is the ordered-block conjecture in the set-partitions section of [Alexandersson's catalog](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions). The [repository tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1) records fixed-threshold eventual interlacing and earlier joint inner-root results. The [independent investigation](https://github.com/1337isnot1337/solved-conjectures/issues/108) records the reciprocal EGF and coefficient identities, and the [author's broader problem](https://github.com/PerAlexandersson/RealRooted/issues/2590) distinguishes ordered and unordered models.

I checked these primary and GitHub sources on 26 November 2026 and searched indexed GitHub and X for Alexandersson, ordered set partitions, large blocks, outer zeros and interlacing. The specific X and alternate GitHub searches returned no results. Indexed searches can miss work. The target here is one necessary outer-root comparison, which removes an endpoint obstruction for a genuine joint-limit regime. The review point is the proof of the dominance estimate and the actual next-row sign, or a precise failure of those estimates. The consolidated fixed-rank theorem uses the two independently reviewed arguments linked above. The quantitative rank-one refinement is recorded separately in [the carry note](carry.md).
