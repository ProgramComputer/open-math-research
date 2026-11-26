# Necessary and sufficient bounds on the number of retained column factors

For $`n\ge2`$ put $`h_k=\binom nk^s`$ and $`p_k=a(n,k,r,d)/\binom nk^d`$. Define $`S(n)`$ to be the least integer $`s\ge0`$ for which $`B_s(q)=\sum_k h_k p_kq^k`$ is real-rooted for every $`d\ge\max(1,s)`$ and every cap. The binomial multiplier proves monotonicity of this property in $`s`$. Removing one source binomial factor means $`s=d-1`$; that parameter varies with dimension.

Let $`Q=3.23363666\ldots`$ be the partial-theta constant of Katkova, Lobova and Vishnyakova. The original uniform-cap counts obey

$$
\frac{\log Q}{4}\le\liminf_{n\to\infty}\frac{S(n)}n\le
\limsup_{n\to\infty}\frac{S(n)}n\le\frac{\log4}{4}.
$$

The two outer constants are approximately $`0.293402`$ and $`0.346574`$.

## Sufficient bound and sharpness for arbitrary log-concave probabilities

Write $`R_{n,k}=(1+1/k)(1+1/(n-k))`$ and $`R_n=\min_{1\le k<n}R_{n,k}`$, attained at $`\lfloor n/2\rfloor`$. The array orientation theorem proves $`p_k^2\ge p_{k-1}p_{k+1}`$. Each internal coefficient curvature of $`B_s`$ is therefore at least $`R_n^s`$. A value above four gives simple negative roots by the coefficient separation theorem. At equality multiply the coefficients by $`\exp(-\delta k^2)`$ and let $`\delta`$ decrease to zero to obtain weak real-rootedness. Hence $`S(n)\le\lceil\log4/\log R_n\rceil`$, and $`n\log R_n\to4`$. [Orientation estimate](../orientation-normalization.md)

The constant four is sharp under just positivity, monotonicity and log-concavity of probabilities. If $`R_{n,k}^s<4`$, take $`p_j=1`$ through $`k-1`$, then take successive ratios $`\epsilon`$ twice and $`\epsilon^2`$ thereafter, where $`0<\epsilon<1`$. Multiply the polynomial evaluated at $`q/\epsilon`$ by $`\epsilon^{k-1}`$ and let $`\epsilon`$ tend to zero. The limit is $`q^{k-1}(h_{k-1}+h_kq+h_{k+1}q^2)`$, with strictly negative quadratic discriminant. Real-rootedness is closed under coefficient limits of bounded degree, so a positive profile of the prescribed kind fails. The profiles in this sharpness argument are auxiliary.

## Necessary binomial sections for actual arrays

Fix $`1\le m<n`$, take $`d`$ through multiples of $`2n`$, and set $`r=(2m+1)d/(2n)`$. Then $`D=\lfloor nr/d\rfloor=m`$. If each column independently selects a uniform $`k`$-subset, a single row sum is $`\mathrm{Bin}(d,k/n)`$ with variance at most $`d/4`$. At $`k\le m`$ the gap to the cap is at least $`d/(2n)`$, so Chebyshev's inequality and the union bound give $`1-p_k\le n^3/d`$. A universal retained exponent thus requires all the ordinary sections $`H_m(q)=\sum_{k=0}^m h_kq^k`$ to have only real zeros. Any nonreal section gives normalized counterexamples for every sufficiently large $`d`$ in this explicit family. At $`s=1`$ the quadratic section has discriminant $`n(2-n)`$, covering every fixed $`n\ge3`$.

For $`m=\lfloor n/2\rfloor\ge2`$, Newton at $`m-1`$ requires $`R_{n,m-1}^s\ge 2m/(m-1)`$. Explicit finite examples exist for every retained $`s`$. Set $`m=6s+2`$, $`n=2m`$, $`d=128m^3`$, and $`r=(2m+1)d/(4m)`$. Then $`p_k\ge15/16`$ through degree $`m`$. Writing $`R_{n,m-1}=1+x`$ gives $`x=(2m+1)/(m^2-1)`$ and $`sx\le1/3`$. The binomial expansion gives $`(1+x)^s\le 1/(1-sx)\le3/2`$. The actual normalized curvature at $`m-1`$ is bounded by $`(3/2)(16/15)^2<2`$, violating Newton's inequality.

## Limiting necessary constant

Take $`s=S(n)`$ with $`s/n\to c`$ along any convergent subsequence. Newton gives $`c\ge\log(2)/4`$ and the sufficient bound makes $`c`$ finite. Reverse the necessary section at $`m=\lfloor n/2\rfloor`$, divide by the constant coefficient, and dilate the variable to make the linear coefficient one. The resulting coefficients are $`u_0=u_1=1`$ and

$$
u_j=\prod_{i=1}^{j-1}R_{n,m-i}^{-s(j-i)}, \qquad 2\le j\le m.
$$

For each fixed $`i`$, $`n\log R_{n,m-i}\to4`$ at both parities. Consequently $`u_j\to\exp(-2c j(j-1))`$. Since $`s\log R_n\ge2c`$ for all sufficiently large $`n`$, the summable majorant $`\exp(-c j(j-1))T^j`$ works on every disk $`|z|\le T`$. Hurwitz's theorem shows that the entire limit has only real zeros. It equals $`f_a(az)`$ with $`a=e^{2c}`$ and $`f_a(z)=\sum_{j\ge0}a^{-j^2}z^j`$. Katkova, Lobova and Vishnyakova's Theorem 4 requires $`a^2\ge Q`$. This proves the lower bound for both parities. [Version of record](https://doi.org/10.1007/BF03321047) · [Theorem 4](https://www.dcce.ibilce.unesp.br/~dimitrov/ProfRusev/Katkova/14.pdf)

## An effective converse for simple sections

If $`s\ge1`$ and all the sections of degrees $`1,\ldots,n-1`$ have simple negative zeros, all sufficiently large dimensions pass for every cap, with a computable cutoff at this fixed $`n,s`$.

For any proper cap of degree $`2\le m<n`$, one has $`r\ge dm/n`$. For $`k<m`$ Chebyshev gives $`1-p_k\le n^3/(4d)`$. The top probability need only lie in $`(0,1]`$. Consider the monic polynomials

$$
F_u(z)=\sum_{k=0}^{m-1}h_k z^{m-k}+u h_m,\qquad 0\le u\le1.
$$

Both endpoints have $`m`$ simple real roots: $`F_0`$ is $`z`$ times the reversed previous section, and $`F_1`$ is the reversed current section. Their common derivative has $`m-1`$ simple zeros separating both root sets strictly. At every such point both polynomials have the same sign, fixed by their positive leading terms and the rank of the point. Rational probes $`z_i`$ sufficiently close to these derivative zeros have the same nonzero alternating signs for both endpoints. One can find them by root isolation or an exhaustive rational search. Set $`M_i=\min(|F_0(z_i)|,|F_1(z_i)|)>0`$, also a lower bound on $`|F_u(z_i)|`$ throughout the segment. The reversed actual polynomial differs from $`F_{p_m}`$ at the probe by at most $`(n^3/(4d))\sum_{k<m}h_k|z_i|^{m-k}`$. Choose $`d`$ making this less than $`M_i`$ for every probe and every $`m<n`$. The resulting signs and the leading signs at infinity certify the full number of simple real zeros. Positivity of the coefficients locates them on the negative axis. Degrees zero and one are immediate. Full cap has coefficients $`\binom nk^s`$ and is real-rooted for positive integral $`s`$ by binomial multiplication.

For the exact replay one may instead use Hoeffding and a union bound, which give $`1-p_k\le n\exp(-2d/n^2)\le n\cdot 2^{-\lfloor2d/n^2\rfloor}`$ when $`k<m`$. The integer power of two makes the sufficient dimension test rational for each probe. [Exact certificate checker](section_certificate.py) · [Sample cutoffs](section-cutoffs.jsonl).

Thus nonreal sections decide the fixed-row question negatively; simple sections give an effective reduction to finitely many dimensions. A repeated zero in a proper section can require separate analysis. These conclusions concern renormalization. The unit-weight all-parameter conjecture remains open.
