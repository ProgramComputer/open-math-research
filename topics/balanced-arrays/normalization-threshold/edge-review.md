# Independent review of the binomial normalization edge obstruction

**Verdict.** Both the fixed-row Newton bound and the stronger partial-theta lower bound hold. The latter requires universal real-rootedness for each even row count along the limiting family. It is a necessary condition on the retained exponent.

Fix $`n=2m`$ with $`m\ge2`$. Take $`d`$ through positive multiples of $`2n`$ and $`r=(n+1)d/(2n)`$, so $`\lfloor nr/d\rfloor=m`$. To sample arrays before applying the row caps, independently choose a uniform $`k`$-subset of rows in each column. The number of choices is $`\binom nk^d`$ and each individual row sum is $`\mathrm{Bin}(d,k/n)`$. For $`0\le k\le m`$, cap failure on any given row entails an excess of at least $`d/(2n)`$ above its mean. Hoeffding and the union bound give

$$
1-\varepsilon_d\le p_k:=\frac{a(n,k,r,d)}{\binom nk^d}\le1,\qquad
\varepsilon_d=n\exp(-d/(2n^2)).
$$

Dependence across rows is immaterial for the union bound. Thus the normalized polynomials with a fixed retained exponent $`s\ge0`$ converge at this row count to $`H(q)=\sum_{k=0}^m h_kq^k`$, where $`h_k=\binom{2m}k^s`$. Every locally uniform limit of these real-rooted polynomials, with nonzero constant term, has no nonreal zero by Hurwitz.

Newton at $`m-1`$ for this degree-$`m`$ polynomial demands

$$
\left(\frac{m(m+2)}{(m-1)(m+1)}\right)^s
\ge \frac{2m}{m-1}.
$$

Indeed the left side is the central adjacent-coefficient curvature at $`m-1`$, and the right side is $`\binom{m}{m-1}^2/(\binom{m}{m-2}\binom{m}{m})`$. Hence $`s`$ is at least the quotient of the respective logarithms, asymptotic to $`n\log(2)/4`$. At finite $`d`$, normalization produces coefficients $`p_k h_k`$. When $`\varepsilon_d<1`$, their curvature at $`m-1`$ is at most the left side divided by $`(1-\varepsilon_d)^2`$. For example $`n=4,d=104,r=65,s=1`$ already fails Newton, since $`(8/3)/(1-4e^{-13/4})^2<4`$. One entirely rational verification is $`e^{13/4}>24`$ by the Taylor sum through degree seven, so the displayed expression is less than $`(8/3)/(5/6)^2=96/25<4`$.

Let $`s=s_n`$ along even $`n\to\infty`$ with $`s_n/n\to c\in(0,\infty)`$. Put $`b_j=h_{m-j}`$, reverse $`H`$, divide by its new constant coefficient $`b_0`$, and replace the variable by $`z b_0/b_1`$. The resulting coefficients $`u_{m,j}`$ satisfy $`u_{m,0}=u_{m,1}=1`$ and

$$
u_{m,j}
=\prod_{i=1}^{j-1}
\left[\left(1+\frac1{m-i}\right)
\left(1+\frac1{m+i}\right)\right]^{-s_n(j-i)}
\quad (2\le j\le m).
$$

Here the bracket is the binomial curvature at $`m-i`$, and the product follows by iterating adjacent coefficient ratios. Its logarithm is $`4/n+O_i(n^{-2})`$ for fixed $`i`$, giving $`u_{m,j}\to e^{-2c j(j-1)}`$. Uniformly over $`1\le i<m`$, the bracket is at least $`(1+1/m)^2`$, since it equals $`1+(2m+1)/(m^2-i^2)`$. Therefore $`u_{m,j}\le e^{-c j(j-1)}`$ for sufficiently large $`n`$, by $`s_n\log(1+1/m)\to2c`$. Terms past degree $`m`$ are zero. The summable majorant $`e^{-c j(j-1)}R^j`$ on any disk $`|z|\le R`$ gives locally uniform convergence to $`\sum_{j\ge0}e^{-2c j(j-1)}z^j`$. Reversal and positive dilation preserve real-rootedness since the constant and leading coefficients are positive. Thus if all the limiting $`H`$ are real-rooted, the entire limit has only real zeros by Hurwitz.

Theorem 4 of Katkova, Lobova and Vishnyakova, *On Power Series Having Sections With Only Real Zeros*, Comput. Methods Funct. Theory 3 (2003), 425–441, gives the all-real-zero threshold $`a^2\ge q_\infty`$ for $`f_a(z)=\sum_{j\ge0}a^{-j^2}z^j`$, with $`a>1`$. The limiting function above is $`f_a(az)`$ with $`a=e^{2c}`$, equivalently $`\theta(q,z/q)`$ for $`q=e^{-4c}`$ when $`\theta(q,z)=\sum q^{j(j+1)/2}z^j`$. Hence $`c\ge(\log q_\infty)/4=\log(1/q_*)/4\approx0.2934018516`$, with $`q_*=0.3092493386\ldots`$ the first positive spectral value. The Newton bound excludes $`c=0`$ for universally real-rooted choices. Every finite subsequential ratio is therefore at least this constant, which gives the claimed liminf bound over even row counts. The argument supplies no sufficient condition for the original finite-$`d`$ normalizations. [Katkova–Lobova–Vishnyakova, Theorem 4](https://www.dcce.ibilce.unesp.br/~dimitrov/ProfRusev/Katkova/14.pdf) · [Kostov, first spectral value](https://arxiv.org/abs/1605.05469)

**Signed** — four_literature, independent agent-assisted mathematical review.

## Small exact example at retained exponent one

An independent integer scan of sorted row occupancies found a much smaller exact witness at $`n=4,d=7,r=5`$. It has $`a_1=16296`$ and $`a_2=211176`$, also verified by inclusion–exclusion. For $`k=1`$, a specified row violates the cap in $`7\cdot3+1=22`$ assignments, with no pair intersections. Thus $`a_1=4^7-4\cdot22`$. For $`k=2`$, a specified row violates the cap in $`8\cdot3^7`$ assignments, since it misses at most one column and each column has three possible partners or three pairs avoiding it. For two specified rows the intersection size is $`1+2\cdot7\cdot2+7+7\cdot6\cdot4=204`$. These terms distinguish neither missing a column, one missing one, both missing the same column, and both missing different columns. Three violating rows would require at least 18 ones, exceeding the total of 14. Hence $`a_2=6^7-4\cdot8\cdot3^7+6\cdot204`$. At $`s=1`$ this gives

$$
1+\frac{2037}{512}q+\frac{2933}{648}q^2
$$

with exact discriminant $`-48335287/21233664<0`$.
