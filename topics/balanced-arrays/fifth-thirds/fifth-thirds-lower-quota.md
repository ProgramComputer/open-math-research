# Positive lower quotas when $`r/b`$ tends to infinity

Let $`d\to\infty`$, $`b=d^2/n\to\infty`$, $`b=o(d^{1/3})`$, $`1\le r<d`$ and $`r/b\to\infty`$. At $`k/d\to\beta\in(0,\infty)`$ the original array coefficients satisfy, for every fixed integer $`j`$,

$$
\log\Gamma_{k+j}\to1/\beta,\qquad
\log t_k=d\log w_k+d/(2k)+o(1),
\qquad d\log v_k=\log t_k+o(1).
$$

Here $`w_x`$ produces mean row size $`dx/n`$, $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$, and $`v_k`$ is the first hitting point of the occupied-cell phase $`k\pi`$. [Definitions and global phase inequality](https://github.com/ProgramComputer/open-math-research/blob/4fb624ba937a8eecc1361a6066185cd81ab7b172/topics/balanced-arrays/quadratic/proof.md)

## Capped counts and a row switch

On bounded translates $`i`$ of $`k`$ put $`p=i/n`$, $`m=di/n\sim\beta b`$, $`M=di\asymp d^2`$, $`K_i=\binom ni^d/\binom{nd}{di}`$ and $`A_i=[z^{di}]H(z)^n`$ for $`H(z)=\sum_{s\le r}\binom ds z^s`$. Under the uniform measure on the balanced capped arrays, let $`N_s`$ be the number having $`s`$ entries in row one. Move a one out of this row in its original column, into a row with space and with zero in that column. There are at least $`s(n-i-M/r)`$ moves per array: at most $`i`$ receivers are occupied in that column and at most $`M/r`$ rows are full. Each reverse move has at most $`(d-s+1)i`$ choices. Each move is reversible with the column and the other row specified. Since $`m/r\to0`$ and $`p\to0`$, for large $`d`$ we obtain $`N_s\le (2m/s)N_{s-1}`$ for $`1\le s\le r`$. Thus the probability that some row exceeds $`L=\lceil B(m+\log n)\rceil`$ is less than $`n^{-10}`$ for a sufficiently large absolute $`B`$, by $`N_s/\sum N_j\le(2m)^s/s!`$ and summation. The exponent 10 can be replaced by any fixed number by increasing $`B`$.

The scalar tilted law $`S`$ is a binomial of underlying mean $`m_0`$ conditioned on $`S\le r`$, with conditional mean $`m`$. It has $`m\le m_0\le2m`$ for large $`d`$. Indeed at trial binomial mean $`2m`$ the right tail above $`r`$ is superexponentially small in $`m`$ since $`r/m\to\infty`$, so its conditioned mean exceeds $`m`$, and conditioned means increase in the tilt. More precisely, for any fixed moment order $`j`$, the deleted raw moment at $`m_0\le2m`$ is $`o(m^{-A})`$ for every fixed $`A`$: using the factorial generating function or the binomial mgf at $`t=1,2`$ gives $`\mathbb E[Z^j\mathbf1_{Z>r}]\le C_j\exp(2m(e^2-1)-r)`$. Since $`r/m\to\infty`$, this proves the bound, with no claim it is smaller than every inverse power of $`n`$. The variance therefore satisfies $`V=m(1+o(1))`$, the absolute third centered moment is $`O(m^{3/2})`$ by the binomial fourth moment, and $`|dV/dm|=O(\sqrt m)`$.

At $`L=B(m+\log n)`$ the scalar upper tail with any fixed polynomial weight is instead $`O(n^{-A})`$ for any desired fixed $`A`$ by increasing $`B`$, from the same generating function bound and $`\mathbb P(Z\le r)\ge1/2`$. At the integer total $`M=nm`$ the scalar sum of $`n`$ copies has mass at least $`1/(nd+1)`$. In fact its log-concave mass function (convolution of log-concave sequences) has concave piecewise-linear log interpolation, so its log mass at its integer mean is at least the expectation of its log mass, at least $`-\log(nd+1)`$ by entropy. Conditioning on that total therefore also leaves negligible probability of any row larger than $`L`$.

## Uniform margin correction

For profiles below $`L`$, Greenhill–McKay–Wang's Corollary 5.2 applies uniformly. The maximum-degree product is $`Li=o(d^{4/3})=o(M^{2/3})`$, the column variance is zero, and the normalized row variance is at most $`L/(1-p)=O(M^{1/3})`$. All profiles of total $`M`$ are feasible by cyclically assigning the $`M`$ entries in order to the $`d`$ columns. The count is $`K_i\prod_j\binom d{s_j}`$ times the exponential of

$$
-1/2+\frac{\sum_j(s_j-m)^2}{2nm(1-p)}+o(1).
$$

[Greenhill–McKay–Wang, Corollary 5.2](https://web.maths.unsw.edu.au/~csg/papers/irregular-final.pdf#page=33) · [Version of record](https://doi.org/10.1016/j.jcta.2005.03.005)

To average this weight, clip $`(S-m)^2`$ to zero above $`L`$. The clipped expectation differs from $`V`$ by $`O(n^{-10})`$ after increasing $`B`$. For independent rows Hoeffding at tolerance $`m d^{-1/10}`$ on the row average gives exceptional probability at most $`2\exp(-c n d^{-1/5}m^2/L^4)`$. This exponent dominates $`L+\log(nd)`$. When $`b\ge\log n`$ the ratio to $`L`$ is at least a constant times $`n d^{-1/5}/b^3\to\infty`$, since $`b=o(d^{1/3})`$ and $`n=d^2/b`$. Otherwise the denominator is at most a constant times $`(\log n)^5`$ after comparison to $`L+\log(nd)`$, and $`n d^{-1/5}/(\log n)^5\to\infty`$. Conditioning on the total costs at most $`nd+1`$. On retained profiles the exponent of the margin correction is bounded by $`O(L)`$, since $`\sum s_j^2\le LM`$. Hence even its weighted exceptional contribution tends to zero. The switching bound on the actual arrays permits discarding all larger profiles with relative error $`o(1)`$, independently of their margin formula. It follows that

$$
a_i=K_i A_i\exp[-1/2+V/(2m(1-p))+o(1)]=K_i A_i(1+o(1)).
$$

The tilt formula gives $`A_i=e^{E(i)}(2\pi n V)^{-1/2}(1+o(1))`$, where $`E(x)=n\log H(w_x)-dx\log w_x`$. Here $`V\sim m\to\infty`$. The repository lattice lemma applies at the integer mean with relative error $`O(n^{-1/2})`$. [Repository lattice local limit theorem](https://github.com/ProgramComputer/open-math-research/blob/605cc467a5be93a8408519da331e46f1008df96e/topics/balanced-arrays/dense-regime/uniform-lattice-lemma.md)

On fixed translates of $`k`$, $`E''=-b/V\to-1/\beta`$ and $`|E'''|=O(b(d/n)\sqrt m/V^2)=O(\sqrt b/d)=o(1)`$. Neighboring variances have ratio tending to one. The exact first difference of $`\log K_i`$ is $`-(d-1)/(2i)+O(d/n+d/i^2)`$ by its adjacent product formula, so it contributes $`d/(2k)+o(1)`$ to the signed centered first difference and $`o(1)`$ to log curvature. This proves the first two claims. [Binomial margin increments](https://github.com/ProgramComputer/open-math-research/blob/4fb624ba937a8eecc1361a6066185cd81ab7b172/topics/balanced-arrays/quadratic/quadratic-lower-quota.md)

## Phase drift at the first hitting point

At any crossing of $`k\pi`$, the height-independent phase bound initially gives $`y=n\mu/d=O(d)`$, hence $`\mu=O(b)`$. Use the trial binomial mean $`2(C+1)b`$ when $`\mu\le Cb`$ to conclude that the unconditioned mean is also $`O(b)`$. The truncated row law has raw moments of each fixed positive order $`j`$ bounded by $`C_j\mu(1+b)^{j-1}`$. For example log-concavity of its upper tail gives $`\mathbb E[(S)_j]\le j!\mu^j`$: summing $`\mathbb P(S\ge i_1+\cdots+i_j)\le\prod \mathbb P(S\ge i_m)`$ over positive indices bounds $`\mathbb E\binom Sj`$ by $`\mu^j`$. Also $`\mathbb E G(S)\asymp \mu/d`$ since $`V\le\mu`$. The mean size under the $`G`$-weighted law is therefore $`O(1+b)`$. Centering the radial characteristic and using the third absolute moment gives $`n|\arg H(we^{i\phi})-\mu\phi|=O(n(1+b)^3/d^3)=o(1)`$ since $`b=o(d^{1/3})`$. The determinant argument is $`O((1+b)/d)`$ by the absolute first moments and the characteristic functions being close to one at this angle. Thus $`y=k+O(1+b)=k+o(d)`$ and $`\mu/b\to\beta`$ at every crossing, including the first.

Now $`\mu\asymp b`$, so the preceding uncapped comparison gives $`V\sim\mu`$ and bounded normalized moments. The $`G`$-weighted mean minus $`\mu`$ is

$$
\frac{(d-2\mu)V-\mathbb E(S-\mu)^3}{\mu(d-\mu)-V}\longrightarrow1 .
$$

Expanding the centered characteristic functions of both laws through their linear phase gives $`\arg\lambda_\phi=(1+o(1))\phi+O((1+b)^3\phi^3)=(1+o(1))\phi`$ by the third absolute moments of the two laws; the size-weighted bound follows from the fourth raw moment divided by $`\mu`$. Hence $`y(v_k)=k+1/2+o(1)`$. Integrate $`\frac{\mathrm d}{\mathrm dx}(d\log w_x)=b/V_x\to1/\beta`$ on the resulting bounded interval to get the final log-radius comparison. The geometric and angular nodes consequently have the same strict sign by the Gaussian alternating-sum argument.
