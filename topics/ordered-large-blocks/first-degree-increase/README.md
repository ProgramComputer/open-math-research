# Strict interlacing through the first ordered-partition degree increase

**Proposed theorem.** For every threshold $`j\ge2`$, each consecutive pair $`O_{n,j},O_{n+1,j}`$ with a linear old row has simple negative roots and strict oriented interlacing, including the transition from $`n=2j-1`$ to $`2j`$. At equal degrees the new root lies between the old root and zero. At the degree increase the new roots bracket the old root. [Alexandersson’s original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1)

For a uniform ordered set partition of $`[n]`$, choose any fixed nonempty set of marked block sizes. Every binomial moment of the marked count increases strictly with $`n`$ from the first transition at which that moment can be positive. This includes individual block sizes and yields the signed comparison in the linear band. The endpoint correction for the quadratic row has a separate quantitative bound. Formal verification is ⬜ None. [Continuous-age return and its sign obstruction](age-return.md)

## Two unrestricted coefficient growth rates

Define $`A(z)=(2-e^z)^{-1}`$, $`a_n=[z^n]A(z)`$, and $`c_r=[z^r]A(z)^2`$. Then for every $`n\ge r+1`$ and $`r\ge0`$,

$$
\frac{c_{r+1}}{c_r}>\frac{a_{n+1}}{a_n}.
$$

Let $`\lambda=\log2`$ and $`\mu=7/20`$. The normalized expansions are

$$
A_n^{\ast}=2\lambda^{n+1}a_n=1+\epsilon_n,
\qquad C_r^{\ast}=4\lambda^{r+2}c_r=r+1+\lambda+\eta_r,
\qquad |\epsilon_n|\le 14\mu^n,\quad |\eta_r|\le196\mu^r.
$$

Indeed, at $`w=z-\lambda=0`$, $`A=-1/(2w)+1/4+O(w)`$ and $`A^2=1/(4w^2)-1/(4w)+O(1)`$. To bound the analytic remainders on $`|z|=2`$, note that $`\Re w>-3`$, $`|\Im w|\le2`$ and $`|w|>13/10`$. For $`w=a+ib`$, the identity $`|1-e^w|^2=(1-e^a)^2+2e^a(1-\cos b)`$ gives $`|1-e^w|\ge e^{-3}|w|`$. Use $`|1-e^a|\ge e^{-3}|a|`$, $`1-\cos b\ge2b^2/\pi^2`$ and $`4e^3\ge\pi^2`$. Therefore $`|A|<9`$ on the circle since $`e^3<21`$. The pole-subtracted remainders are holomorphic on a disk containing this circle since the poles $`\lambda+2\pi i k`$ with $`k\ne0`$ all have modulus greater than $`2`$. Their suprema are below $`10`$ and $`100`$, respectively. Cauchy bounds the errors after subtracting the pole coefficients, and $`693/1000<\lambda<7/10`$ gives the displayed normalized bounds.

For $`r\ge8`$ the normalized difference $`C_{r+1}^{\ast} A_n^{\ast} - C_r^{\ast} A_{n+1}^{\ast}`$ is $`1`$ plus an error. With $`n\ge r+1`$ its absolute error is at most

$$
14(r+3)\mu^{r+1}+14(r+2)\mu^{r+2}
+196\mu^r(1+14\mu^{r+2})+196\mu^{r+1}(1+14\mu^{r+1}).
$$

All terms decrease for $`r\ge8`$, and their sum at $`r=8`$ is less than $`1/10`$. In particular the normalized difference is larger than $`9/10`$ in this range. For $`r\le7`$, the finitely many $`c_{r+1}/c_r`$ are all above $`3/2`$, computed using $`A'=2A^2-A`$. Every $`a_{n+1}/a_n`$ is at most $`3/2`$. For $`n\le5`$ this follows directly from the coefficient recurrence, and for $`n\ge6`$ the normalized error bound gives

$$
\frac{a_{n+1}}{a_n}\le\frac{1+14\mu^7}{(693/1000)(1-14\mu^6)}<\frac32.
$$

The checker verifies the finite coefficient comparisons and the rational estimates used here. [Exact check](check.py) · [Recorded output](check-output.txt)

## Strict growth of factorial moments

Let $`B(z)=\sum_{s\in S}z^s/s!`$ for the marked sizes $`S\subseteq\{1,2,\ldots\}`$, with least element $`d`$. The ordered sequence of blocks gives the bivariate exponential generating function at mark $`1+u`$ as $`(2-e^z-uB(z))^{-1}`$. Thus

$$
\mathbb E\binom{X_n}{k}=\frac{[z^n]B(z)^k A(z)^{k+1}}{a_n}\qquad (k\ge1).
$$

For $`d_{r,k}=[z^r]A^{k+1}`$, convolve the coefficients of $`A^2`$ with those of $`A^{k-1}`$. For a fixed $`n\ge r+1`$ each $`c_{r-s}`$ in the convolution grows to $`c_{r+1-s}`$ by a strictly larger factor than $`a_n`$ grows to $`a_{n+1}`$, by the preceding bound. The other factor has nonnegative coefficients and constant coefficient one. Therefore $`d_{r+1,k}/d_{r,k}>a_{n+1}/a_n`$. Now convolve once more, with $`B^k`$. Each lag $`\ell`$ in that series is at least $`kd\ge1`$, so $`r=n-\ell`$ always satisfies $`n\ge r+1`$. The same strict comparison proves monotonicity when $`n\ge kd`$ because at least one old term is strictly positive. At $`n=kd-1`$ the moment goes from zero to a positive value. This proves the claimed all-size strict growth, including the case of a single marked size. Equivalently the factorial moments grow by the constant factor $`k!`$ times these binomial moments.

## Actual signs through the first degree increase

Return to the threshold $`j\ge2`$, and write $`q_n=O_{n,j}/n!`$ and $`b_n=\sum_{s=j}^n c_{n-s}/s!`$. For $`j\le n<2j`$, $`q_n(t)=a_n+(t-1)b_n`$, from the mark expansion about $`t=1`$. The unique root $`\xi_n=1-a_n/b_n`$ is strictly negative because the unmarked coefficient is positive. The $`k=1`$ growth theorem says $`b_{n+1}/a_{n+1}>b_n/a_n`$. For $`j\le n\le2j-2`$ this yields $`q_{n+1}(\xi_n)<0`$ and puts its root strictly between $`\xi_n`$ and zero.

For $`N=2j-1`$ and $`X=a_N/b_N`$ the exact new value is

$$
q_{N+1}(1-X)=a_{N+1}-Xb_{N+1}+\frac{X^2}{(j!)^2}.
$$

The quadratic term comes from the two marked blocks of size exactly $`j`$ filling the row. Put $`T=a_{N+1}/a_N`$. The desired sign is equivalent to

$$
b_{N+1}-T b_N>\frac{a_N}{(j!)^2 b_N}.
$$

Each common summand of $`b_{N+1}-Tb_N`$ is positive by the coefficient growth comparison. For $`j\ge9`$, retain just $`s=j`$, with $`r=j-1`$ and $`n=N`$ in that comparison. The margin $`9/10`$ gives

$$
c_j-Tc_{j-1}>\frac{9/10}{4 A_N^{\ast}\lambda^{j+2}}>\frac{1}{5\lambda^{j+2}},
$$

since $`A_N^{\ast}<101/100`$. On the other side $`b_N\ge c_{j-1}/j!`$ and $`C_{j-1}^{\ast}\ge j`$ since $`196\mu^8<693/1000`$. Consequently

$$
\frac{a_N}{j! b_N}\le\frac{a_N}{c_{j-1}}<\frac{202}{100j}\lambda^{1-j}<\frac{1}{5\lambda^{j+2}}.
$$

The last inequality follows from $`5(202/100)(7/10)^3<9\le j`$. Dividing the comparison by $`j!`$ verifies the desired sign. For $`2\le j\le8`$, the checker compares the exact value from this formula with the direct original recurrence at the exact rational old zero. All seven signs are negative. The direct recurrence also certifies the 28 equal-degree pairs at the same thresholds. The quadratic has positive constant and leading coefficients, so the old negative value forces a simple negative new root on each side of the old one. This proves oriented strict consecutive interlacing through the first degree increase at every threshold.

## Reproduction and provenance

Run `python3 -B check.py` beside this note and compare with the recorded output. It uses only the standard library. [Exact checker](check.py) · [Recorded output](check-output.txt) The pole estimates concern the classical unrestricted ordered Bell series. The marked factorial-moment identity is obtained by substituting $`1+u`$ in Alexandersson’s reciprocal generating function. The proof gives a partial sign result for the original unweighted statistic and an all-size moment comparison. The separate continuous-age note records the precise sign obstruction to a pointwise first-return argument.
