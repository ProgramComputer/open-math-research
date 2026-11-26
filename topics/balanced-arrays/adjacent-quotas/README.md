# Simple negative zeros at an explicit linear dimension bound

**Theorem.** Let $`n\ge10^{200}`$, let $`200d\ge59n`$, and let $`1\le r\le d`$. For each $`k`$ let $`a_k`$ count the labeled $`n\times d`$ binary matrices with all column sums $`k`$ and all row sums at most $`r`$. The polynomial $`\sum_{k=0}^D a_k q^k`$ has $`D=\lfloor nr/d\rfloor`$ simple negative zeros. Every row cap is allowed. The theorem gives a numerical height cutoff in part of the range covered by the qualitative eventual theorem. The full conjecture remains open. [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Eventual theorem in every dimension](../eventual-all/README.md)

**Formal verification**　⬜ None. The argument is a written proof. The rational calculations in the proof can be replayed with Python 3. [Manuscript](paper.pdf) · [TeX source](paper.tex)

## Proof

The coefficients are positive through $`D`$. For example, fill the $`dk`$ column positions successively, using consecutive blocks of $`k`$ residues modulo $`n`$ as the row labels of each column. Every row then has at most $`\lceil dk/n\rceil\le r`$ cells. For $`D\le1`$ the assertion follows at once. Write $`\Gamma_k=a_k^2/(a_{k-1}a_{k+1})`$ for $`1\le k<D`$. By the orientation inequality the normalized sequence $`a_k/\binom nk^d`$ is log-concave, so

$$
\log\Gamma_k\ge d\log\left[(1+1/k)(1+1/(n-k))\right]\ge4d/(n+2).
$$

The last inequality follows from $`\log(1+1/u)\ge1/(u+1)`$ and convexity of the reciprocal. For $`d\ge n`$ this gives $`\Gamma_k>4`$ at every internal index. For $`59n/200\le d\le n`$ it gives $`\Gamma_k>3.2`$. Call an index difficult if $`\Gamma_k\le4`$. Such an index lies in $`.305n<k<.695n`$, by retaining both individual reciprocal bounds. Consequently the two feasible edges from $`k-1`$ to $`k+1`$ lie in the density interval $`[.30,.70]`$. [Orientation proof](../orientation-normalization.md) · [Localization and constants](scalar.md)

Let $`U_j`$ be the number of arrays with the row cap and $`dj`$ ones in total, and $`Q_j=a_j/U_j`$. Put $`x_j=j/n`$ and $`L_j=(2\pi n x_j(1-x_j))^{-(d-1)/2}`$. The adjacent-quota estimate gives, for consecutive feasible indices in that density interval,

$$
\left|\log\frac{Q_{j+1}}{\sqrt d\thinspace{}L_{j+1}}-\log\frac{Q_j}{\sqrt d\thinspace{}L_j}\right|<10^{-6}.
$$

The Gaussian expansion for fixed row sums controls the leading factor even when both the number of rows and the number of columns vary. A monotone coupling then compares consecutive total sums before the equal-column condition is imposed. Conditioning on two actual rows bounds the contribution of irregular profiles after that condition is imposed. [Fixed-profile estimate](fixed-profile.md) · [Coupling and averaging proof](comparison.md)

At a difficult index, the two immediate comparisons give

$$
\log\frac{U_k^2}{U_{k-1}U_{k+1}}\le\log4+2\cdot10^{-6}+50/n<1.4 .
$$

Here the contribution of $`\log L`$ has absolute value at most $`50/n`$ by its second derivative. Write $`e=nr-dk`$, $`h=e/d\ge1`$. We give the scalar lower bound needed to locate the difficult indices away from the upper end of the support. Put $`b_s=\binom d{r-s}`$ for $`0\le s\le r`$, extend it by zero, and put $`C_{m,u}=[z^u](\sum b_s z^s)^m`$. Thus $`C_{n,e}=U_k`$. Under masses proportional to $`(s+1)b_s C_{n-1,e-s}`$ the expectation of $`b_{s+1}/b_s`$ is $`(e+1)C_{n,e+1}/((n+e)C_{n,e})`$, by symmetry and differentiation. As $`e`$ increases, this distribution moves upwards in likelihood-ratio order by log-concavity of the convolution $`C_{n-1,\cdot}`$. The adjacent ratio $`b_{s+1}/b_s`$ decreases, so $`C_{n,e}/\binom{n+e-1}e`$ is log-concave. The mass supports are intervals, and a zero at $`s=r+1`$ includes the last adjacent ratio. [Full scalar normalization proof and literature](https://github.com/ProgramComputer/open-math-research/blob/8a0a986e6baeed69b30de189e75c02fd2c8cb955/topics/balanced-arrays/deficit-curvature/scalar.md)

For the $`d`$-step curvature the binomial factor alone consequently gives a log lower bound of

$$
\sum_{i=1}^d\int_0^d\frac{n-1}{(e-d+i+t)(n+e-d+i-1+t)}\thinspace{}dt
\ \ge\ \frac{d(n-1)}{n+e+d-1}\log(1+1/h)
\ \ge\ \frac{n-1}{(h+1)(h+5)} .
$$

The last estimate uses $`n/d\le4`$. At $`h\le .84\sqrt n`$ the last quantity exceeds $`1.4`$ for $`n\ge10^{200}`$. Therefore $`h>.84\sqrt n`$ at every difficult index. This gives room for three further quotas on both sides using the lower density bound on $`k`$. All four edges from $`k-2`$ through $`k+2`$ now obey the adjacent-quota estimate. The scalar local limit estimate and the variance bound for the tilted row size give $`\Gamma_{k\pm1}\le1.001\Gamma_k`$. [Proof of neighboring curvature control](scalar.md)

Finally take the geometric nodes $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$. Strict log-concavity gives $`0<t_1<\cdots<t_{D-1}`$. At $`-t_k`$ the two first neighbors have relative magnitude $`1/\sqrt{\Gamma_k}`$. On either side the successive magnitudes decrease outwards, so the alternating remainders after the first neighbors are nonnegative. This gives the sign $`(-1)^k`$ when $`\Gamma_k>4`$. When $`\Gamma_k\le4`$, retain the second and third neighbors on both sides. The resulting signed value, divided by $`a_k t_k^k`$, is at least

$$
1-2/\sqrt{\Gamma_k}+1.88/\Gamma_k^2>0,
$$

by the neighbor bound and $`\Gamma_k>3.2`$. At zero the sign is positive, and sufficiently far to the left the sign is $`(-1)^D`$. Thus $`D`$ disjoint open negative intervals each contain a zero. Degree $`D`$ gives simplicity. [Alternating-tail bounds](scalar.md)

## Verification and sources

Run `python3 -B scalar-constants.py` in this directory to replay the rational comparisons for the scalar local limit estimate, localization, height cutoff and sign compensation. The code checks finite numerical bounds used by the proof. [Gaussian and coupling review](review-comparison.md) · [Scalar and root-count review](independent-review-scalar.md)

The general dense margin asymptotics of Canfield, Greenhill and McKay describe binary matrices with prescribed row and column sums. The earlier eventual result in this repository already covers every dimension at an unspecified height. The contribution here is the explicit height cutoff and the effective comparison of adjacent balancing probabilities. On 26 November 2026 we checked the original SymCat entry, GitHub issue search for “balanced arrays” and “real-rooted”, and public web results for explicit dense binary matrix margins and for those terms on X. The X search was limited to public indexing. No separate resolution of the full original conjecture was identified in these checks. [Primary dense-enumeration paper](https://doi.org/10.1016/j.jcta.2007.03.009) · [Research and earlier source checks](https://github.com/ProgramComputer/open-math-research/issues/2)
