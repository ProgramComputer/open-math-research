# Consecutive excedance interlacing from size 10,000 at bounded ratios

For integers $`n\ge10000`$ and $`3\le k\le n`$ with $`4\le n/k\le48`$, the nonzero roots of the consecutive minimum-cycle-length excedance polynomials at sizes $`n,n+1`$ are simple, negative and strictly interlace. The common root zero is simple. Formal coverage is ⬜ None. [Original claim](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Exact checker](check.py) · [Output](output.txt)

Use the notation and identities of the [degree-block proof](../degree-blocks/README.md). In particular $`S=\sin\theta`$, $`C=\cos\theta`$, $`z_a=(C+iaS)^{-1}`$ and $`A=kS`$. On the middle interval, $`U=6/5\le nS^2`$. Write $`\ell\le n/k\le X`$ for a table interval in the checker and $`K=\lfloor10000/X\rfloor\ge208`$. We estimate both signed insertion vectors $`V_\pm`$ from the degree-block proof.

**Large angles.** If $`A\ge10`$, the degree-block disk proof applies with the same numerator weights, kernels and cycle bounds. For the off-diagonal matrix entry we retain the estimate using $`\rho_a^{r/2}`$, where $`\rho_a=|z_a|`$ and $`r\ge k`$ is the distinguished degree. In the Bernoulli bound on this half power we use exponent 48, since $`r/4\ge52`$. With $`y\le r/n`$ and $`c=yU/192`$ the resulting kernel is $`(1+c(a^2-1))^{-48}`$. Its first moment beyond the odd indices $`\pm63`$ is bounded by $`(1+c(63^2-1))^{-47}/(94c)`$ by monotone integration. For $`\rho_a^r`$ the original exponent 96 still applies. All nine intervals have strict disk margin.

**Small angles.** Suppose $`A\le10`$. The two intervals with $`X\le10`$ already have $`A\ge10`$ from $`A\ge\sqrt{Un}/X`$. In the other seven intervals take $`A_0=\lfloor4\sqrt{12000}/X\rfloor/4\ge9/4`$, a lower bound on $`A`$. Put $`d_\infty=\exp(-\sum_{j=1}^{k-1}1/j)`$ and $`M_1=d_\infty Q_1(z_1^{-1})`$. Retain the full contribution $`M_1z_1^n`$ and its conjugate. The comparison vector is

$$
 U_M=2k\left(\Re(M_1z_1^n),\Re(-iM_1z_1^n)\right).
$$

The goal is to put both $`V_\pm`$ within $`0.97\lVert U_M\rVert_2`$ of $`U_M`$. The bound on the phase of $`M_1`$ below will give the correct integer sample signs even though the direction of $`U_M`$ differs from that used at larger angles.

**The principal residue.** Use $`r_0=\pi/S`$, $`s=r_0 C`$, $`w=s+i\pi`$, and $`H`$ from the [differentiated residue identity](../differentiated-residues/README.md). It gives $`M_1=z_1 e^{-H(w)}/r_0`$ and

$$
 \frac{M'_1}{nM_1}=\frac{z_1}{nS}+\frac{\pi H'(w)}{nS^2}.
$$

We have $`C>0.998`$, $`s>65`$, and $`\theta<1/20`$. Along the segment from $`s`$ to $`w`$, the unimodal gamma-density bound gives $`\pi|H'|\le\pi\exp(A^2/(2kC^2))(1/s+1/\sqrt{2\pi(k-1)})<0.18`$. Indeed $`(k-1)\log(|w|/s)\le A^2/(2kC^2)`$. Thus $`|\arg M_1|<0.23`$, and $`\cos(\arg M_1)>0.97`$. At $`s`$ sum $`1/b`$ for $`b\le5k/(4s)`$. For the remaining terms the Poisson lower tail bound at mean $`bs`$ is at most $`e^{-bs/50}`$ since $`k<4bs/5`$. The sum is at most $`e^{-k/40}/(1-e^{-s/50})<0.01`$. With $`h=\lfloor(2/5)A\rfloor`$ and $`H_h`$ the harmonic number, this proves

$$
 2k|M_1|\ge (2A/\pi)\exp(-H_h-0.19)>0.47.
$$

Here $`5k/(4s)\le(2/5)A`$, and it suffices to check $`0\le h\le4`$ at $`A\ge\max(9/4,5h/2)`$. The normalized derivative of the multiplier has magnitude below $`1/(A_0\ell)+0.18/U`$.

**Coefficient errors at the principal poles.** Define $`\tilde d_r=d_r`$ for $`r\ge k`$ and zero for every other integer, including zero and negative indices. The contribution at $`a=1`$ to the difference between $`F_N`$ and the carrier $`M_1z_1^N`$ is

$$
 \sum_{T\ge0}(\tilde d_{N-T}-d_\infty)z_1^{N-T}[u^T]Q_1(u).
$$

Use $`N=n`$ for the old row or $`N=n+1-k`$ for the residual. The numerator factorial bound and the weighted estimate below give locally uniform absolute convergence also after one angular derivative. For the joint vector the contribution from differentiating $`z_1^{n-T}`$ pairs with its value through a diagonal two-by-two real matrix of norm $`\max(1,|n-T|/n)`$. The same coefficient difference multiplies the term with $`Q_1'`$. Differentiating the carrier itself adds the separate cost $`2k|M'_1|/n`$.

If $`r/k\ge g`$, an upper bound $`e(g)`$ for $`k|\tilde d_r-d_\infty|`$ is $`4/7`$ for $`g<1`$, and $`0.453`$ for $`1\le g<2`$. For $`g\ge2`$ take $`j=\lfloor g\rfloor`$. The cycle bounds give $`4/7-1/2`$ for $`j=2`$ or $`4/7-0.547`$ for $`j\ge3`$. Intersect this bound with $`(j+1)/(2j\,j!)`$, obtained by summing the factorial numerator differences over all blocks beyond $`r`$. The cycle bounds also apply to $`d_\infty`$ by passage to the limit in $`D(u)=e^{-\sum_{i<k,\,i\ge1}u^i/i}/(1-u)`$. The checker may weaken the factorial estimate by capping $`j`$ at 40.

In bin $`b`$ use $`h_b=b/4`$, and let $`Q_b,D_b`$ denote the binned coefficient majorants for $`Q_a,Q_a'/n`$ including $`Q_0=1`$. They are computed by the nonnegative exponential and its marked-factor derivative from the degree-block proof. Through bin 240 the two principal poles incur old and residual errors bounded respectively by

$$
 \begin{aligned}
 p_n&=2\sum_b e(\ell-h_b)\bigl[Q_b\max(1,h_b/\ell-1)+D_b\bigr],\\
 p_m&=2\sum_b e(\ell-1-h_b)Q_b .
 \end{aligned}
$$

For the tails evaluate the degree majorants at $`v=9/8`$, with $`t=v^4`$. The singleton primitive mass is one before applying its lattice weight. For block $`jk<s\le(j+1)k`$ the actual numerator mass is at most $`0.51/j!`$ for $`j\ge1`$. In the first block use the telescoping variation $`k\sum_{k<s<2k}1/(s(s-1))<1/2`$, plus the jump at $`2k`$ of size at most $`1/(4k)`$ in these units. In later blocks there are precisely $`k`$ integers and the factorial pointwise bound applies. Consequently the actual weighted mass is at most $`t+0.51t(e^t-1)<7`$ and its moment with factor $`b/4`$ is at most $`t+0.51t((1+t)e^t-1)<13`$. The lattice suprema for the scalar and first moment are below 4 and 20 on the entire range. Using these full-block masses in the weighted product bound gives $`L(v)<14`$, $`vL'(v)<104`$, and $`J(v)<14`$. Bound the sums of the omitted true product masses and their $`b`$-moments using $`e^{L(v)}v^{-240}`$ and $`vL'(v)e^{L(v)}v^{-240}`$, and use $`J(v)e^{L(v)}v^{-240}`$ for the marked derivative. Since $`e(g)\le4/7`$ and $`\ell\ge10`$, the tail added to either displayed error is less than $`10^{-4}`$.

**Remaining poles and insertion.** Sum the degree-block matrix and residual estimates over $`|a|\ge3`$, using the exponent-48 correction above. Keep the constant bin accounting for single-pole terms. The two principal poles have diagonal mass exactly two in every bin since $`r/n\le1`$; they have zero off-diagonal entry. Denote the resulting errors by $`v_n,z_m`$. Products with total bin index above $`5X`$ cannot contribute to an actual row. The normalized insertion factor $`|B_k|/(nS)`$ is at most $`I=W(U/(192X))/(A_0\ell)`$ with $`W`$ the signed-lattice mass defined in the degree-block proof. Hence, in units of $`2k|M_1|`$, each disk error is strictly below

$$
 \frac{1}{A_0\ell}+\frac{0.18}{U}+I+
     \frac{p_n+v_n+I(p_m+z_m)}{0.47}.
$$

Both $`p`$ bounds here include their infinite tails. The seven small-angle replays put this expression below $`0.97`$ with margin exceeding $`0.324`$. Since the unrotated unit vector $`(\cos(n\theta),-\sin(n\theta))`$ has scalar product $`2k|M_1|\cos(\arg M_1)`$ with $`U_M`$, its scalar product with either $`V_\pm`$ is strictly positive. At an integer phase this fixes the sign of the old value. At an old zero it fixes the signs of both second coordinates, including the one that gives the actual next row. Thus the small- and large-angle comparisons agree on the actual old and new signs even if the angle regime changes within a gap.

The [exterior theorem](../effective-front.md) supplies the first $`\lfloor7\sqrt n/20\rfloor`$ roots at both ends before their first middle samples. The remaining integer-phase gaps, their reciprocal images and the central root for odd $`n`$ exhaust the degree. The actual signs at the old roots alternate, and the two endpoint coefficients give both outer roots in the next row. This proves the claimed consecutive interlacing.

Run the following from this directory with Python 3. The checker imports the earlier degree-block rational lattice and numerator bin bounds.

~~~sh
python3 -I -B check.py
~~~

[Independent review](review.md) · [Independent checker](verify.py) · [Independent output](replay.txt)

**Source check, November 26, 2026.** Alexandersson states consecutive interlacing for the excedance statistic on permutations with all cycles longer than the forbidden lengths. GitHub searches for `"excedance" "minimum cycle length" interlacing` in issues and `"excedance" "Fourier" interlacing` in code returned no matches. A web search by author, statistic, threshold, and interlacing, including indexed X posts, surfaced no competing general proof or proof of these cutoffs. Index coverage of X was limited. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Earlier source checks](../differentiated-residues/literature.md)
