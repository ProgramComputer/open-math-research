# Ordered large blocks: obstructions to production and PF kernels

November 26, 2026. [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1) · [Alexandersson’s original statement, Set partitions and trees](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#setPartitionsAndTrees).

For fixed $`j\ge2`$, the conjecture asks for real-rootedness and consecutive interlacing of the polynomials $`O_{n,j}(t)`$ counting ordered set partitions with weight $`t`$ per block of size at least $`j`$. Set $`A(x)=\sum_{i=1}^{j-1}x^i/i!`$, $`B(x)=\sum_{i\ge j}x^i/i!`$, $`g=(1-A)^{-1}`$ and $`C=gB`$. Then

$$
\frac{1}{1-A-tB}=\sum_{k\ge0}t^k g C^k,\qquad
R_{n,k}=n![x^n]gC^k.
$$

The decomposition chooses the $`k`$ large blocks and a sequence of small blocks before, between and after them.

## A production matrix on the stated columns cannot exist

An ordinary exponential Riordan array with a unit $`g`$ requires the compositional parameter to have nonzero linear coefficient. Here $`C`$ starts in degree $`j`$. There is a direct obstruction even if a production matrix is allowed without the usual Riordan formulas. Rows zero and one are both $`(1,0,\dots)`$, while row two is $`(2,1,0,\dots)`$ for $`j=2`$ and $`(3,0,\dots)`$ for $`j>2`$. Therefore no fixed right-multiplying matrix can take every row to its successor. The obstruction persists for the factorial-normalized rows. Replacing $`C`$ by its formal $`j`$-th root $`D`$ produces an invertible Riordan array with columns $`gD^m`$, but one then retains only every $`j`$-th column. A proof using that larger array needs to control the transition through the inserted columns.

Even when it exists, a totally nonnegative production matrix does not suffice by itself for rowwise real-rootedness. Take the first row of $`P`$ to be $`(1,1,0,\ldots)`$ and row $`i\ge1`$ to be $`e_{i+1}`$. Its row supports are pairwise disjoint and ordered, so every minor is zero or one. Yet $`e_0P^n`$ has ones in slots zero through $`n`$, giving $`1+t+t^2`$ at $`n=2`$. A proof using total nonnegativity of a lifted matrix would need an additional condition controlling roots or common interlacers.

## Toeplitz minors of the component kernels

The shifted large-block kernel $`j! B(x)/x^j=\sum c_mx^m`$ has $`c_0=1`$ and $`c_m=j!/(j+m)!`$. Its Toeplitz minor with rows $`1,2,3`$ and columns $`0,1,2`$ is

$$
\det\begin{pmatrix}c_1&1&0\cr c_2&c_1&1\cr c_3&c_2&c_1\end{pmatrix}
=c_1^3-2c_1c_2+c_3
=\frac{1-j}{(j+1)^3(j+2)(j+3)}<0 .
$$

Thus the large-block coefficient sequence fails even $`\mathrm{PF}_3`$ for every conjectured threshold. The delay $`x^j`$ merely shifts the index of this minor. For $`j\ge3`$, $`g`$ has initial coefficients $`1,1,3/2`$ and fails $`\mathrm{PF}_2`$ by the contiguous minor $`1-3/2=-1/2`$. For $`j=2`$, $`g=1/(1-x)`$ has the usual geometric PF kernel. These computations test the component kernels. The root and interlacing results for the actual marked polynomials are summarized on the [topic landing](README.md).

## The canonical lifted production matrix also fails total nonnegativity for $`j\ge3`$

Set $`D=(j!C)^{1/j}=x+a x^2+b x^3+\cdots`$ and let $`\bar D`$ be its compositional inverse. Define $`V(w)=D'(\bar D(w))`$ and $`Z(w)=(g'/g)(\bar D(w))`$, with coefficients $`V_m,Z_m`$ taken to be zero at negative indices. Differentiating $`gD^k/k!`$ and changing variables to $`w=D(x)`$ shows that the lifted production entry divided by the positive factor $`\ell!/k!`$ is $`\widetilde P_{\ell,k}=Z_{\ell-k}+k V_{\ell-k+1}`$. Also $`V_0=1,\ V_1=2a,\ V_2=3b-2a^2`$.

For $`j\ge3`$, write $`j!C/x^j=1+m_1x+m_2x^2+\cdots`$, where

$$
m_1=1+\frac1{j+1},\qquad
m_2=\frac32+\frac1{j+1}+\frac1{(j+1)(j+2)}.
$$

The expansion of $`D/x`$ gives $`b>2a^2`$ exactly when $`m_2>(j+3)m_1^2/(2j)`$. For $`j=3`$ these sides are $`9/5`$ and $`25/16`$. For $`j\ge4`$ the right side is at most $`(7/8)(6/5)^2=63/50<3/2`$. Therefore $`V_1^2-V_0V_2<0`$. The minor of $`\widetilde P`$ with rows $`k,k+1`$ and columns $`k,k+1`$ is quadratic in $`k`$, with this negative leading coefficient, so is negative for all sufficiently large $`k`$. This is an obstruction to total nonnegativity even after filling in the missing columns via the canonical root lift.
