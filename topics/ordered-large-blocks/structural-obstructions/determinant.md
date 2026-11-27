# The canonical renewal determinant and its reduced matrix

**Verdict.** The original unit-weight rows have a canonical determinant and an exact finite-dimensional resolvent, including a rank-$`d`$ quotient for old degree $`d`$. Their natural matrix pencils are indefinite in a precise sense. This rules out obtaining all-size interlacing directly from definite principal-minor interlacing or from a totally nonnegative renewal core. A signed comparison on the reduced matrices remains open.

Write $`q_{n,j}=O_{n,j}/n!`$, let $`A(z)=\sum_{1\le m\lt j}z^m/m!`$ and $`B(z)=\sum_{m\ge j}z^m/m!`$, and put $`g=(1-A)^{-1}`$, $`C=gB`$. The rows are $`q_{n,j}=[z^n]g/(1-tC)`$. I used the repository's prior production obstructions, finite-alphabet normalized-state analysis and continuous-age return as inputs. The determinant representation itself is the classical reciprocal Toeplitz–Hessenberg identity. [Alexandersson's statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Classical determinant formula](https://combinatorialpress.com/ojac-articles/issue-19-2024/toeplitz-hessenberg-determinant-formulas-for-the-sequence-f_n-1/) · [Production obstructions](https://github.com/ProgramComputer/open-math-research/blob/research/topics/ordered-large-blocks/production-obstructions.md) · [Finite-alphabet states](https://github.com/ProgramComputer/open-math-research/tree/research/topics/ordered-large-blocks/finite-alphabet-states) · [Age return](https://github.com/ProgramComputer/open-math-research/blob/research/topics/ordered-large-blocks/first-degree-increase/age-return.md)

## Why the canonical pencil cannot be made definite

Let $`N`$ be the $`n`$-dimensional lower shift, and $`T_n(t)=A(N)/N+tB(N)/N-N^{\mathsf T}`$, where a quotient by $`N`$ means evaluating the formal quotient by $`z`$ at $`N`$. Expansion down the first column, including the triangular top blocks made by the superdiagonal $`-1`$, gives the renewal recurrence for $`\det T_n=q_{n,j}`$. The matrices are nested leading principal submatrices. Put $`U=T_n(0)`$ and $`V=(B/z)(N)`$.

The rank of $`V`$ is $`n-j+1`$ when $`n\ge j`$: it is $`N^{j-1}`$ times an invertible triangular factor. The determinant has degree $`d=\lfloor n/j\rfloor`$, by choosing $`d`$ blocks of exact length $`j`$ and filling the remaining labels with singletons. For every $`n\gt j`$ we have $`n-j+1\gt d`$. Suppose constant invertible left and right multipliers made this pencil symmetric with a definite value at some real parameter $`a`$. Up to an overall sign let that value be $`D\gt 0`$ and write the transformed coefficient as $`W=W^{\mathsf T}`$. The determinant of $`D+(t-a)W`$ has degree $`\operatorname{rank}W`$, by diagonalizing $`D^{-1/2}WD^{-1/2}`$. Both determinant degree and coefficient rank are invariant under the two constant multipliers, contradiction. This excludes all such equivalences regardless of the point of definiteness, for this specific pencil.

## An exact reduced resolvent with a natural indefinite metric

Let $`u=g(N)e_1`$, $`w^{\mathsf T}=e_1^{\mathsf T}U^{-1}V`$, and $`K=U^{-1}V`$. Multiplying $`U x=V y`$ by $`N`$ gives $`(1-A(N))x=e_1x_1-B(N)y`$. Therefore

$$
K=u w^{\mathsf T}-C(N).
$$

The first row of $`U^{-1}`$ has entries $`g_{n-r}/g_n`$ in column $`r`$, with $`g_m=[z^m]g`$. To verify it, multiply this proposed row by $`U`$ and use $`(1-A)g=1`$ in every column. Thus $`w_r=C_{n-r+1}/g_n\ge0`$. The rank-one determinant lemma gives

$$
q_{n,j}(t)/g_n=\det(I+tK)=1+t w^{\mathsf T}(I-tC(N))^{-1}u.
$$

The Krylov vectors $`u_i=C(N)^iu`$ have distinct leading indices $`1+ij`$ while nonzero. For $`0\le i\lt d`$, $`Ku_i=\mu_i u_0-u_{i+1}`$ where $`\mu_i=[t^{i+1}]q_{n,j}/g_n`$. The vector $`u_d`$ is either zero or is killed by $`K`$. Hence their span modulo the possible line $`\mathbb Ru_d`$ is an explicit $`d`$-dimensional invariant quotient. The induced matrix has first row $`(\mu_0,\ldots,\mu_{d-1})`$ and subdiagonal $`-1`$. On the quotient of the full ambient space by the span of the $`u_i`$, the matrix acts as $`-C(N)`$ and is nilpotent.

If $`J`$ reverses coordinates, the natural symmetric metric is $`M=JV`$. Indeed $`VC(N)`$ is lower triangular Toeplitz, so $`JVC(N)`$ is symmetric. Also $`Mu=g_nw`$, so both terms of $`MK`$ are symmetric. The Gram matrix on the Krylov quotient is exact:

$$
u_a^{\mathsf T}M u_b=[z^{n-1}]g^2(B/z)C^{a+b}=[t^{a+b+1}]q_{n,j}.
$$

Its coefficients vanish past the anti-diagonal and are strictly positive on the anti-diagonal. It has inertia $`(\lceil d/2\rceil,\lfloor d/2\rfloor)`$: scale all entries strictly before the anti-diagonal continuously to zero, leaving the determinant nonzero, then diagonalize the coordinate reversal. It is therefore indefinite whenever $`d\ge2`$. The same argument gives inertia $`(\lceil(n-j+1)/2\rceil,\lfloor(n-j+1)/2\rfloor,j-1)`$ for $`M`$ itself, counting positive, negative and zero directions. This natural quotient does not supply a definite compression.

There is a direct total-nonnegativity obstruction for the actual combined core, as well as the previously documented failures for its individual factors. For $`j\ge3`$ the first coefficients of $`j!C/z^j`$ are

$$
1,\quad m_1=1+\frac1{j+1},\quad
m_2=\frac32+\frac1{j+1}+\frac1{(j+1)(j+2)}.
$$

The contiguous Toeplitz minor $`m_1^2-m_2=-1/2+1/(j+1)+1/((j+1)^2(j+2))`$ is strictly negative for every such $`j`$. The same minor occurs in $`C(N)`$ as soon as $`n\ge j+3`$, using zero-based row indices $`j+1,j+2`$ and column indices $`0,1`$. Thus nonnegative entries of the resolvent factors do not extend to total nonnegativity of the nilpotent core.

## Residues and the remaining signed comparison

At a real zero $`\xi`$ of $`q_{n,j}`$ the right null vector of $`T_n(\xi)`$ is $`v=(q_{0,j}(\xi),\ldots,q_{n-1,j}(\xi))^{\mathsf T}`$. The first $`n-1`$ equations solve uniquely from the first coordinate. The left null vector is $`Jv`$ because $`JT_n`$ is symmetric. The corner cofactor gives $`(\mathrm{adj}\,T_n)_{1,n}=1`$, so $`\mathrm{adj}\,T_n=v v^{\mathsf T}J`$ there. The derivative at this zero is exactly $`v^{\mathsf T}JVv`$. The next row evaluates to the last-row border applied to $`v`$. For simple old roots the required Pick sign of $`q_{n+1,j}/q_{n,j}`$ is therefore the strict negativity of that border value divided by $`v^{\mathsf T}JVv`$. This uses the original rows, but the Gram inertia shows why a definite quadratic-form argument cannot establish it directly.

There is also an exact obstacle to interpreting the renewal sum for the next/old ratio term by term as a sum of Pick functions. A real rational Pick function that is $`O(t^{-2})`$ at infinity is zero. Its possible simple real poles have nonpositive residues and their sum is the $`1/t`$ coefficient, so vanishing forces all of them to disappear. For old degree $`d\ge3`$, any nonempty group consisting only of marked lags whose earlier sizes satisfy $`n+1-r\lt (d-2)j`$ gives a nonzero $`O(t^{-2})`$ quotient after multiplying each term by $`t`$. Such groups need genuine cancellation with nearer lags before a Pick-function argument can apply. This is a degree obstruction for every eligible $`n,j`$, independent of any conjectural root orders of earlier rows.

I checked the matrix and Gram identities with exact rational arithmetic on 252 parameter pairs. These checks corroborate the algebra and do not test or extend the range of the original interlacing theorem. The script is [check-determinant.py](check-determinant.py).
