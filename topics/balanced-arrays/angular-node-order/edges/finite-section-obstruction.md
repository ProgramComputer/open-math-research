# An obstruction to a direct finite gamma-mixture analogue

Write $`H(z)=\sum_{s=0}^r\binom ds z^s`$, $`A_j=[z^j]H(z)^n`$, and $`p_k=a(n,k,r,d)/A_{dk}`$. Thus $`p_k`$ is the probability of exact column balance conditional on an array having $`dk`$ ones, when all labeled arrays satisfying the row cap have equal weight. Consider averaging scaled copies of the unshifted section $`\sum_k A_{dk}q^k`$. A positive probability measure on $`[0,1]`$ gives the array polynomial by this procedure precisely when $`p_k=\int t^k\,d\mu(t)`$ throughout its degree range. This is one possible finite-array extension of the [limiting mixture](lower-gamma-mixture.md).

**Obstruction.** Such a representation fails at $`(n,r,d)=(4,3,4)`$. More generally, fix $`1\le r<d`$ with $`2r>d+1`$. It fails for every sufficiently large $`n`$ with $`d\mid nr`$. This concerns the raw coefficients of this particular section. The sign of the array polynomial at an angular radius is a separate question.

## Four columns

There are $`15^4=50{,}625`$ allowed matrices. Their balanced counts in order of increasing quota are $`(1,252,978,24)`$, and their counts at the corresponding total loads are $`(1,1816,10896,256)`$. In particular,

$$
p_3-p_2=\frac{24}{256}-\frac{978}{10896}=\frac{29}{7264}>0.
$$

Every sequence of moments of a positive measure on $`[0,1]`$ is nonincreasing. The counts follow by expanding $`((1+z)^4-z^4)^4`$ for the total loads. For quota two, inclusion-exclusion over full rows gives $`\binom42^4-4\binom31^4+6=978`$. At quota three the missing entries form a permutation matrix. Direct independent enumeration of the four labeled row masks reproduced both count vectors.

## High row caps

Put $`D=nr/d`$ along the stated progression of heights. Give an allowed row mask $`X`$ probability proportional to $`w^{|X|}`$ at fixed $`w>0`$, and write $`S=|X|`$, $`V=\mathrm{Var}(S)`$, $`q_s=s(d-s)/(d(d-1))`$ and $`a=\mathbb E[q_S]`$. Conditioning on total load cancels the tilt. For $`k`$ a nearest integer to $`n\mathbb E[S]/d`$, both the target vector $`(k,\ldots,k)`$ and its total load are a bounded distance from their means in the respective sums of $`n`$ independent rows. The row law contains zero and every unit vector and is aperiodic on $`\mathbb Z^d`$. The size law contains zero and one. The row covariance has eigenvalue $`a`$ on the sum-zero hyperplane, by conditioning on $`S`$, and eigenvalue $`V/d`$ along the all-ones vector. Dividing the two lattice local central limit estimates gives

$$
p_k\sim\sqrt d\thinspace{}(2\pi n a)^{-(d-1)/2}.
$$

At the saturated quota all rows are independent uniform $`r`$-subsets before checking the column sums. Record the first $`d-1`$ indicators of each row. Support differences include all unit vectors by swapping the corresponding element with element $`d`$. Their covariance is $`q_r(I-\mathbf1\mathbf1^\mathsf{T}/d)`$ in these coordinates, so its determinant is $`q_r^{d-1}/d`$. The integrality condition puts the target at the mean. The same lattice estimate gives

$$
p_D\sim\sqrt d\thinspace{}(2\pi n q_r)^{-(d-1)/2}.
$$

For either local estimate, Fourier inversion on the ordinary coordinate lattice has a single maximum modulo $`2\pi`$, since the differences span the lattice. Off a neighborhood of zero the characteristic function has modulus bounded below one. On that neighborhood the centered transform is $`1-\xi^\mathsf{T}\Sigma\xi/2+O(\|\xi\|^3)`$. Scaling by $`\sqrt n`$ and integrating the Gaussian gives $`(2\pi n)^{-h/2}/\sqrt{\det\Sigma}`$ in dimension $`h`$, also for bounded displacements from the mean. [Fixed-dimension lattice estimate](../../fixed-rank-eventual.tex)

Finally $`q_{r-1}-q_r=(2r-d-1)/(d(d-1))>0`$. As $`w`$ increases, the first two terms of the finite row-size sum give

$$
a=q_r+\frac{\binom d{r-1}}{\binom dr}\frac{q_{r-1}-q_r}{w}+O(w^{-2}).
$$

Fix $`w`$ sufficiently large that $`a>q_r`$. Then $`\mathbb E[S]<r`$ and $`k<D`$ for large $`n`$. The two asymptotics give $`p_D/p_k\longrightarrow(a/q_r)^{(d-1)/2}>1`$. This contradicts moment monotonicity.

**Review and scope.** An independent agent-assisted reviewer reconstructed the four-column counts and checked the covariance eigenvalues, lattice spans, local limit constants and strict comparison. Scales outside $`[0,1]`$ and changes of section or coefficient normalization remain possible. Formal verification is ⬜ None.

At dimension nine and cap four an eighth-difference certificate also excludes mixtures over arbitrary nonnegative scales for every sufficiently large height. [Explicit finite bound and proof](positive-scales/README.md)
