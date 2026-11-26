# Simple negative zeros below the row cap

The coefficient of $q^k$ counts labeled binary $n\times d$ arrays with every column sum equal to $k$ and every row sum at most $r$. This comparison addresses a range of Per Alexandersson’s balanced-array conjecture for uniform matroids. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Literature and source record](literature.md)

For $`n\ge10^6`$ and $`n/4\le d\le n/3`$, all but at most $`\lceil n\sqrt{\log(100n)/(2d)}\rceil+4`$ roots are simple and negative at every cap. [Explicit error, exact disk counts and independent checks](finite-aspect/README.md)

**Theorem.** There is an absolute constant $C$ such that for every $2\le d\le n$ and $1\le r\le d$, the number of zeros not certified as simple and strictly negative is at most $CD\sqrt{n\log(n+1)}/d$, where $D=\lfloor nr/d\rfloor$ is the degree. In particular the certified fraction tends to one uniformly over the caps when $D>0$ and $d/\sqrt{n\log(n+1)}\to\infty$. Coefficient separation gives all $D$ roots when $D\le d/2$ or $d>n$.

The [proof](proof.md) compares on disjoint disks of radius $\rho_i/(4n^2)$ about selected negative roots $-\rho_i$ of the unrestricted polynomial. The [root-circle estimate](full-rank-root-stability.md) supplies the spacing and the lower contour bounds. Through any accepted index $i$, the disks contain the first $i$ capped zeros in increasing modulus, and all other zeros have modulus above $\sqrt{\rho_i\rho_{i+1}}$. The theorem leaves their root types and consecutive interlacing open.

The [finite illustration](example/README.md) gives exact sign brackets for $n=7$, $d=14$, $r=12$. It compares the same-index moduli using a separate relative tolerance $1/49$ and includes an optional exact coefficient cross-check against the earlier seven-row archive.

[Manuscript](paper.pdf) · [LaTeX source](paper.tex). Build from this folder with `tectonic paper.tex`.

**⬜ None.** The argument has no checked Lean or Rocq proof. An [independent blind review](review.md) checked the uniform bound, disk localization, and ordering against the original conjecture.
