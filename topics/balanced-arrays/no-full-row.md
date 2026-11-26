# All row counts when a full row is forbidden

Fix $d\ge2$. Let $a_{n,k}$ be the number of labeled $n\times d$ binary arrays with $k$ ones in every column and with at least one zero in every row. Write $P_n(q)=\sum_k a_{n,k}q^k$.

**Theorem.** For every $n\ge0$, $P_n$ has its full degree $m_n=\lfloor n(d-1)/d\rfloor$ of distinct negative zeros. The zeros of consecutive rows strictly alternate. If the degree increases, the new row supplies both outer zeros. If the positive degree stays the same, the new row supplies the rightmost zero and the old row supplies the leftmost. Constant rows have no zeros.

This settles the family $U(d-1,d)$ of Alexandersson's balanced-array conjecture, including every $d\ge4$. The cap-one case $d=2$ and the three-column case $d=3$ overlap earlier proofs. For example, row cap two with four columns still lies outside this family. [Alexandersson's statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Author's issue](https://github.com/PerAlexandersson/RealRooted/issues/2005) · [Cap one](finite-linear-reduction.md) · [Three columns](three-column-all-rows.md)

For a nonzero coefficient, the total number $dk$ of ones is at most $n(d-1)$. At $k=m_n$ and $n>0$, set $l=n-k=\lceil n/d\rceil$. Take $dl$ consecutive entries of the periodic list of $n$ row labels and divide them into $d$ consecutive blocks of size $l$. Since $l\le n$, each block has distinct labels. Since $dl\ge n$, every row occurs. Use the labels of each block as the zeros of its column. This verifies the degree. The empty array gives $P_0=1$.

## Inclusion–exclusion and a determinant

Inclusion–exclusion over the forbidden full rows gives
$$
a_{n,k}=\sum_{j=0}^k(-1)^j\binom nj\binom{n-j}{k-j}^{d}.
\tag{1}
$$
Equivalently, complementing all entries gives $d$ subsets of size $n-k$ whose union is the full row set. Define the normalized polynomial
$$
T_n(q)=\sum_{k=0}^n a_{n,k}\left(\frac{(n-k)!}{n!}\right)^d q^k
\quad\text{and}\quad
v_n=(n!)^{d-1}T_n.
$$
Multiplying (1) by $(n-k)!^d/n!$ gives
$$
[q^k]v_n=\sum_{j=0}^k\frac{(-1)^j(n-j)!^{d-1}}{j!\,(k-j)!^d}.
$$
Set $V(z)=\sum_{n\ge0}v_nz^n$ and $W(z)=\sum_{n\ge0}w_nz^n$, where
$$
w_n=(n!)^{d-1}\sum_{l=0}^n\frac{q^l}{(l!)^d}.
$$
The coefficient formula gives $V=e^{-qz}W$. Since $w_0=1$ and $w_n-n^{d-1}w_{n-1}=q^n/n!$ for $n\ge1$, writing $\theta=z\,\partial_z$ gives
$$
W=e^{qz}+z(\theta+1)^{d-1}W,\qquad
V=1+z(\theta+1+qz)^{d-1}V .
\tag{2}
$$
All series here are formal in $z$.

For $n\ge1$, write $D_n=\operatorname{diag}(1,\ldots,n)$, and let $L_n$ and $U_n$ be the matrices with ones on the first subdiagonal and first superdiagonal, respectively, and zeros elsewhere. In the basis $1,z,\ldots,z^{n-1}$, the matrix of $\theta+1+qz$ modulo $z^n$ is $D_n+qL_n$. For $s=d-1$ put $A_n=(D_n+L_n)^s$. Every $(i,j)$ entry of $(D_n+qL_n)^s$ with $i\ge j$ equals $q^{i-j}(A_n)_{ij}$, since each subdiagonal step increases the row index by one. Equation (2) therefore reads
$$
v_n=\sum_{j=1}^n (A_n)_{nj}q^{n-j}v_{j-1}.
\tag{3}
$$

The leading sections of $A_n$ agree with the smaller $A_j$. Expanding the last row of $A_n-qU_n$ gives (3), with the empty determinant equal to one. In the minor for column $j$, the upper-left block is $A_{j-1}-qU_{j-1}$ and the remaining diagonal block is lower triangular with diagonal $-q$. Its sign cancels the cofactor sign. Consequently
$$
v_n=\det(A_n-qU_n).
$$
Factor out $A_n$, whose determinant is $(n!)^s$. Conjugate by a diagonal matrix with alternating signs to change both $L_n$ and $U_n$ to their negatives. This gives
$$
T_n(q)=\det(I+q B_n),\qquad
B_n=C_n U_n,\qquad C_n=(D_n-L_n)^{-s}.
\tag{4}
$$

## The normalized polynomials and their reversals

A matrix is totally nonnegative if all its minors are nonnegative. The inverse of $D_n-L_n$ has entry $(j-1)!/i!$ for $i\ge j$ and zero otherwise, by triangular substitution. It is a positive diagonal scaling of the matrix $J_{ij}=\mathbf 1_{\{i\ge j\}}$. In every square submatrix of $J$, each row is a prefix of ones and the prefix lengths increase weakly. Subtract each preceding row from its successor, working from bottom to top. The resulting rows have disjoint consecutive supports in order, so the minor is either zero or one. Hence $(D_n-L_n)^{-1}$ is totally nonnegative. Every minor of the shift $U_n$ is zero or one. Thus $C_n$ and $B_n$ are totally nonnegative by Cauchy–Binet.

For $\varepsilon>0$, the matrices $C_n(U_n+\varepsilon I)$ are invertible and totally nonnegative. Every entry on the first superdiagonal is positive because $C_n$ has positive diagonal. Every entry on the first subdiagonal is positive because $C_n$ has positive subdiagonal and $\varepsilon>0$. The matrices of successive sizes are nested leading principal sections, since $C_n$ is lower triangular and multiplication by $U_n$ shifts columns one place to the right. The Gantmacher–Krein criterion makes each perturbed matrix oscillatory, with positive eigenvalues strictly interlacing those of its leading principal section. Taking $\varepsilon\downarrow0$ gives a nonnegative real spectrum for $B_n$ and weak adjacent interlacing for
$$
H_n(x)=\det(xI+B_n)=x^n T_n(1/x).
\tag{5}
$$
Here and below roots count with multiplicity. [Gantmacher and Krein, *Oscillation Matrices and Kernels*](https://doi.org/10.1090/chel/345) · [Oscillatory criterion and leading-section interlacing, Theorems 1–2](https://files.ele-math.com/articles/oam-01-18.pdf)

## Return to the original polynomials and strict interlacing

The coefficient map $\mathcal M(\sum_i f_i x^i)=\sum_i f_i x^i/i!$ preserves real-rootedness and makes every nonzero root simple. To see this, for a real-rooted polynomial $F$ of degree $N$ put $f(t)=t^NF(1/t)$. Then
$$
N!\mathcal M(F)(x)=f(\partial_x)x^N.
$$
The polynomial $f$ has nonzero constant term and real roots, so its differential operator factors into real multiples of operators $1+\lambda\partial_x$ with $\lambda\ne0$. On a real-rooted input $g$, each such factor retains an old root of multiplicity $m$ with multiplicity $m-1$. Its other roots solve $g'/g=-1/\lambda$. The logarithmic derivative strictly decreases on every interval between distinct roots, with opposite infinite limits at the two ends. It supplies one simple root in each such gap and one simple root on one of the two outer intervals, the side determined by the sign of $\lambda$. Starting from $x^N$ leaves zero as the only possible multiple root. For a constant $F$, the conclusion is immediate.

By (5) and the real-rooted pencil criterion, every $H_{n+1}+cH_n$ is real-rooted for $c\in\mathbb R$. Applying $\mathcal M$ a total of $d$ times preserves this property. Thus $\mathcal M^d(H_n)$ and $\mathcal M^d(H_{n+1})$ weakly interlace by the same criterion. Any common nonzero root would be a double root of some pencil member, by choosing $c$ to cancel the derivative there. This contradicts the simplicity of every nonzero root of the image of each pencil member. [Obreschkoff's pencil criterion, Theorem 6.1 in Savage and Visontai](https://dmtcs.episciences.org/articles/2321/download)

By definition of $T_n$, the coefficient of $x^i$ in $H_n$ is $a_{n,n-i}(i!/n!)^d$. Consequently
$$
(n!)^d\mathcal M^d(H_n)(x)=x^nP_n(1/x).
$$
The nonzero roots are negative by nonnegative coefficients and simple by the multiplier argument. The zero at the origin has multiplicity $n-m_n$. Removing these zeros from the weak interlacing yields strict interlacing of the remaining roots. When $m_{n+1}=m_n+1$, the reversed new row supplies both extremes. When $m_{n+1}=m_n>0$, it supplies the leftmost negative zero in the reversed variable and the old row supplies the rightmost. Taking reciprocals reverses both orders and gives the stated orientation in $q$.

## Prior overlap and exact checks

The same empty-intersection inclusion–exclusion was previously used to screen the $r=d-1$ family in an independent public investigation. It reported exact Newton-inequality checks for $3\le d\le20$ and $2\le n\le100$ and left the root problem open. The repository's eventual theorem already covers each fixed $r=d-1,d$ at sufficiently large $n$. The determinant and multiplier argument above gives the conclusion at every row count for this family. [Independent inclusion–exclusion investigation](https://github.com/1337isnot1337/solved-conjectures/issues/165#issuecomment-7058747753) · [Earlier eventual theorem](fixed-rank-eventual.pdf) · [Search record](no-full-row-literature.md)

A fresh independent referee reviewed the original conjecture and an anonymized proof, checked the determinant and both interlacing orientations, and found no gap in the restricted theorem. The finite replay uses an independent column-intersection count and integer determinants for $2\le d\le12$ and $0\le n\le24$. It checks 275 rows, 3,575 determinant values and 242 adjacent pairs with a nonconstant old row. [Independent referee report](review-no-full-row.md) · [Exact replay](verify_corank_one.py) · [Archive](results/corank-one.jsonl.gz)

Run the checker from the repository root with Python and python-flint 0.9.0.

~~~sh
python -I -B topics/balanced-arrays/verify_corank_one.py
~~~

Each determinant and its expected polynomial have degree at most $n$, so the $n+1$ distinct integer samples suffice for exact equality. Signed Euclidean chains check the original root counts and strict orientation. The arguments above prove the result for every row count. **🟨 Partial · Lean 4.** The theorem `BalancedNoFullRowCounting.array_inclusion_exclusion` proves (1) from the finite set of labeled Boolean matrices, at every admissible size and dimension. The determinant, spectral interlacing and multiplier arguments are written. [Formal statement](lean/BalancedNoFullRowCounting.lean) · [Kernel audit](lean/corank-one-count-kernel.txt) · [Build instructions](lean/README.md#arrays-with-no-full-row)

[Manuscript](no-full-row.pdf) · [LaTeX source](no-full-row.tex) · [Why the same scalar method fails at the next cap](scalar-normalization-obstruction.md)
