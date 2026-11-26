# An obstruction to extending the corank-one determinant

The [corank-one proof](no-full-row.md) realizes a factorially normalized polynomial $T_n$ using a nested unit lower triangular matrix $A$ with nonnegative minors. Expanding $\det(A_n-qU_n)$ along its last row forces
$$
T_n=T_{n-1}+A_{n,n-1}qT_{n-2}+A_{n,n-2}q^2 T_{n-3}+\cdots+A_{n,1}q^{n-1}T_0.
$$
Here $U_n$ is the unit upper shift. Since all $T_j(0)=1$, coefficient comparison uniquely fixes these entries.

**Proposition.** For $U(2,4)$, no fixed real exponent $a\ge0$ makes this construction work with nonnegative entries at every size if $T_n=\sum_k a_{n,k}q^k/(n)_k^a$. This includes the exponent $a=4$ used for the neighboring cap.

The original labeled counts in rows two through four are $(1,6)$, $(1,54)$ and $(1,204,90)$. The forced entries are
$$
A_{4,3}=204/4^a-54/3^a,\qquad
12^a A_{4,2}=90-1224(3/2)^a+324\,2^a .
$$
For $0\le a\le4$, the ratio of the positive terms to the magnitude of the negative term in the latter formula is
$$
\frac9{34}(4/3)^a+\frac5{68}(2/3)^a .
$$
This is convex in $a$. Its endpoint values are $23/68$ and $1172/1377$, both less than one, so $A_{4,2}<0$. At $a=4$, this entry is $-205/4608$.

If $a>4$, write $b_n=a_{n,1}/n^a$ for $n\ge1$. There are at most $n^4$ ways to choose one entry in each of four columns, so $b_n\to0$, whereas $b_2=6/2^a>0$. The linear coefficient gives $A_{n,n-1}=b_n-b_{n-1}$ for $n\ge2$. These entries cannot all be nonnegative.

This excludes a scalar determinant with the specified upper shift, nested triangular matrix and normalization. Real-rootedness of the original $U(2,4)$ rows remains open. The obstruction leaves room for a matrix with additional states tracking rows with exactly one zero. [Published finite coefficient archive](results/source_range.jsonl)
