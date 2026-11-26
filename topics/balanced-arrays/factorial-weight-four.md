# A factorial weighting fails beyond fifteen rows

Take $d=4$, $r=2$, and let $B_n(q)=\sum_k(k!)^3 a_{n,k}q^k$. The cubic factorial is the unique quota-only weight that could realize the growing-first-coefficient scalar determinant in the [method classification](scalar-determinant-boundary.md). In this note $\alpha=0$. The related question with weight $k!$ remains open.

**Proposition.** $B_n$ is real-rooted precisely when $0\le n\le15$. At $n=16$ its ascending coefficient vector is

~~~text
1, 64560, 1473675840, 14190446350080, 56495032283289600,
81630086904317952000, 32476834642181529600000,
1930762399785360261120000, 1820300355657140797440000
~~~

It has eight distinct zeros, six of them real. This is a counterexample to the cubic factorial strengthening. The original polynomial counts the same arrays with weight one per array.

**Proof.** For each $k$ take $k$ distinct tokens of each of four colors. A row using two colors pairs two tokens of different colors. The pairs form a matching of the complete four-partite graph $K_{k,k,k,k}$, with all remaining tokens as singleton blocks. A matching of size $j$ yields $4k-j$ distinct nonempty blocks which can be injected into the row labels in $(n)_{4k-j}$ ways. An array has $(k!)^4$ token labelings. Writing $m_j$ for the number of these matchings gives the polynomial identity in $n$
$$
b_k(n)=[q^k]B_n=\frac1{k!}\sum_j m_j(K_{k,k,k,k})(n)_{4k-j}.
$$
The complete multipartite matching count for rank two also appears in the author's discussion. The cubic factorial question concerns zeros in $q$. [Original conjecture and matching interpretation](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

Put
$$
S_4=b_1^4-4b_1^2b_2+2b_2^2+4b_1b_3-4b_4 .
$$
For $B_n(q)=\prod_i(1+\lambda_iq)$, Newton's identities give $S_4=\sum_i\lambda_i^4$. It must be nonnegative if every zero of $B_n$ is real. The matching formula computes $S_4$ as a polynomial of degree 13 in $n$ with leading coefficient $-64$. Every one of the fourteen coefficients of $S_4(76+t)$ is negative, starting at $-1946127300258102662304000$ and ending with $-64$. The archived first record contains all fourteen and the checker derives them symbolically from the matchings. Hence every $n\ge76$ has a nonreal root.

For $0\le n\le75$ the checker counts the coefficients once by matchings and once by pairing the columns. It computes the square-free degree and an exact signed Euclidean chain for each transformed row. The numbers of nonreal roots are zero through 15, two for $16\le n\le33$, four for $34\le n\le52$, six for $53\le n\le70$, and eight for $71\le n\le75$. Each count is for the full polynomial. The independent reviewer repeated the computation using sorted margins and integer Sturm chains, then recovered the polynomial $S_4$ by classifying the number of occupied rows. [Archive](results/factorial_weight_four.jsonl) · [Independent review](review-scalar-determinant.md)

With python-flint 0.9.0 installed, the following compares every record, including the tail certificate. The reviewer’s alternative uses standard Python.

~~~sh
python -I -B topics/balanced-arrays/code/verify_factorial_weight_boundary.py > /tmp/weighted-four.jsonl
cmp /tmp/weighted-four.jsonl topics/balanced-arrays/results/factorial_weight_four.jsonl
python -I -B topics/balanced-arrays/code/rank-two-review-exact.py
~~~

**⬜ None.** This auxiliary family has a written proof, two exact prefix counts and a symbolic tail certificate. [Primary checker](code/verify_factorial_weight_boundary.py) · [Reviewer’s checker](code/rank-two-review-exact.py)
