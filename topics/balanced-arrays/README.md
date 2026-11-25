# Real zeros of balanced binary arrays

Fix a column count $d\ge2$ and a row cap $1\le r<d$. Let $a_{n,k}$ count labeled $n\times d$ binary arrays with $k$ ones in each column and at most $r$ ones in each row. Define $P_n(q)=\sum_k a_{n,k}q^k$.

**Theorem.** For every fixed pair $(r,d)$ and all sufficiently large $n$, all $\lfloor nr/d\rfloor$ zeros of $P_n$ are simple and negative. They strictly interlace the zeros of $P_{n+1}$, whose rightmost zero is further right. The proof gives an existential threshold $N(d,r)$. The conjecture for every $n$ remains open. [Proof](fixed-rank-eventual.pdf) · [Manuscript source](fixed-rank-eventual.tex)

The dominant terms in a torus integral come from the two points at which all coordinates have angle $\pi/d$ or all have angle $-\pi/d$. The resulting sign changes locate the central roots. Two limits of the coefficient sequence identify the remaining roots at either end and account for the full degree. The author’s public issue had already described a preliminary eventual argument for $(r,d)=(2,4)$. The manuscript credits this overlap. The project proof has received independent internal review. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs) · [Prior four-column claim](https://github.com/PerAlexandersson/RealRooted/issues/2005)

**🟨 Partial · Lean 4.** Lean proves that each connected component of the maximizing set for the balanced-array row polynomial on the fixed-product torus contains a diagonal point. The diagonal phase comparison, integral estimates and final root count have written proofs. [Exact formal scope](lean/README.md) · [Kernel report](verification.json)

## A sufficient bound valid at every row count

For every $n\ge1$ and every $1\le r\le d$, the normalized sequence $a_{n,k}/\binom nk^d$ is log-concave. It follows that $P_n$ has simple negative roots whenever $d\ge (n+1)\log(2)/2$, or whenever $d\ge\sqrt{nr\log 4}$. The proof applies Kahn and Neiman’s inequality for orientations of multigraphs to pairs of arrays. This conclusion has an independently reviewed written proof. Its orientation argument has no checked Lean or Rocq proof. [Counting argument and full hypotheses](orientation-normalization.md)

## All dimensions through 24 rows

For $0\le n\le24$, the original conjecture holds for every $d$ and $r$. For $d\ge2$ the zeros are simple. A finite reduction leaves 130 polynomials requiring coefficient counts and exact root tests. This computer-assisted theorem has no checked Lean or Rocq proof. [Proof and reproducible finite certificates](finite-linear-reduction.md)

## All degrees through fourteen

For every row count, dimension and rank, the conjecture holds whenever the polynomial has degree $\lfloor nr/d\rfloor\le14$. For $d\ge2$ its zeros are simple and negative. For $d=1$ the polynomial is $(1+q)^n$. The standalone Python verifier independently reconstructs all 388 polynomials remaining after coefficient separation. This computer-assisted theorem has no checked Lean or Rocq proof. [Proof and reproduction](low-degree.md) · [Finite archive](results/degree_reduction.jsonl)

## Reproduce the published finite range

For $r=2$, $4\le d\le12$, and $0\le n\le40$, the verifier recomputes all 369 coefficient vectors from labeled matchings and again from row capacities. It then counts the real roots by an exact square-free Sturm sequence. Each record contains the full coefficient vector and root count. These finite checks and the asymptotic proof have different scopes. [Archive](results/source_range.jsonl) · [Verifier](verify_source_range.py)

From the repository root, using Python 3.10 or later and a virtual environment, run

~~~sh
python -m pip install python-flint==0.9.0
python -I -O topics/balanced-arrays/verify_source_range.py
~~~
