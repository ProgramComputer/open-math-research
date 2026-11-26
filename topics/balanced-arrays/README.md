# Real zeros of balanced binary arrays

For four columns with row cap two, the polynomial has exactly $\lfloor n/2\rfloor$ distinct negative zeros at every row count $n$. The computer-assisted proof covers $0\le n\le532$ by exact finite certificates and $n\ge533$ by a uniform sign argument. Consecutive-row interlacing remains open in this case. **⬜ None** for Lean or Rocq. [Theorem, proof and independent review](four-columns/README.md)

For every $d\ge2$, balanced arrays with row cap $r=d-1$ have $\lfloor n(d-1)/d\rfloor$ simple negative zeros for every row count $n$. Consecutive rows strictly interlace. When the degree stays the same, the new rightmost zero is closer to zero. This settles the entire family $U(d-1,d)$. The general conjecture remains open. [Four-page paper](no-full-row.pdf) · [Proof](no-full-row.md) · [Independent review](review-no-full-row.md) · [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**🟨 Partial · Lean 4.** Lean proves the all-dimension inclusion–exclusion formula directly from the labeled binary matrices. The determinant, spectral argument and strict interlacing have written proofs. The independent referee reviewed the written proof before this Lean theorem was added. A separate exact computation reconstructed 275 rows and checked 242 consecutive nonconstant pairs. [Lean theorem](lean/BalancedNoFullRowCounting.lean) · [Build and axiom audit](lean/README.md#arrays-with-no-full-row) · [Replay](verify_corank_one.py) · [Archive](results/corank-one.jsonl.gz)

[Stable Lean recheck and per-theorem axiom reports](verification.json) · [Reproduce the audit](../../shared/lean/publication/README.md)

The same nested scalar determinant fails for $U(2,4)$ at every nonnegative power of the falling-factorial normalization. [Obstruction at the next cap](scalar-normalization-obstruction.md)

## Eventual interlacing at each fixed rank and dimension

Fix a column count $d\ge2$ and a row cap $1\le r<d$. Let $a_{n,k}$ count labeled $n\times d$ binary arrays with $k$ ones in each column and at most $r$ ones in each row. Define $P_n(q)=\sum_k a_{n,k}q^k$.

**Theorem.** For every fixed pair $(r,d)$ and all sufficiently large $n$, all $\lfloor nr/d\rfloor$ zeros of $P_n$ are simple and negative. They strictly interlace the zeros of $P_{n+1}$, whose rightmost zero is further right. The proof gives an existential threshold $N(d,r)$. The conjecture for every $n$ remains open. [Proof](fixed-rank-eventual.pdf) · [Manuscript source](fixed-rank-eventual.tex)

The dominant terms in a torus integral come from the two points at which all coordinates have angle $\pi/d$ or all have angle $-\pi/d$. The resulting sign changes locate the central roots. Two limits of the coefficient sequence identify the remaining roots at either end and account for the full degree. The author’s public issue had already described a preliminary eventual argument for $(r,d)=(2,4)$. The manuscript credits this overlap. The project proof has received independent internal review. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs) · [Prior four-column claim](https://github.com/PerAlexandersson/RealRooted/issues/2005)

**🟨 Partial · Lean 4.** Lean proves that each connected component of the maximizing set for the balanced-array row polynomial on the fixed-product torus contains a diagonal point. The diagonal phase comparison, integral estimates and final root count have written proofs. [Exact formal scope](lean/README.md) · [Kernel report](verification.json)

## Three columns with row cap two

For every $n\ge0$, the polynomial for $U(2,3)$ has $\lfloor2n/3\rfloor$ distinct negative zeros. The proof uses explicit sign bounds for $n\ge20$ and exact Sturm counts below that cutoff. One binomial normalization gives an algebraic generating function with four branch points. Estimates for its coefficients at selected phases locate all the zeros, and a finite multiplier transfers the result back to the array polynomial. Agent-assisted independent review checked the argument and ran a separate exact calculation through $n=20$, including the overlap row. [Seven-page paper](three-column-all-rows.pdf) · [LaTeX source](three-column-all-rows.tex) · [Proof and review](three-column-all-rows.md) · [Prefix verifier](code/verify_three_column_prefix.py) · [Exact prefix records](results/three_column_prefix.jsonl)

**🟨 Partial · Lean 4.** The three-column module turns strict signs at integer phase levels into an exact count of all $\lfloor2n/3\rfloor$ simple roots of the reflected, once-normalized polynomial. The coefficient formula, analytic estimates, small-row Sturm counts, and multiplier transfer remain at the level of the written proof and exact Python checks. [Formal statement and build instructions](lean/README.md#three-columns-with-row-cap-two) · [Kernel report](verification.json)

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

## Every row has a simple negative zero closest to the origin

When $d\ge2$ and $nr\ge d$, the unique closest zero is $-b_n$. In the next row exactly one zero has modulus at most $b_n$, and it satisfies $0<b_{n+1}<b_n$. This applies to every admissible rank at every nonconstant row. The proof counts decompositions into quota-one layers. Lean checks the disk estimate and its geometric bound. The counting argument and the transfer between rows have independent mathematical review. [Proof](first-root.md) · [Formal scope](lean/README.md) · [Exact verifier](verify_first_root.py)

~~~sh
python -I -O topics/balanced-arrays/verify_first_root.py
~~~
