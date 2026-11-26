# Real zeros of balanced binary arrays

One absolute threshold $N$ gives $\lfloor nr/d\rfloor$ simple negative zeros for every $n\ge N$, $d\ge2$, and $1\le r\le d$. The threshold is ineffective, and the original all-row-count conjecture remains open. **⬜ None** for Lean or Rocq. [Proof and independent reviews](eventual-all/README.md)

Earlier bounds include the [five-thirds row bound and polynomial cap or corank range](fifth-thirds/README.md), [all fixed quadratic aspects](critical-aspect/README.md), the [absolute quadratic cutoff](quadratic/README.md), [quartic-log cutoff](very-tall/README.md), and [dimension-uniform fixed-cap threshold](fixed-cap/README.md).

Every dimension and cap satisfies the conjecture through 35 rows. The exact finite replay includes 171 coefficient vectors and 3,391 simple negative roots certified by integer sign evaluations. [Finite coverage and independent checks](finite-residual/README.md)

There are absolute constants $C>0$ and $N$ such that, for every $n\ge N$, $d\ge Cn/\log n$, and every row cap, the balanced-array polynomial has exactly $\lfloor nr/d\rfloor$ simple negative zeros. This extends the earlier theorem for $d\ge\epsilon n$ with fixed $\epsilon>0$. **⬜ None** for Lean or Rocq. [Theorem and proof](dense-regime/README.md)

For $2\le d\le n$ and every cap, a reviewed comparison with the unrestricted polynomial leaves at most $CD\sqrt{n\log(n+1)}/d$ of the $D=\lfloor nr/d\rfloor$ roots uncertified as simple and negative. It identifies individual roots below the cap by disjoint disks. The logarithmic and below-cap bounds use unspecified absolute constants. **⬜ None** for Lean or Rocq. [Below-cap comparison](dense-regime/below-cap/README.md)

The rank-dependent theorem gives all simple negative zeros for $d\ge C_\varepsilon\sqrt{nr/\log n}$ when $r\le n^{1/5-\varepsilon}$ or $d\ge n^{3/4+\varepsilon}$, for each fixed $0<\varepsilon<1/5$ and all sufficiently large $n$. The constants are existential. **⬜ None** for Lean or Rocq. [Rank-dependent theorem](dense-regime/rank-dependent/README.md)

For four columns with row cap two, the balanced-array polynomial has only simple negative zeros at every row count. The computer-assisted proof combines forty lower sign changes, uniform analytic phase estimates, and exact checks through 532 rows. A blind agent-assisted review checked the full argument against the original conjecture. **⬜ None** for Lean or Rocq. [Four-column theorem and verification](four-columns/README.md)

Fix a column count $d\ge2$ and a row cap $1\le r<d$. Let $a_{n,k}$ count labeled $n\times d$ binary arrays with $k$ ones in each column and at most $r$ ones in each row. Define $P_n(q)=\sum_k a_{n,k}q^k$.

**Theorem.** For every fixed pair $(r,d)$ with $1\le r<d$ and all sufficiently large $n$, all $\lfloor nr/d\rfloor$ zeros of $P_n$ are simple and negative. They strictly interlace the zeros of $P_{n+1}$, whose rightmost zero is further right. The proof gives an existential threshold $N(d,r)$. The all-row conjecture for general caps remains open. [Proof](fixed-rank-eventual.pdf) · [Manuscript source](fixed-rank-eventual.tex)

The dominant terms in a torus integral come from the two points at which all coordinates have angle $\pi/d$ or all have angle $-\pi/d$. The resulting sign changes locate the central roots. Two limits of the coefficient sequence identify the remaining roots at either end and account for the full degree. The author’s public issue had already described a preliminary eventual argument for $(r,d)=(2,4)$. The manuscript credits this overlap. The project proof has received independent internal review. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs) · [Prior four-column claim](https://github.com/PerAlexandersson/RealRooted/issues/2005)

**🟨 Partial · Lean 4.** Lean proves that each connected component of the maximizing set for the balanced-array row polynomial on the fixed-product torus contains a diagonal point. The diagonal phase comparison, integral estimates and final root count have written proofs. [Exact formal scope](lean/README.md) · [Kernel report](verification.json)

[Stable Lean recheck and per-theorem axiom reports](verification.json) · [Reproduce the audit](../../shared/lean/publication/README.md)

## All row counts with row cap one less than the column count

For every $d\ge2$ and $n\ge0$, the balanced-array polynomial for $U(d-1,d)$ has its full degree $\lfloor n(d-1)/d\rfloor$ of distinct negative zeros. Consecutive rows strictly alternate, with the new row supplying the rightmost zero when both rows have zeros. Inclusion–exclusion gives a determinant of totally nonnegative leading matrix sections after a coefficient normalization. A factorial multiplier transfers strict alternation to the original rows. A fresh agent-assisted referee checked the proof against the original conjecture. The exact replay independently verifies 275 rows and 242 adjacent pairs with a nonconstant old row. **🟨 Partial · Lean 4.** Lean checks the coefficient identity from the labeled matrices. The determinant and root arguments remain on paper. [Lean theorem](lean/BalancedNoFullRowCounting.lean) · [Manuscript](no-full-row.pdf) [Proof](no-full-row.md) · [Independent review](review-no-full-row.md) · [Verifier](verify_corank_one.py) · [Exact archive](results/corank-one.jsonl.gz)

## Three columns with row cap two

For every $n\ge0$, the polynomial for $U(2,3)$ has $\lfloor2n/3\rfloor$ distinct negative zeros. The proof uses explicit sign bounds for $n\ge20$ and exact Sturm counts below that cutoff. One binomial normalization gives an algebraic generating function with four branch points. Estimates for its coefficients at selected phases locate all the zeros, and a finite multiplier transfers the result back to the array polynomial. Agent-assisted independent review checked the argument and ran a separate exact calculation through $n=20$, including the overlap row. [Proof and review](three-column-all-rows.md) · [Prefix verifier](code/verify_three_column_prefix.py) · [Exact prefix records](results/three_column_prefix.jsonl)

**🟨 Partial · Lean 4.** The three-column module turns strict signs at integer phase levels into an exact count of all $\lfloor2n/3\rfloor$ simple roots of the reflected, once-normalized polynomial. Lean also derives the coefficient formula directly from labeled arrays at every size and proves the complete root theorem for $0\le n<20$. The analytic phase-sign estimates for larger rows and multiplier transfer have written proofs. [Formal statement and build instructions](lean/README.md#three-columns-with-row-cap-two) · [Kernel report](verification.json)

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

For four columns at row cap two, a Hermite-polynomial expansion reduces the problem to a stronger integer sequence. Two constructions and exact root checks agree in all 121 rows through $n=120$. The all-row proof uses a separate sign argument. [Reduction and replay](four-column-mehler.md) · [Exact scope of the scalar determinant method](scalar-determinant-boundary.md)

At row cap two, every order-two minor comparing two row counts and two componentwise ordered quota vectors is coefficientwise nonnegative in the pair-type weights. This makes the entries of the consecutive Bézout matrices nonnegative. Their higher principal minors are the remaining obstacle in this approach to interlacing. **⬜ None.** [Statement and proof](rank-two-row-minors.md) · [Independent review](review-rank-two-row-minors.md)

Three heavy pair types already obstruct an extension to arbitrary positive row weights on four columns. At five rows a weighted triangle gives a quadratic with negative discriminant. More generally a fractional matching gap forces a violation of log-concavity for sufficiently large weights. The original specialization gives $1+540q+2490q^2$ at five rows. [Proof and exact certificates](triangle-weight-gap.md)

## Four columns with prescribed singleton rows

At row cap two, fixing the singleton count in each column gives simple negative nonzero roots and strict consecutive interlacing after removing the forced power of $q$. The same conclusions hold for exactly two singleton rows with arbitrary positive row weights on singleton and pair types. With uniform weights they also hold for exactly four singleton rows, exactly six singleton rows, and the sum of the two- and four-singleton slices. These results concern the stated slices within the four-column problem. **⬜ None.** The Bessel arguments and root comparisons have an agent-assisted independent written review. [Fixed counts and weighted two-singleton slice](singleton-slices.md) · [Uniform four-singleton slice](four-singletons.md) · [Uniform six-singleton slice](uniform-bessel-comparison.md) · [Sum of the two- and four-singleton slices](paired-singleton-sums.md) · [Independent review](review-bessel-slices.md)

The exact coefficient replay compares labeled row enumeration with the Bessel coefficient formulas. It checks 52 uniform, 27 fixed-count, and nine weighted two-singleton rows. [Verifier](code/verify_singleton_slices.py) · [Exact archive](results/singleton-slices.json)

~~~sh
set -o pipefail
python -I -O topics/balanced-arrays/code/verify_singleton_slices.py | diff -u topics/balanced-arrays/results/singleton-slices.json -
~~~

## A common weight on every pair row

Giving every two-entry row the same positive weight can produce arbitrarily many nonreal conjugate pairs. At 32 rows, weight 216 yields fourteen simple negative roots and one nonreal pair. The original weight 1 gives sixteen simple negative roots. A Bessel expansion identifies the transition at weights of order $n^{5/2}$. **⬜ None.** [Theorem, proof and exact examples](symmetric-pair-weights.md)

## The column-addition multiplier can fail

With seven rows, cap $6t$, and $7t$ columns, adding one column induces a diagonal map whose finite multiplier symbol has a nonreal pair exactly when $t\ge15$. This limits a possible proof method for the conjecture. [Proof, exact records and verification](column-extension-multiplier.md)

## The geometric-center sign test at fixed dimension

At every fixed $d\ge2$ and row cap, the geometric-center signs reverse at asymptotically half of the internal quotas. This limits a sufficient test for real-rootedness. [Obstruction, proof and exact endpoint checks](geometric-centers/README.md)

## Coefficient curvature near the upper quota

An exact screen checked a proposed deficit-dependent curvature inequality at 13,346 internal quotas. The scalar row-deficit model admits a convolution proof without equal-column conditioning. The general bound for balanced arrays remains open. [Screen, analytic checks and scalar proof](deficit-curvature/README.md)
