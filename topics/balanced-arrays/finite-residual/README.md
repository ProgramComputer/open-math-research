# Balanced arrays through 35 rows

For every $0\le n\le35$, $d\ge2$ and $1\le r\le d$, the polynomial counting labeled binary $n\times d$ arrays with row sums at most $r$, by their common column sum, has its full degree $\lfloor nr/d\rfloor$ of simple negative zeros. Constants have no zeros. For $d=1$, the polynomial is $(1+q)^n$. This finite computer-assisted result has no checked Lean or Rocq proof. [Alexandersson’s original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

The replay extends the earlier universal check through $n=24$. For each $25\le n\le35$, the ledger records all $1\le r\le d<n$ with $d\ge2$ and one analytic record for the infinite dimension tail $d\ge n$. In that tail the orientation bound on each internal coefficient ratio is at least $(1+1/n)^{2n}>4$, so strict coefficient separation gives simple negative roots. The finite ledger contains 4,829 triples. [Previous finite proof and replay](https://github.com/ProgramComputer/open-math-research/blob/ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2/topics/balanced-arrays/finite-linear-reduction.md) · [Orientation proof and separation criterion](https://github.com/ProgramComputer/open-math-research/blob/ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2/topics/balanced-arrays/orientation-normalization.md)

| Method | Finite triples |
| --- | ---: |
| Rank one, full cap, corank one, or four columns with cap two | 924 |
| Degree at most fourteen | 1,913 |
| Exact orientation separation | 1,821 |
| Inherited coefficient vectors and fresh exact Sturm counts | 4 |
| Fresh coefficient vectors and exact Sturm counts | 167 |

The first row count requiring fresh coefficient checks was $n=25$. The five triples there have $(r,d)=(3,5),(4,6),(5,7),(5,8),(6,8)$. Every directly checked polynomial has positive coefficients and as many distinct real zeros as its degree, so all of its roots are simple and negative. The compressed [ledger](records.jsonl.gz) records each method and, when used, the full coefficient vector and rational Sturm report. The [manifest](summary.json) gives per-row counts, source revision, and hashes. [Rank-one and full-cap criteria](https://github.com/ProgramComputer/open-math-research/blob/ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2/topics/balanced-arrays/finite-linear-reduction.md) · [Corank one](https://github.com/ProgramComputer/open-math-research/blob/ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2/topics/balanced-arrays/no-full-row.md) · [Four columns with cap two](https://github.com/ProgramComputer/open-math-research/blob/ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2/topics/balanced-arrays/four-columns/README.md) · [Degree at most fourteen](https://github.com/ProgramComputer/open-math-research/blob/ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2/topics/balanced-arrays/low-degree.md)

## Replay

Use Python 3, Git, and [python-flint 0.9.0](https://pypi.org/project/python-flint/0.9.0/). The checkout needs the pinned source revision and matching shared root-check and coefficient modules. From the repository root run

~~~sh
python -m pip install python-flint==0.9.0
python topics/balanced-arrays/finite-residual/verify.py --check
~~~

From this topic directory run `python verify.py --check`. The command validates the complete range and separation comparisons, compares inherited vectors to the pinned archives, and recomputes each stored Sturm count. To recompute every fresh coefficient vector using the repository Python implementation, omit `--check` and give an output path. For example, from the repository root

~~~sh
python topics/balanced-arrays/finite-residual/verify.py --start 25 --end 28 --output /tmp/balanced-25-28.jsonl
~~~

The optional [GMP engine](exact.cpp) implements the same labeled-column construction in C++. The two implementations produced byte-identical records for rows 25 through 28. The engine groups rows by remaining capacity, sums the product of binomial choices for each allocation of the next column quota, and clips capacity to the number of remaining columns. From this topic directory, with a C++17 compiler supporting 128-bit unsigned integers, GMP and pkg-config, run

~~~sh
c++ -std=c++17 -O3 exact.cpp $(pkg-config --cflags --libs gmpxx) -o /tmp/balanced-residual-exact
python verify.py --engine /tmp/balanced-residual-exact --output /tmp/balanced-25-35.jsonl
gzip -dc records.jsonl.gz | cmp - /tmp/balanced-25-35.jsonl
~~~

## Independent checks

A second root certificate uses only Python integer arithmetic. For each of the 171 stored polynomials, the signs at zero, at $-2^j$ for $-64\le j\le51$, and at negative infinity give as many sign changes as the degree. Omitting zero evaluations leaves opposite endpoint signs for each counted interval. The intermediate value theorem gives 3,391 distinct negative roots in total. The degree count gives simplicity. [Dyadic sign checker](dyadic_signs.py)

For all 69 directly tested polynomials with $r=d-2$, a separate inclusion–exclusion count over rows with at most one zero reconstructed all 1,575 coefficients. [Independent recount](../code/recount_residual_corank_two.py) · [Counting formula](../code/verify_corank_two_symbol.py)

From the repository root run

~~~sh
python -I -B topics/balanced-arrays/finite-residual/dyadic_signs.py
python -I -B topics/balanced-arrays/code/recount_residual_corank_two.py topics/balanced-arrays/finite-residual/records.jsonl.gz
~~~
