# Real zeros of balanced binary arrays

Fix a column count $d\ge2$ and a row cap $1\le r<d$. Let $a_{n,k}$ count labeled $n\times d$ binary arrays with $k$ ones in each column and at most $r$ ones in each row. Define $P_n(q)=\sum_k a_{n,k}q^k$.

**Theorem.** For every fixed pair $(r,d)$ and all sufficiently large $n$, all $\lfloor nr/d\rfloor$ zeros of $P_n$ are simple and negative. They strictly interlace the zeros of $P_{n+1}$, whose rightmost zero is further right. The proof gives an existential threshold $N(d,r)$. The conjecture for every $n$ remains open. [Proof](fixed-rank-eventual.pdf) · [Manuscript source](fixed-rank-eventual.tex)

The dominant terms in a torus integral come from the two points at which all coordinates have angle $\pi/d$ or all have angle $-\pi/d$. The resulting sign changes locate the central roots. Two limits of the coefficient sequence identify the remaining roots at either end and account for the full degree. The author’s public issue had already described a preliminary eventual argument for $(r,d)=(2,4)$. The manuscript credits this overlap. The project proof has received independent internal review. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs) · [Prior four-column claim](https://github.com/PerAlexandersson/RealRooted/issues/2005)

**🟨 Partial · Lean 4.** Lean checks the fixed-product pair argument in the torus reduction. The diagonal phase comparison, integral estimates and final root count have written proofs. [Exact formal scope](lean/README.md) · [Kernel report](verification.json)

## Reproduce the published finite range

For $r=2$, $4\le d\le12$, and $0\le n\le40$, the verifier recomputes all 369 coefficient vectors from labeled matchings and again from row capacities. It then counts the real roots by an exact square-free Sturm sequence. Each record contains the full coefficient vector and root count. These finite checks and the asymptotic proof have different scopes. [Archive](results/source_range.jsonl) · [Verifier](verify_source_range.py)

From the repository root, using Python 3.10 or later and a virtual environment, run

~~~sh
python -m pip install python-flint==0.9.0
python -I -O topics/balanced-arrays/verify_source_range.py
~~~
