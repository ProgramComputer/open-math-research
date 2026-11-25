# Eventual real-rootedness of the Eulerian matrix square

Let $A(n,k)$ count permutations of $[n]$ with $k-1$ descents. Mao and Wang conjecture that the row polynomials of the ordinary square $A^2$ have only real nonpositive zeros. [Original paper, §4](https://arxiv.org/abs/2607.01572)

**Theorem.** For all sufficiently large $n$, row $n$ has a simple zero at zero and $n-1$ distinct negative zeros. The threshold is unknown. This gives a finite gap between the theorem and the all-row conjecture. [Proof and range overlaps](eventual.md) · [Manuscript](eventual.pdf) · [LaTeX source](eventual.tex)

The proof counts zeros inside circles until two families of roots approach each other. On the remaining scales a coefficient expansion gives the local quadratic $\xi^2-\Delta^2-1$, whose two real roots stay separated even when $\Delta=0$. The fixed-disk argument, Cauchy limit for logarithmic root magnitudes, consecutive interlacing in each fixed annulus, and extreme-root laws for every fixed power are in the companion paper. [Counting circles](left-cross-sections.md) · [Collision analysis](theta-lower-bridge.md) · [Companion manuscript](paper.pdf) · [Companion source](paper.tex)

**🟨 Partial · Lean 4.** For every matrix power $p$ and cluster index $h\ge1$, Lean verifies the limiting polynomial's coefficient formula and its complete real factorization. The positive root moduli are strictly separated by the factor $(h+1)/h$. The analytic convergence, winding numbers and eventual all-root conclusion have independently reviewed written proofs. [Lean source and checks](lean/README.md)

## Exact computations

All rows $0\le n\le256$ passed exact real-rootedness tests. So did the selected larger rows $384,512,768,1024$. For the extended range an independent verifier reconstructs every coefficient from the alternating Eulerian formula and checks the polynomial's signs at rational separators. At $n=1024$ the signs account for every one of the 1,023 nonzero roots. [Rows 0–125](results/family-rows.jsonl) · [Rows 126–255](results/rows-126-255.jsonl.gz) · [Seven larger certificates including 256 and 1024](results/large-rows.jsonl.gz) · [Independent verifier](verify.py)

From the repository root, with Python 3.10 or later and python-flint 0.9.0, run

~~~sh
python -I -O topics/eulerian-matrix-square/verify.py --initial
python -I -O topics/eulerian-matrix-square/verify.py
python -I -O topics/eulerian-matrix-square/verify.py --interval 126 255 --archive topics/eulerian-matrix-square/results/rows-126-255.jsonl.gz
~~~
