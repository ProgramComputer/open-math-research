# Zeros of the Eulerian matrix square

Let $A(n,k)$ count permutations of $[n]$ with $k-1$ descents. Mao and Wang ask whether every row polynomial of the ordinary square $A^2$ has only real zeros. For $n\ge1$ there is always a simple zero at zero. The general conjecture remains open. [Original question](https://arxiv.org/abs/2607.01572)

**Theorem.** In every fixed closed disk centered at the origin, all nonzero zeros of sufficiently large rows are simple and negative. Consecutive rows interlace in every fixed annulus. At least $n-O(n^{2/3})$ zeros of the full row are simple and negative, and their logarithmic moduli have a limiting Cauchy distribution with scale $\pi$. The manuscript also gives the positions of the extreme zeros at either end. [Manuscript](paper.pdf) · [LaTeX source](paper.tex) · [Closed unit disk](right-half.md) · [Compact annuli](compact-annuli.md)

The largest-modulus roots occur in pairs on distinct exponential scales. A fixed higher matrix power has as many roots in each such cluster as the power. Their limiting positions are given by an explicit polynomial. The paper cites earlier extreme-zero formulas and the limiting distribution for individual Eulerian polynomials. The square results have received independent review within this project. [Clusters for fixed powers](matrix-powers.md) · [Prior work and endpoints](endpoint-asymptotics.md#prior-work-checked)

**🟨 Partial · Lean 4.** Lean verifies the strict spacing, exact real root multiset and factorization in the polynomial insertion step for the limiting clusters. The asymptotic estimates and root counts for the Eulerian matrix square have written proofs. [Lean scope and build instructions](lean/README.md)

At $n=128,192,256,384,512,768,1024$, an independent verifier reconstructs every coefficient from the alternating Eulerian formula and checks exact signs at dyadic rational separators. At $n=1024$ these signs account for all 1,023 nonzero roots. To replay the certificates, install python-flint 0.9.0 and run the following command from the repository root. [Verifier](verify.py) · [Coefficient vectors and certificates](results/large-rows.jsonl.gz)

~~~sh
python -I -O topics/eulerian-matrix-square/verify.py
~~~
