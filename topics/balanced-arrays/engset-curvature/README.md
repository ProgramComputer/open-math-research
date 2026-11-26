# Carried-load curvature and balanced-array extensions

This package studies two quantities that arise in [Alexandersson’s balanced-array conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays).

- The tilted one-row law has weights proportional to $\binom dj z^j$ for $0\le j\le r<d$. Its saddle correction as a function of carried load satisfies a strict convexity inequality for $r\ge2$. The variance bounds also follow from the classical same-mean convex-order comparisons. [Carried-load proof](carried-load.md) · [Source comparison and review](independent-review.md)
- For actual finite counts $a_k$, the $d$th root of the mean number of simultaneous extensions is $u_k=(k+1)(a_{k+1}/a_k)^{1/d}$. Its strict concavity holds eventually for fixed $d,r$ on compact interior density intervals, at each fixed positive lower quota, and at each fixed distance at least two below saturation. The finite inequality at every center remains a conjecture. [Proof and tested scope](finite-extensions.md)
- A conditional sign argument derives full simple negative roots when $n\ge65{,}536$ and $200d\ge59n$, if the normalized curvatures are nondecreasing from $k-1$ to $k$ at every internal $k$ with raw curvature at most four. The finite extension inequality would imply this monotonicity at the indicated centers. [Conditional reduction](curvature-reduction.md) · [Exact constants](curvature-reduction-check.py)

The Engset source is Azimzadeh and Carpenter, *Operations Research Letters* 44 (2016), 313–318. The proof uses the reciprocal convexity from Theorem 7 in the corrected preprint and changes variables to actual carried load. The two same-mean variance comparisons are applications of the standard convex-order crossing argument. [Version of record](https://doi.org/10.1016/j.orl.2016.02.011) · [Corrected v5, §5](https://arxiv.org/abs/1511.00291v5) · [Karlin–Novikoff](https://doi.org/10.2140/pjm.1963.13.1251) · [Whitt](https://doi.org/10.2307/3213865)

For each fixed dimension, strict extension concavity holds at every genuine internal quota for all sufficiently large row counts, simultaneously over proper caps. The proof includes the moving lower and upper edge regimes. [All-quota theorem and reviews](all-quotas/README.md).

## Exact finite evidence

The pinned-archive screen reads 1,659 distinct coefficient vectors, including full-cap vectors that it skips when testing the inequality. At a dyadic scale of $2^{256}$ it certifies all 14,570 differences tested. The archive revision and per-source names are embedded in the script. A separate inclusion–exclusion screen recomputes 1,914 corank-one vectors for $4\le n\le90$, $3\le d\le24$, and certifies all 75,968 tested differences at scale $2^{192}$. These corpus sizes count separate replays, with possible overlaps. In both runs each scaled value is enclosed within a unit interval by exact integer-root arithmetic. There were no violations or undecided signs in either run.

Run from the repository root. The first two screens use python-flint and the pinned archive screen also uses Git. The constant check uses only the standard library.

~~~sh
python3 -B topics/balanced-arrays/engset-curvature/extension-concavity.py
python3 -B topics/balanced-arrays/engset-curvature/extension-corroboration.py
python3 -B topics/balanced-arrays/engset-curvature/curvature-reduction-check.py
~~~

**⬜ None** for Lean or Rocq. The written proofs, the scope of the Engset input, the fixed-deficit Gaussian factor and the conditional sign reduction received [agent-assisted independent review](independent-review.md).
