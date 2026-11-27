# Lean bridge for the paired-residue profile

The [paired-residue middle proof](../../paired-residues/README.md) uses the original fixed-threshold permutation rows for $n\ge10{,}000$ and $4\le n/k\le48$. This package checks supporting exact identities. The quantitative occupied-degree bounds and the resulting middle signs remain open Lean obligations. This package treats values. Angular differentiation remains a separate proof obligation.

Write $x\ge0$, $R\gt0$ and $z_q=R/(x+i(2q+1)\pi)$ for $q\in\mathbb Z$. At cycle size $p\ge2$ the signed Eulerian moment at $t=-\exp(-x)$ contributes

$$
\frac{R^p}{p!}\cdot\mathrm{cycleMoment}(p,x)
=\frac{1}{p}\sum_{q\in\mathbb Z}z_q^p.
$$

The formula includes $x=0$. The coefficient is set to zero below the cutoff. The factorial-scaled anchored recurrence identifies the coefficient of the power of order $h$ of this cycle series with $R^n/n!$ times the ordered $h$-cycle profile. The sum with weights $1/h!$ runs through $\lfloor n/k\rfloor$ and gives the scaled original normalized row. Absolute log-coefficient summability starts at degree two, and summability with one odd-index weight starts at degree three. The truncated exponential coefficients converge along all finite odd-pole subsets. The signed Eulerian Mittag–Leffler formula and literal ordered-cycle expansion are due to Bowen Zuo and imported from the authenticated cutoff-six release. [Supplying Eulerian formula](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/EulerianSeries.lean#L134-L147) · [Original cycle expansion](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleSupports.lean#L328-L357)

For a finite pole set with distinct nonzero denominators $w_q=z_q^{-1}$, let $D$ be a formal series and $B=(D-1)(1-u)$. The checked Lagrange partition gives

$$
\prod_{q\in A}D(u/w_q)-1
=\sum_{a\in A}(D(u/w_a)-1)
\prod_{q\in A\setminus\lbrace a\rbrace}\left(1+\frac{w_q}{w_q-w_a}B(u/w_q)\right).
$$

Each nonempty occupied set contributes once by the Lagrange partition of unity. The coefficient identity uses $w_q-w_a=2i(q-a)\sin\theta$ in angular coordinates. [Finite Lagrange identity](FinitePoleProduct.lean) · [Odd-pole specialization](PairedPoleFamily.lean) · [Literal cycle normalization](RepositoryPairedCycleLift.lean) · [Literal profile and coefficient limit](RepositoryScaledCycleProfile.lean)

The formal cycle factor $D_k(u)=\exp(\sum_{p\ge k}u^p/p)$ converts the coefficient limit into convergence of actual finite products. The exponential addition law uses the finite support of each power-series coefficient in the power indices and the factorial binomial identity. It gives

$$
[u^n]\prod_{q\in A}D_k(z_qu)=\sum_{h=0}^{\lfloor n/k\rfloor}\frac{[u^n](\sum_{q\in A}\sum_{p\ge k}z_q^p u^p/p)^h}{h!}.
$$

The coefficient is one at degree zero and zero at positive degrees below $k$. For $k\ge2$, the product coefficients converge along all finite pole subsets to $R^n\mathrm{normalizedEnumerator}(n,k,x)/n!$ using the signed profile above. [Formal exponential](CutoffFormalExp.lean) · [Finite product](PairedExpProduct.lean) · [Original permutation limit](RepositoryPairedProductLimit.lean)

The finite distinguished-pole sum also converges absolutely over all marked occupied tuples at each positive degree for cutoff at least three. This identifies the full lattice sum with the original normalized permutation row through the finite-product limit. [Occupied-value theorem and proof](occupied-values.md)

Run `python3 -Bu topics/long-cycle-excedances/lean/paired-profile/check.py /path/to/scratch-project` from the repository root with Lean 4.33.1 and its Lake executable on PATH. An optional second argument is the authenticated common-pin import archive. The driver delegates dependency authentication and setup to the [common-pin driver](../common-pin/check.py), then compiles and kernel-replays all nineteen modules and checks their named axiom reports. [Hosted receipt](verification.md) [Finite-product receipt](product-verification.md)
