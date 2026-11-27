# Exterior signs for all cycle cutoffs at large sizes

Let $E_{n,k}(t)$ count strict excedances of permutations all of whose cycles have length at least $k$. For $n\ge10000$ and $2\le k\le n$, put $H=\lfloor7\sqrt n/20\rfloor$. The Lean theorem `RepositoryQuotientAudit.original_all_aspect_exterior` constructs $H$ strictly increasing positive moduli $f_0,\ldots,f_{H-1}$ with

$$
E_{n,k}(-f_i)=0,\qquad (-1)^{i+2}E_{n+1,k}(-f_i)>0,\qquad
f_i<\exp\left(-\frac{\pi}{\tan((H+1)\pi/n)}\right).
$$

With the checked near-lag bound, the companion window theorem supplies a root in each prescribed open interval about an actual coefficient ratio. The witness theorem applies to every admissible cutoff. The root-list assembly also needs $\lfloor n/2\rfloor-H-1$ ordered middle witnesses with the correct successor signs and the applicable center-sign argument. For $k\ge3$ the repository’s earlier written proof includes exterior signs at all these sizes. This argument gives a shorter bound for the lag and a formal verification of the exterior witnesses. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Prior exterior proof](../../effective-front.md) · [Literal theorem](AllAspectExterior.lean)

## Two binomial grids

Let $V$ be the full insertion lag, $a=kp/n$, $d=k-1$, $m=n-d$, $L=[t^p]V/p^n$ and $\alpha=[t^p]E_{n,k}/p^n$. Consider $1\le p\le\lfloor\sqrt n/2\rfloor$. Write $b_{N,d}(y)=\binom Nd y^d(1-y)^{N-d}$ and $B_{N,d}=\sum_{j=0}^p b_{N,d}(j/p)$. For $2k\le n+1$ we have $m\ge k$. The marked-orbit identity bounds $L$ by a grid whose summands contain the residual acceptance probability on $p-j$ colors. The elementary upper bound one gives $L\le B_{n,d}$.

The second upper bound on the residual acceptance probability is $151m/[100k(p-j)]$ for $j<p$. The zero-color residual vanishes. The identity $(n-d)\binom nd=n\binom{n-1}d$ cancels the factor $1-j/p$ in the binomial mass and gives

$$
aL\le\frac{151}{100}B_{n-1,d}.
$$

This identity treats every grid point in the same sum. [Integer binomial identity and grid comparison](ResidualLagGrid.lean) · [Original residual count](OriginalResidualLag.lean)

For $k\ge151$ the two sizes $N=n,n-1$ both satisfy $2d\le N$ and $d\ge150$. The frozen scaled binomial atom implies a peak at most $29/500$ at either size. The Bernstein integral and the finite mesh inequality now give $B_{N,d}\le 1/200+29/500$. The lower estimate $\alpha(1+8a/3)\ge99/100$, together with the bounds for $L$ and $aL$, gives

$$
\frac{L}{\alpha}\le
\frac{100}{99}\left(1+\frac83\frac{151}{100}\right)
\left(\frac1{200}+\frac{29}{500}\right)
=\frac{2639}{8250}=\frac8{25}-\frac1{8250}.
$$

For $k\le150$ we have $a\le3/4$, so the geometric grid bound gives $L\le1/500$. For $2k>n+1$ the residual has positive size less than $k$, hence the lag vanishes. For the old coefficient lower bound, the orbit cutoff $b=\lceil4a/3\rceil$ only requires $b\le p$ in the marking argument. When $b\ge p$, a permutation consisting of a single cycle on the $p$ colors already gives acceptance probability at least $1/p$. [Scalar comparison](SharpLagBudget.lean) · [Mesh bounds](TwoGridLag.lean) · [Supplying atom](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/BandBinomial.lean#L77-L86) · [Coefficient bounds](../../color-load-bounds/RepositoryColorAlpha.lean)

## Verification

A fresh-context reviewer reconstructed the endpoint cases of the residual grid and the rational margin, and reproduced the four large-row digests using a separate Eulerian recurrence. The root witnesses give existence, ordering and successor signs. Exact ordinal rank and uniqueness inside the intervals require further information. [Independent review](independent-review.md) · [Recurrence-based checker](check-half-recurrence.py)

The integer checker decomposes each permutation with $n<3k$ into a single cycle or an unordered pair of cycles. A cycle of length $r$ contributes $t A_{r-1}(t)$, where $A_s$ is the Eulerian polynomial. It computes the lag from both its cycle factor and the separately enumerated successor. It agreed with literal permutations on 33 complete rows of sizes at most eight. For $(n,k)=(10000,5000),(10001,5001),(10000,5002),(10008,5000)$ it checked every positive rank through 50, including the vanishing-lag and two-cycle transitions. [Exact checker](check-half.py) · [Output and prefix digests](check-half-output.txt)

Lean 4.33.1 checked the two-grid lag bound, the exact coefficient-window tests and their composition with the original permutation rows. The standalone and composed hosted audits replayed their declared Lean modules with the Lean kernel. [Verification receipt](verification.md) · [Root windows and signs](RepositoryAllAspectExterior.lean) · [Verification driver](../front-envelope-sums/check.py)

~~~sh
python3 -I topics/long-cycle-excedances/lean/all-aspect-exterior/check-half.py
python3 -I topics/long-cycle-excedances/lean/front-envelope-sums/check.py /tmp/all-aspect-exterior
~~~
