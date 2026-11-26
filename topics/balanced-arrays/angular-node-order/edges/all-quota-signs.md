# Signs at every internal angular node in fixed dimension

Fix $`d\ge2`$ and $`1\le r<d`$. Let $`P_n`$ be the balanced-array polynomial, $`D=\lfloor nr/d\rfloor`$, and $`w_{n,k}`$ the unique positive solution of $`\Psi_n(w)=k\pi`$ for $`1\le k<D`$ and $`n\ge d`$.

**Theorem.** There exists $`N(d,r)\ge d`$ such that for every $`n\ge N(d,r)`$ the following inequalities hold simultaneously:

$$
(-1)^kP_n(-w_{n,k}^{d})>0\qquad(1\le k<D).
$$

In dimension two the inequalities hold for every $`n\ge2`$. Consequently these prescribed radii separate the roots. When $`D\ge1`$, the $`D`$ open intervals formed on $`(0,\infty)`$ by the $`D-1`$ internal radii each contain exactly one root of $`x\mapsto P_n(-x)`$, and each root is simple. For the outer intervals use $`P_n(0)=1`$ and the positive degree-$`D`$ coefficient. The upper bound of $`D`$ on the number of roots counted with multiplicities then gives the conclusion.

## Combining the interior and the two edges

Assume $`d\ge3`$. Write $`\theta=\pi/d`$, $`\nu=(d-1)/2`$, $`z=w e^{i\theta}`$, $`H(z)=\sum_{s=0}^{r}\binom ds z^s`$ and $`B(z)=\sum_{s=0}^{r-1}\binom{d-2}s z^s`$. The uniform overlap lemma uses the phase $`n\arg H(z)-\nu\arg(zB(z)/H(z))`$. It agrees with the ordered phase. The ratio has positive real part, its argument tends to $`\theta`$ as $`w\downarrow0`$, and the arguments of $`H,B`$ are continued from zero. Thus the two expressions use the same continuous argument throughout. [Uniform overlap estimates and phase matching](../../fixed-rank-eventual.tex) · [Ordering theorem](../README.md)

The matching argument in that manuscript gives fixed positive integers $`L,M`$ for which, at every sufficiently large $`n`$, the internal nodes with labels $`L\le k\le D-M`$ lie in the interval of the overlap lemma. There it gives a positive normalization $`C_n(w)`$ satisfying

$$
\left|C_n(w)P_n(-w^d)-\cos\Psi_n(w)\right|<\tfrac12.
$$

At a node labeled $`k`$, the cosine equals $`(-1)^k`$. Global phase ordering identifies these nodes uniquely. It remains to check a fixed list at each end. For each $`1\le k<L`$, the lower-edge transfer gives the strictly positive limit $`(-1)^kF_d(-U_{d,k}^d)`$ proved by the gamma-mixture estimate and the two finite certificates. For each $`1\le j<M`$, the upper-edge theorem gives the sign at $`k=D-j`$ for all sufficiently large $`n`$, including every attainable residue of $`nr`$ modulo $`d`$. Taking the largest of these finitely many thresholds and the overlap threshold proves the simultaneous assertion. The proof gives no explicit value of $`N(d,r)`$. [Edge transfers](phase-edge-transfer.md) · [Lower limiting signs](lower-gamma-mixture.md) · [Upper limiting signs](angular-upper-edge-sign.md)

## Dimension two at every height

Here $`r=1`$. Choosing disjoint supports gives $`a_k=n!/((k!)^2(n-2k)!)`$. Summing these polynomials in $`n`$ gives the generating function $`(1-2x+(1+4w^2)x^2)^{-1/2}`$ at $`q=-w^2`$. The Legendre generating function identifies

$$
P_n(-w^2)=(1+4w^2)^{n/2}L_n(\cos\phi),\qquad \phi=\arctan(2w),
$$

where $`L_n`$ denotes the Legendre polynomial. Put $`A=n+1/2`$. The exact angular phase is $`A\phi-\pi/4`$ since $`H(z)=1+2z`$ and $`B(z)=1`$. The Legendre equation for $`y(\phi)=\sqrt{\sin\phi}\,L_n(\cos\phi)`$ gives

$$
y''+\left(A^2+\frac{1}{4\sin^2\phi}\right)y=0.
$$

The vector $`(y,-y'/A)`$ never vanishes on $`0<\phi\le\pi/2`$, by uniqueness for the differential equation. Write it as $`R(\cos\psi,\sin\psi)`$ with $`R>0`$. Choose the lift with $`\psi(\pi/2)=n\pi/2`$. Legendre parity and Rodrigues' formula justify this choice: $`L_{2m}(0)`$ and $`L'_{2m+1}(0)`$ both have sign $`(-1)^m`$, and the other component vanishes in each case. Differentiation and integration back from $`\pi/2`$ give

$$
\psi'=A+\frac{\cos^2\psi}{4A\sin^2\phi},
\qquad
\left|\psi-(A\phi-\pi/4)\right|\le\frac{\cot\phi}{4A}<\frac{1}{4A\phi}.
$$

At an internal node, $`A\phi=k\pi+\pi/4`$. The rightmost bound is less than $`\pi/2`$, so $`\cos\psi`$ has strict sign $`(-1)^k`$. The positive factors relating it to $`P_n(-w^2)`$ preserve that sign.
