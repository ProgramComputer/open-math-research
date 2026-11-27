# A uniform bound for the long-cycle log tilt

Let $k\ge7$, $x\ge0$, $t=-e^{-x}$, $r=|x+i\pi|$ and $R=r(1+1/(50k))$. Write $G(w)=\sum_{j=1}^{k-1}g_jw^j$ for the finite logarithm in the generating function of the minimum-cycle-length excedance polynomials. With $A_m$ the ordinary Eulerian polynomial, its coefficients are $g_j=-tA_{j-1}(t)/(j!(1-t)^j)$. Then

$$
\sum_{j=1}^{k-1}|g_j|R^j\le 6+9\log k.
$$

Consequently, with $T=\exp G$ and $B=6+9\log k$, every Taylor coefficient satisfies $|[w^d]T|\le e^B/R^d$. Throughout $|w|\le R$ the modulus satisfies $|T(w)|\ge e^{-B}$. This verifies the common-contour input used to control truncation errors at small angles. The [earlier uniform proof](../../effective-uniform.md) used the bound $6+10\log k$. The signs of the other enclosed residues and the near-zero roots require separate estimates. [Original coefficient and amplitude statements](RepositoryUniformMass.lean)

## Proof

Set $w_p=x+ip\pi$ for odd $p$, $S=\pi/r$ and $\rho_p=r/|w_p|$. The Eulerian moment identity gives $j|g_j|r^j\le\sum_p\rho_p^j$ for $j\ge2$. For $j<k$ the radius factor $(R/r)^j$ is at most $50/49$. [Pole-to-monomial inequality](PoleMonomial.lean) · [Inflation bound](UniformHighDegreeLattice.lean)

If $0\le x\le10$, the nearest pair contributes two. Each farther pair has $|p|=2h+1$ with $h\ge1$, and each term is at most $1/(4h(h+1)S^2)$. Telescoping gives a total of at most $2+1/(2S^2)<8$, using $\pi>3.1$. Thus $|g_j|R^j\le9/j$ for $j\ge2$. The linear term costs at most six. [Lattice computation](UniformHighDegreeOddPoles.lean) · [Linear term](LinearTilt.lean)

For $x\ge10$ put $L=\min(k-1,\lfloor x^2/16\rfloor)$. For $j>L$ with $j<k$, one has $j\ge7$ and $jS^2\ge1/2$. Let $m=\lfloor j/2\rfloor$. Then $mS^2\ge3/14$. Bernoulli’s inequality bounds each farther pole by $7/(6h(h+1))$. Thus $\sum_p\rho_p^j\le13/3$, and the inflated multiplier is at most $650/147<5$. These degrees cost at most $5\log k$. [High-degree lattice](UniformHighDegreeLattice.lean) · [Original poles](RepositoryUniformHighDegree.lean)

For $2\le j\le L$, expand the Eulerian moment as an absolutely convergent alternating sum over positive integers $a$. Taking absolute values and interchanging the finite degree sum with the frequency sum gives the upper bound

$$
\sum_{a\ge1}\frac{e^{-ax}}a\sum_{j=0}^{L}\frac{(aR)^j}{j!}.
$$

Write $\delta=R-x$. The circle geometry gives $\delta\le5/x+x/(40k)$ and $R\le53x/50$. If $ax\le2L$, then $a\le k$ and $a\delta\le5/8+1/20<1$. The contribution of that frequency is at most $3/a$. If $ax>2L$, the truncated exponential at $aR$ is at most $2^L e^{aR/2}$ by comparison term by term. As $2\le e^{7/10}$, one has $-ax+(7/10)L+aR/2\le-a$. Each such frequency costs at most $2^{-a}$. Summing gives $3H_k+1\le4+3\log k$, with $H_k=\sum_{a=1}^k1/a$. The linear term costs at most one. This gives $5+8\log k$ when $x\ge10$ and proves the uniform bound. [Radius geometry](RadiusGeometry.lean) · [Frequency estimates](UniformDiscreteTilt.lean) · [Moment sum](LowMomentMass.lean) · [Harmonic summation](UniformMassSum.lean)

## Formal verification

The supporting estimates were checked on the local Lean 4.19.0 toolchain. A specialization using the exact statement of each upstream moment identity as a premise also compiled. Verification against the upstream proofs on their shared Lean 4.33.1 pin is pending. The result is part of the formalization of the [all-cutoff theorem](../../all-cutoffs/README.md). Its overall status is 🟨 Partial · Lean 4.
