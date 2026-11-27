# From an adjacent sine comparison to interlacing

For $n\ge10000$, $2\le k\le n$, the theorem in this package reduces strict interlacing of the reduced rows and weak interlacing of the original rows to positivity of one scalar comparison throughout $0<\theta\le\pi/2$, $n\sin^2\theta\ge6/5$. This is a conditional theorem. With $F_m$ the positive angular normalization of the original row and $D_n=\sin((n+1)\theta)F_n-\sin(n\theta)F_{n+1}$, its hypothesis is $D_n>0$. [Formal statement](RepositoryPairedSine.lean) · [Bounded-aspect estimate and rational certificate](https://github.com/ProgramComputer/open-math-research/pull/284)

At the integer samples, $D_n$ fixes the old sign. At an old root inside a complete gap, it fixes the sign of the original successor. The coefficient identity identifies $D_n$ with a finite sine-weighted sum of the coefficients after multiplication by $1-2u\cos\theta+u^2$. The principal wave with real and imaginary amplitudes $a,b$ contributes exactly $a\sin\theta$. [Sine identities](PairedSineComparison.lean) · [Finite Taylor identity](PairedDeflatedCoefficients.lean) · [Integer-gap witnesses](PairedIntegerWindows.lean)

The [signed-pole kernel](PairedSineKernel.lean) checks the exact trigonometric identity at each occupied pole and the absolute bound for its joint old-row and numerator contribution. All four local axiom reports contain only standard axioms.

Local Lean 4.19 rebuilt the generic identities and the conditional assembly with the literal permutation definitions. Two previously stated inputs, the exterior witnesses and the passage from a complete family of signed half-axis roots to both root lists, were supplied as hypotheses in the local assembly check. The production theorem imports both. The integrated Lean 4.33.1 build is pending. The quantitative uniform lower bound in the linked argument has no end-to-end Lean proof.

From the repository root, the production driver is

~~~sh
python3 -I topics/long-cycle-excedances/lean/front-envelope-sums/check.py /tmp/long-cycle-sine-check
~~~
