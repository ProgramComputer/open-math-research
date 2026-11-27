# Interlacing from signed roots in the bounded-aspect range

Let $E_{n,k}(t)$ enumerate permutations of $n$ letters by strict excedances, with every cycle of length at least $k$. For $n\ge10000$ and $4k\le n\le48k$, the quotient rows $E_{n,k}(t)/t$ and $E_{n+1,k}(t)/t$ have simple, strictly negative zeros that strictly interlace. The upper row supplies both outer zeros. Restoring the common simple zero gives weak interlacing of the two original rows. This package formalizes the bounded-aspect part of the repository’s reviewed all-size argument. [Alexandersson’s statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Written proof](../../all-cutoffs/README.md) · [Original Lean statement](RepositoryBoundedInterlacing.lean)

**Formal verification**　🟨 Partial · Lean 4. The cell signs, the half-list of selected middle roots, the seam, and the coverage of the nine aspect intervals passed local Lean 4.19.0. The five new supporting modules compiled on Lean 4.33.1. The original-row adapter is pending because an inherited determinant lemma exhausted its heartbeat budget. [Hosted diagnostic](https://github.com/ProgramComputer/open-math-research/actions/runs/45997329149) [Determinant certificate](../paired-profile/RepositoryCoarseDeterminant.lean) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

## From the determinant to the root lists

Use $t=-\exp(-\pi\cot\theta)$, $R=\pi/\sin\theta$, and the positive normalization $F_m=R^m E_{m,k}(t)/(m!(1-t)^m)$. The bounded-aspect estimate gives

$$
\frac{k}{\sin\theta}\bigl(\sin((n+1)\theta)F_n-\sin(n\theta)F_{n+1}\bigr)>\frac{93581}{10^6}
$$

for $0<\theta\le\pi/2$ and $n\sin^2\theta\ge6/5$. At the sample $\theta_j=j\pi/n$, the second term vanishes and the first sine is $(-1)^j\sin\theta_j$. Consecutive samples thus have opposite old-row signs. Continuity gives an old root in the open interval between them. At every such root the first term vanishes. Inside the interval $\sin(n\theta)$ has sign $(-1)^j$, so the upper row has sign $(-1)^{j+1}$. Both conclusions transfer to the literal polynomials because each row is multiplied by a positive factor. [Cell-sign lemma](DeterminantCellSigns.lean) · [Normalization and middle witnesses](BoundedAngularWitnesses.lean)

Put $H=\lfloor7\sqrt n/20\rfloor$. Every complete cell from $j=H+1$ through $j=\lfloor n/2\rfloor-1$ meets the angular threshold at both endpoints and throughout its interior. At the first sample the root modulus equals the boundary used by the exterior theorem. Strict increase of $\exp(-\pi\cot\theta)$ orders the selected middle roots beyond the $H$ exterior roots. The final selected modulus is strictly less than one, even when the upper endpoint is $\pi/2$. [Seam and monotonicity](IntegerMiddleSeam.lean) · [Selection over the disjoint open cells](AngularRootSelection.lean) · [Exterior witnesses](../all-aspect-exterior/AllAspectExterior.lean)

Together the two families give $\lfloor(n-2)/2\rfloor$ signed old roots below modulus one. The existing reciprocal-polynomial theorem incorporates the central sign and uses the exact degrees to obtain the two complete root lists. The aspect-interval argument includes equality at each shared endpoint. [Nine-interval coverage](BoundedAspectSlabs.lean) · [Reciprocal root-list theorem](../front-middle-join/OriginalLiteralHalfRoots.lean)

## Reproduction

Use Lean 4.33.1 at the repository research pin. The checker traces the original theorem's imports, compiles each source in dependency order, and checks the theorem's axiom report and Lean kernel replay. [Composition driver](check.py) · [Hosted workflow](../../../../.github/workflows/long-cycle-angular-interlacing.yml)

~~~sh
python3 -I -B topics/long-cycle-excedances/lean/angular-interlacing/check.py --plan
python3 -I -B topics/long-cycle-excedances/lean/angular-interlacing/check.py /tmp/angular-interlacing-verification
~~~
