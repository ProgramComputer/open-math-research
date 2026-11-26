# Marking cycles and detecting adjacent-root collisions

Let $u$ mark each cycle after the first. Write
$$
Q_{n,k}(t,u)=\sum_{\pi}u^{\#\mathrm{cycles}(\pi)-1}t^{\mathrm{exc}(\pi)-1},
\qquad
Q_{n,k}=(1+t)^{n-2}G_{n,k}(y,u),\quad y=t/(1+t)^2,
$$
where all cycles have size at least $k$ and $n\ge k\ge3$. At $u=0$ only single cycles contribute, so $Q_{n,k}(t,0)=A_{n-1}(t)$. At $u=1$ this is the original polynomial after removing its zero at the origin. Applying inversion gives reciprocity at every $u$. Put $a_m(y)=A_m(t)/(1+t)^{m-1}$. Distinguishing the cycle containing the smallest letter gives
$$
G_{n,k}=a_{n-1}+u y\sum_{\ell=k}^{n-k}\binom{n-1}{\ell-1}a_{\ell-1}G_{n-\ell,k}.
$$
Every coefficient of $a_m$ is positive through degree $\lfloor(m-1)/2\rfloor$, by the Eulerian differential recurrence. Thus for all $u\ge0$, $G_{n,k}$ has constant coefficient one and degree $\lfloor(n-2)/2\rfloor$ with positive leading coefficient. The unpaired old or new zero at $t=-1$ stays simple whenever its row degree is odd.

**Collision criterion.** If $`R(u)=\mathrm{Res}_y(G_{n,k},G_{n+1,k})`$ has no zero on $[0,1]$, then rows $n,n+1$ strictly interlace throughout that interval. At $u=0$ the Eulerian rows strictly interlace. Monicity and continuity prevent roots escaping to infinity. A first loss of strict interlacing forces a common real root. Indeed, if two roots of one row merge, the intervening root of the other row has the same limit. A crossing of old and new roots is itself a common root. Zero is excluded by the constant terms. The fixed reciprocal root $-1$ cannot be shared because the other row has even degree and its leading gamma coefficient is positive. Every other shared root gives a common finite $y$, which would force $R(u)=0$. A constant gamma polynomial contributes resultant one under the usual convention.

**An exact obstruction to extending the deformation to all positive weights.** At $(n,k)=(7,4)$ one obtains
$$
G_7=1+52y+136y^2,\qquad
G_8=1+114y+720y^2+272y^3+35u y(1+2y)^2 .
$$
Dividing $G_8$ by $G_7$ or taking the Sylvester determinant gives
$$
R(u)=32400(49u^2-2016u-3264).
$$
Thus the two rows have a common root at $u=(144+40\sqrt{15})/7>1$. Both roots of $G_7$ are negative and each lifts to two negative $t$ values. The constant and quadratic coefficients of $R$ have opposite signs, so a proof by uniform sign of its ordinary coefficients fails even at this pair. On $[0,1]$ the sign of $R$ stays strictly negative. This obstruction concerns the cycle-weight deformation. The original conjecture uses $u=1$.

The bivariate polynomial $G_{2k,k}(y,u)$ also fails real stability at every $k\ge3$. At that size only the single-cycle term and the pair of $k$-cycles occur, so $G_{2k,k}=a_{2k-1}+c u y a_{k-1}^2$ with $c=\binom{2k-1}{k-1}>0$. At $y=i\varepsilon$, the unique zero as a function of $u$ is $i/(c\varepsilon)+O(1)$ as $\varepsilon\downarrow0$, since both Eulerian gamma polynomials have constant term one. Both variables therefore have positive imaginary part for small positive $\varepsilon$. Already at $k=3$, $G_{6,3}=1+22y+16y^2+10uy$ vanishes at $y=i/8$, $u=(-11+3i)/5$. This rules out an argument by direct bivariate stability of this particular cycle marking.

**Finite exact check.** For every $3\le k\le n\le15$ the normalized resultant $\mathrm{sgn}(R(0))R(u)$ has strictly positive coefficients in the Bernstein basis on $[0,1]$. This proves strict consecutive interlacing for the entire continuous family at each of the 91 pairs. It gives a possible invariant for real change in the cycle weights. A general sign-preserving formula for these coefficients is unknown. Higher endpoint cutoffs alone would leave the original induction problem open.

The archive was computed from the marked smallest-cycle recurrence using integer polynomial resultants at consecutive integer values of $u$ with python-flint. The Sylvester determinant bounds the resultant degree by $\deg_u G_n\deg_y G_{n+1}+\deg_u G_{n+1}\deg_y G_n$, with $\deg_u G_j\le\lfloor j/k\rfloor-1$. Forward differences recover every coefficient and one additional evaluation checks interpolation. An independent symbolic replay uses largest-label insertion instead. If $G=G_{n,k}$, its new row is
$$
(1+2(n-2)y)G+y(1-4y)G'+u\binom n{k-1}y\,a_{k-1}G_{n+1-k,k},
$$
where the lag vanishes when its index is below $k$. SymPy reconstructs the resultant symbolically and compares every entry with the archive. Both methods return the same 91 full coefficient vectors and the corresponding rational Bernstein vectors. [Machine-readable archive](marked-resultants.json) · [Independent symbolic replay](verify_cycle_marking.py) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

~~~sh
python3 -I topics/long-cycle-excedances/verify_cycle_marking.py
~~~

The replay requires SymPy. **⬜ None.** There is no checked Lean or Rocq proof for this investigation.
