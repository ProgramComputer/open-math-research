# Independent blind referee report

**Verdict.** The submission proves Alexandersson’s entire conjecture for the strict interior peak polynomials of Catalan words. Every zero is simple and negative, and consecutive nonconstant rows interleave strictly in the orientation stated by the source. The initial constant rows satisfy the empty-root cases. I found no gap affecting these conclusions. This is an agent-assisted blind mathematical review.

## Original statement and enumerator

I checked the original word conditions, the strict inequality at both neighbors, and the source’s interleaving convention. For equal degrees the old row lies to the left of the new row. For a degree increase the new row has the two outer zeros. A strict peak begins with an ascent of exactly one, so it is precisely the length-one peak in Baril et al.’s terminology. Specializing their Theorem 5.1 and including the empty word gives the generating function used in A and B. A word cannot have adjacent strict peaks, and an alternating word achieves the degree $\lfloor(n-1)/2\rfloor$ for $n\ge1$. [Alexandersson’s statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjCatalanWordPeaks) · [Interleaving convention](https://www.symmetricfunctions.com/realRootedInterlacing.htm) · [Baril et al., Theorem 5.1](https://arxiv.org/html/2404.05672v1#S5.Thmtheorem1)

I also recovered the shifted coefficient formula used in C. With $u=t-1$, rationalizing the generating function gives $G=(1-T)^{-1}$, where $T(1-ux^2-T)=x$. First treat $y=ux^2$ as a separate variable and use $T=x/(1-y-T)$. By Lagrange inversion, for $q\ge1$,
$$
[x^q y^i](1-T)^{-1}
=\frac1q[z^{q-1}y^i](1-z)^{-2}(1-y-z)^{-q}
=\frac1q\binom{q+i-1}{i}\binom{2q+i}{q-1}.
$$
Substitution of $q=n-2i$ gives the required coefficient. The $x^0$ part in the two-variable expansion consists of $1$.

## Infinite ranges

- In A, I checked the quartic roots, the phases and the orientation of the radially cut contour. The branch equal to one at the origin is the product of the four principal factors. Its value at $x=c$ on the positive real axis is $1-c^2$, so the apparent pole is removable for the radial cuts. The upper bank of the ray gives $-2i\sqrt{s}$ in the jump of its singular factor. With the coefficient contour deformed to the rays, this yields the sign in (1). The numerator has order at most two at infinity in the coefficient formula, and the denominator has order two, which disposes of the outer circle term for $n\ge1$.
- I checked the beta moments, the local and tail estimates, and the bound for the two remote rays. The phase levels lie within the admissible parameter interval, and their signs, the positive value at zero, and the leading sign at $-\infty$ force the full degree of distinct roots. Differentiating the two arctangent arguments gives the stated derivative bounds. Strict increase of the phase and the exact root count place each middle root between its two designated phase levels. The beta tilt gives the covariance identity in (8), and at a middle root the correction from the argument of $J_n$ cannot move the phase past either boundary. The sign margins in the two angle ranges therefore give $(-1)^j$ at the old root of rank $j$.
- In B, the square root of the quadratic factor containing the slit is positive on the real axis to the left of the slit and negative to its right, while the other quadratic has its square root positive on the real segment in question. This follows by writing the slit quadratic root as the branch with leading term $-z$ at infinity. The continuation supplies the stated pole and residue at $z=c$, including at the double-root parameter. The horizontal jump adds the integral and the vertical jump subtracts it. I checked the positivity outside the window, the sign at its other endpoint, and the bounds giving the negative derivative at every crossing. The multiplicative comparison of the chord integrals gives a strictly negative value of row $n+1$ at the largest zero of row $n$, as A requires.
- In C, I checked the factorial quotient, the tail ratios and the two Rouché estimates. The reversed variable is $u_1/(1-t)$, so the isolated small root in that variable is the farthest root in $t$. Each neighboring odd row has its farthest root strictly beyond the even row’s farthest root, while all its other roots lie strictly closer to zero. With all zeros already known to be real and simple from A, these orders give the sign $(-1)^m$ at the farthest old zero in both parities.

The analytic arguments cover the pair starting at $n=150$ and every larger pair. The exact prefix covers the pair ending at $150$ and every smaller pair. The signs at old zeros and at zero force all the new roots into the appropriate intervals, with the leading sign supplying the last interval exactly when the degree increases. This also checks the required equal-degree orientation.

## Exact replay and formal coverage

I ran all three supplied checkers under CPython 3.12.16 with python-flint 0.9.0.

- The full checker verified 151 negative simple-root counts and 150 strict oriented pairs, as well as its exact numerical margins.
- The right-edge checker verified nine positive translates, 81 exact rows and 80 oriented pairs.
- The far-left checker verified the exact rational bracket comparisons with both neighboring odd rows for every even row from 4 through 42.

I checked why the second signed remainder chain certifies interleaving. Each step has the recurrence $S_i=q_iS_{i+1}-\lambda_iS_{i+2}$ with $\lambda_i>0$. Backward induction from the positive constant and the exact degree drops gives alternating signs at the intermediate roots, hence strict interleaving. For equal degrees, the initial remainder is positive at the largest zero of the new row and agrees there with the old row up to a positive scalar. At the smallest new zero its sign is opposite the sign of the old row at $-\infty$, giving the additional old root on the left.

I independently rebuilt all 151 archived rows using the word definition and integer coefficient arithmetic. The state records the final letter $h$ and whether the last step was an ascent. Appending $h+1$ starts an ascent, appending $h$ adds no peak, and appending a value below $h$ adds one peak exactly when the previous step was an ascent. These transitions matched every archived coefficient. Literal enumeration of words gave the same coefficients for lengths 1 through 9.

No Lean or Rocq source or formal theorem was supplied. The analytic proof was checked mathematically and the finite component was replayed with exact Python arithmetic. This package has ⬜ None for Lean or Rocq coverage.
