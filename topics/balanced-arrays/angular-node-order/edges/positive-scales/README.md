# Positive dilations of the total-load section fail at rank four

For $`d=9`$ and $`r=4`$ write $`H(z)=\sum_{j=0}^4\binom9j z^j`$, $`A_m=[z^m]H(z)^n`$, and let $`a_{n,k}`$ count the balanced arrays of quota $`k`$. Could the balanced-array polynomial be obtained by integrating $`\sum_k A_{9k}(tq)^k`$ against a positive measure on $`0\le t<\infty`$? The measure can depend on $`n`$. Comparing coefficients would require $`p_{n,k}=a_{n,k}/A_{9k}`$ to be its moments.

**Theorem.** This representation fails for every $`n\ge10^{300}`$. Put $`h=1/1500`$, $`K=\lfloor n(4-9h)/9\rfloor`$ and $`b=\lfloor nh/9\rfloor`$. The following linear combination of nine interior coefficients is strictly negative:

$$
\sum_{j=0}^{8}(-1)^j\binom8j p_{n,K+jb}<0 .
$$

Moments of a positive measure would give the nonnegative integral $`\int t^K(1-t^b)^8\,d\mu(t)`$. The earlier four-column example rules out scales in the unit interval. The present witness covers every nonnegative scale. It concerns the unshifted total-load section and leaves real-rootedness of the original array polynomial open. [Four-column obstruction](../finite-section-obstruction.md) · [Balanced-array conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

## The negative difference in the limit

Give each admissible binary row $`X`$ probability proportional to $`w^{|X|}`$ and put $`S=|X|`$, $`x=4-\mathbb E S`$ and $`a(x)=\mathbb E[S(9-S)]/72`$. Define $`a(0)=5/18`$ by continuity at saturation and $`g(x)=(a(0)/a(x))^4`$. Writing $`v=1/w`$, the functions $`x`$ and $`a`$ are rational in $`v`$. Eight applications of $`(dx/dv)^{-1}\,d/dv`$ give the exact certificate

$$
g^{(8)}(0)=-\frac{8846065132029}{58824500000},
\qquad g^{(8)}(x)<-60\quad (0\le x\le9h).
$$

The certificate and its coefficient bounds are reconstructed in the [independent derivation](review.md). Integration over $`[0,h]^8`$ gives $`\Delta_h^8g(h)<-60h^8`$. For each $`0\le j\le8`$ consider the tilt with $`x=(9-j)h`$. The normalized probability $`(2\pi n)^4 a(0)^4 p_{n,K+jb}/3`$ tends to $`g(x)`$, by dividing a nine-dimensional lattice local limit by the scalar local limit for the total load. Below we bound the error sufficiently tightly to retain the sign for the stated finite heights. Reversing the order of the nine test points leaves the eighth difference unchanged.

## Explicit error at the nine tilts

The polynomials $`B(v)`$ and $`Q(v)`$ in the [derivative calculation](review.md) give $`x=vB'/B`$ with $`x`$ increasing. At $`v=10^{-4}`$ one has $`B'/B<2`$, and $`x(1/100)>9h`$. Thus $`100<w<10^4`$ at every tilt used here. In the row law the atom at zero and the atom at each unit vector have probability at least $`\epsilon=10^{-19}`$ since $`H(w)\le 2^9w^4<10^{19}`$. In the scalar size law the atoms at zero and one satisfy the same bound. Also $`\mathbb P(S=4)=126/B(v)>1/2`$, so $`g(x)<16`$.

Consider either of these two laws in dimension $`m=9`$ or $`m=1`$. Write $`\phi(t)`$ for its centered characteristic function and $`\Sigma`$ for its covariance. The norm of the centered variable is at most four. The two-copy variance formula, restricted to the pairs $`0,e_i`$ in both orders, shows that all eigenvalues of $`\Sigma`$ are at least $`\epsilon^2`$. They are at most 16 by the norm bound. The same pairs in $`1-|\phi(t)|^2`$ and the inequality $`1-\cos t_i\ge2t_i^2/\pi^2`$ give, throughout the Fourier cube $`[-\pi,\pi]^m`$,

$$
|\phi(t)|\le\exp(-\epsilon^2\lVert t\rVert^2/6).
$$

For $`\lVert t\rVert\le1/16`$, Taylor expansion about zero gives $`|\phi(t)-1|\le8\lVert t\rVert^2`$ and $`|\phi(t)-1+t^\mathsf T\Sigma t/2|\le(64/6)\lVert t\rVert^3`$. The logarithm remainder is at most $`128\lVert t\rVert^4`$. In particular

$$
\left|\log\phi(t)+t^\mathsf T\Sigma t/2\right|\le20\lVert t\rVert^3 .
$$

The vector target is $`(K+jb)\mathbf1`$ and both floor errors are less than one. Its displacement from the vector mean has norm at most 27. The scalar displacement from the total-load mean has absolute value at most 81. In the Fourier integral rescale $`t=u/\sqrt n`$. On $`\lVert u\rVert\le n^{1/12}`$ the complex exponent, including the displacement, differs from $`-u^\mathsf T\Sigma u/2`$ by at most $`20n^{-1/4}+81n^{-5/12}\le101n^{-1/4}`$. For $`n\ge10^{300}`$ the exponential relative error there is at most $`202n^{-1/4}`$.

Let $`I=(2\pi)^{m/2}/\sqrt{\det\Sigma}>2^{-m}`$ be the full Gaussian integral. The absolute integral over the rest of the rescaled Fourier cube divided by $`I`$ is at most $`(4\pi\sqrt n)^9\exp(-\epsilon^2 n^{1/6}/6)`$. The missing Gaussian tail divided by $`I`$ is at most $`2^{9/2}\exp(-\epsilon^2 n^{1/6}/4)`$ by retaining half its precision for integration. Each is less than $`n^{-20}`$. Indeed $`\epsilon^2n^{1/6}/6>40\log n`$ at $`n=10^{300}`$ and $`n^{1/6}/\log n`$ increases thereafter. Thus both local probabilities have relative error at most $`\eta=205n^{-1/4}`$ when compared with their centered Gaussian main terms.

Put $`V=\mathrm{Var}(S)`$. The row covariance has eigenvalue $`V/9`$ in the all-ones direction and eigenvalue $`a(x)`$ in its eight orthogonal directions. Dividing the two Gaussian main terms gives $`3(2\pi n a(x))^{-4}`$. The relative error of the quotient is at most $`2\eta/(1-\eta)<3\eta`$. Multiplying by the common normalization above, the absolute error from $`g(x)`$ is less than $`48\eta`$. At $`n\ge10^{300}`$ the total error in the eighth difference is less than $`256\cdot48\cdot205n^{-1/4}<60h^8`$. This proves the claimed strict sign.

**Verification.** An independent agent checked the derivative, the limiting argument and the explicit height cutoff. [Derivative review](review.md) · [Cutoff review](cutoff-review.md) The integer checker uses Python 3 and its standard library. Formal verification is ⬜ None.

~~~sh
python3 -IB verify_derivative.py
~~~
