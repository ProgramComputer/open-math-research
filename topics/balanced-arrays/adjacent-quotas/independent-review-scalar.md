# Independent mathematical review of the scalar and root arguments

**Verdict.** The scalar estimates and the root argument establish the stated partial theorem, taking the consecutive-quota comparison as a separately reviewed input. For every integer $`n\ge 10^{200}`$, $`200d\ge59n`$, and $`1\le r\le d`$, all $`\lfloor nr/d\rfloor`$ zeros of the balanced-array polynomial are simple and negative. This is an agent-assisted written review. The argument has no Lean or Rocq verification.

## Original statement and support

I checked the primary SymCat entry and Per Alexandersson's author issue. Their $`a_{n,k}^{(r,d)}`$ counts labeled zero-one matrices with every column sum equal to $`k`$ and every row sum at most $`r`$. Choosing the support of each row gives their coefficient of $`(e_0+\cdots+e_r)^n`$. The source asks for real-rootedness for every $`n\ge0`$, $`d\ge1`$, and $`1\le r\le d`$, with no simplicity or consecutive-row interlacing requirement. The proposed theorem gives simplicity in its displayed range of $`n,d`$. [SymCat conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Author issue #2005](https://github.com/PerAlexandersson/RealRooted/issues/2005)

For an independent support construction, write the cyclic list of the first $`dk`$ row labels starting at row zero, and assign its consecutive blocks of length $`k`$ to the $`d`$ labeled columns. If $`0\le k\le D=\lfloor nr/d\rfloor`$, then $`k\le n`$, so a block does not repeat a row label. The row sums are either $`\lfloor dk/n\rfloor`$ or $`\lceil dk/n\rceil`$, both at most $`r`$. Counts therefore are positive through $`D`$, with $`a_0=1`$, and vanish thereafter by the total-capacity bound. The construction includes exact saturation and the full cap. Letting $`U_k`$ count capped arrays of the same total without the common-quota condition gives $`a_k=U_k Q_k`$ directly.

## Exact bootstrap away from the cap

At an internal quota let $`h=nr/d-k`$ and $`e=dh`$. Then $`d\le e\le nr-d`$, even when $`k+1`$ is exactly saturated. The negative-binomial-normalized scalar estimate gives

$$
\log\frac{U_k^2}{U_{k-1}U_{k+1}}
\ge \frac{d(n-1)}{n+e+d-1}\log(1+1/h)
\ge \frac{n-1}{(h+1)(h+5)}.
$$

The second inequality uses $`\log(1+1/h)\ge1/(h+1)`$ and $`(n-1)/d<4`$. The cited scalar argument is consistent at the saturated endpoint. In the exact product, the first denominator is $`e-d+1\ge1`$, and all three scalar coefficients have positive support. I also checked the size-biased ratio argument behind the cited estimate. Log-concavity of the convolution of the other $`n-1`$ rows gives the increasing likelihood ratio of the size-biased coordinate as the total increases. The decreasing expectation of the consecutive single-row weight ratio is precisely the decreasing forward ratio after negative-binomial normalization. Comparison of the $`d`$ consecutive forward ratios then gives the stated product. [Scalar deficit inequality](https://github.com/ProgramComputer/open-math-research/blob/8bf2220688ce5fb1e4ac745daa655bb3c3813fbf/topics/balanced-arrays/deficit-curvature/scalar.md)

For $`d\le n`$, orientational log-concavity supplies

$$
\log\Gamma_k\ge d\left(\frac{1}{k+1}+\frac{1}{n-k+1}\right).
$$

The right side exceeds $`1.39>\log4`$ outside $`.305n<k<.695n`$, by the monotonicity of the reciprocal sum on each side of $`n/2`$ and evaluation at the boundary. Thus at a difficult center, where $`\Gamma_k\le4`$, both immediate edges satisfy the density restriction on the comparison, and are feasible by internality. At these three quotas $`Q_j=\sqrt d\,L_jW_j`$ and $`|\Delta\log W|<10^{-6}`$ on both edges. The term $`\log\sqrt d`$ cancels and the absolute $`L_j`$ log curvature is below $`50/n`$. Therefore the scalar log curvature is less than $`1.4`$. If $`h\le .84\sqrt n`$, the exact scalar lower bound would be at least

$$
\frac{1-1/n}{(.84+5/\sqrt n)^2}>1.4,
$$

where the last inequality holds at $`10^{200}`$ and its left side increases with $`n`$. This independently gives $`h>.84\sqrt n>.4\sqrt{n/\log n}`$. It yields $`k+3\le D`$ and, together with the density localization, gives every feasible pair needed for the four comparison slopes and both third neighbors. This use of the comparison is sequential, starting with only the immediately feasible edges, so the bootstrap does not assume its own conclusion. [Orientation normalization](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/orientation-normalization.md)

## One-dimensional local limit and log curvature

For a finite integer log-concave law with standard deviation $`\sigma\ge10^4`$, Chebyshev gives modal mass $`b\ge1/(8\sigma)`$. On each side of a mode the first half-height crossing occurs within $`3/b`$ sites by summing the preceding masses. When that crossing is a zero, all later sites vanish. For a positive crossing, log-concavity extends its secant bound to all later sites. Before the crossing the modal bound suffices. This gives $`p(m\pm j)\le2b\exp(-bj/5)`$. Integrating the corresponding sums for powers two and three gives the written $`2000/b^2`$ and $`30000/b^3`$ bounds, since the unreduced constants are $`1000e^{1/5}`$ and $`15000e^{1/5}`$. Centering the cubic costs at most a factor eight. The combination $`8\cdot30000\cdot8^3<10^9`$ proves the stated centered third moment. The exponential-family identities give $`\lvert d\sigma/d\mu\rvert=\lvert \mathbb E(X-\mu)^3\rvert/(2\sigma^3)`$, within the advertised Lipschitz bound.

The retained sites inside the Chebyshev interval have mass at least $`3/4-6/24=1/2`$. They form an interval by log-concavity, and the upper modal bound $`b\le100/\sigma`$ gives $`M\ge\sigma/200`$. The independent-pair identity for $`1-|\phi|^2`$ thus compares it to the uniform interval characteristic function with the stated $`(M/(24\sigma))^2`$ factor. For $`|t|\ge2\pi/M`$, use $`\sin(|t|/2)\ge |t|/\pi`$. For $`|t|\le 2\pi/M`$, there are at least $`(M/8-1)(3M/4)>M^2/32`$ pairs with distance from $`M/8`$ to $`M/4`$, since $`M\ge50`$. Their angles have magnitude at most $`\pi/2`$. Their contribution gives $`1-|U_M(t)|^2\ge M^2t^2/10240`$. Combining the two bounds and taking the square root leaves the claimed $`10^{-18}`$ damping constant with room.

At the integer target $`n\mu`$, Fourier inversion gives the integral of the centered characteristic function to the $`n`$th power. In the scaled variable $`y=\sigma\sqrt n\,t`$, the cubic Taylor bound contributes at most $`10^9n^{-1/4}`$ on $`|y|\le n^{1/12}`$. The centered second-order bound gives $`|\phi-1|\le y^2/(2n)`$, so the complex logarithm near one has remainder bounded by $`y^4/n`$ after multiplication by $`n`$. The relative Gaussian error from exponentiating is at most $`4\cdot10^9 n^{-1/4}`$. Off the central interval the scaled length is at most $`7n^{3/2}`$ and the damping exponent is at least $`10^{-18}n^{1/6}>4\log n`$. The omitted Gaussian tail is smaller still. Relative to the full Gaussian integral this proves the $`10^{11}n^{-1/4}`$ logarithmic error.

For the capped-binomial tilt at mean $`dx`$, compare with a binomial on $`r`$ trials of mean $`dx`$. The successive ratios of the ratio of their masses are proportional to $`(d-s)/(r-s)`$, so the mass ratio is log-convex on the common finite support. The tilted mass minus the binomial mass has sign pattern plus, minus, plus, allowing ties. Its total and first moment vanish. Testing against the quadratic with zeros at the two sign changes proves $`V(dx)\ge dx(1-dx/r)`$, including equality for identical laws. On the full local interval this is at least $`.04h`$, by $`x\ge.29`$, $`d/n\ge .295`$, $`\rho\le1`$, and local deficit at least $`h/2`$. The assumption $`h\ge .4\sqrt{n/\log n}`$ gives $`h\ge n^{1/3}`$ already at $`10^{200}`$ and thereafter. Thus $`\sigma\ge .2n^{1/6}\ge n^{1/8}`$, and support gives $`\sigma\le d\le n`$. The tilt means in this interval are interior, so the local limit formula applies at every integer quota used for neighbor variation.

Writing $`s=d/n`$, differentiating the entropy term gives $`\Phi''=-1/V`$. The triangular-weight integral $`B_j`$ with total weight $`ns^2`$ is consequently the scalar entropy curvature. The local limit determinant contributes at most $`2\cdot10^9n^{-1/8}`$ to the absolute error because each of the two neighboring log-standard-deviation differences is bounded by $`10^9s/n^{1/8}`$. The three local limit errors contribute at most $`4\cdot10^{11}n^{-1/4}`$. The $`L`$ factor contributes below $`50/n`$ because both $`x`$ and $`1-x`$ exceed $`.29`$, and the consecutive slopes contribute at most $`2\cdot10^{-6}`$. The total is below $`3\cdot10^{-6}`$ exactly in the three places where the applicable slopes are available.

At a difficult center, $`B_k<1.4`$ and hence $`V\ge ns^2/1.4`$ somewhere on the center interval. Since $`(.295)^2>1.4(.24)^2`$, the standard deviation exceeds $`.24\sqrt n`$ there. The full local interval is within $`3s`$ of that point. Its uniform lower bound is therefore $`.23\sqrt n`$, and $`\lvert(1/V)'\rvert<2\cdot10^{11}n^{-3/2}`$. Translating the triangular integral by one mean step changes $`B`$ by less than $`2\cdot10^{11}/\sqrt n`$. Even after including the error at both centers the absolute log curvature change is below $`10^{-5}<\log(1.001)`$. The argument needs only an upper bound on each neighboring $`\Gamma`$, and supplies both.

## Strict signs and all roots

The orientation inequality also gives $`\log \Gamma_j\ge 4d/(n+2)`$ at every internal quota. In the stated range this is greater than $`\log 3.2`$. For $`d\ge n`$ it is greater than $`\log4`$, so every internal index is immediately treated by simple coefficient separation. At any index $`\Gamma_k>4`$, the two neighboring terms at the geometric node have combined magnitude strictly less than the central term. The remaining alternating tails have nonnegative normalized total because their terms decrease outwards. This applies even if one or both tails end immediately.

For $`\Gamma_k\le4`$, set $`R_j=a_j/a_{j-1}`$, $`t_k=(R_kR_{k+1})^{-1/2}`$, and $`\tau=\Gamma_k^{-1/2}`$. The normalized magnitudes at distance one from the center are both $`\tau`$. On either side, the magnitude at distance two is $`\tau^2/\Gamma_{k\pm1}`$ and the ratio from distance two to three is $`\tau/(\Gamma_{k\pm1}\Gamma_{k\pm2})`$. These third terms exist by the bootstrap. Further terms decrease as all curvatures exceed one and can be paired starting at distance four, leaving a nonnegative normalized contribution. Substituting $`\Gamma_{k\pm1}\le1.001\Gamma_k`$, $`\Gamma_j>3.2`$, and $`\tau<.56`$ in the first three distances gives the claimed lower bound

$$
f(\Gamma_k)=1-2\Gamma_k^{-1/2}+1.88\Gamma_k^{-2}.
$$

In fact $`2(1-.56/3.2^2)/1.001>1.88`$. Also $`f'(g)=g^{-3}(g^{3/2}-3.76)>0`$ for $`g\ge3.2`$, and $`3.2(1+1.88/3.2^2)^2>4`$ proves $`f(3.2)>0`$ with positive sides before squaring. This includes equality $`\Gamma_k=4`$ in the difficult branch.

The nodes have $`t_{k+1}/t_k=\sqrt{\Gamma_k\Gamma_{k+1}}>1`$. The strict signs $`(-1)^k`$ at $`-t_k`$, the positive value at zero, and the leading sign $`(-1)^D`$ on a sufficiently negative final point give $`D`$ disjoint negative intervals containing roots. Since the degree is $`D`$, these are all roots and all are simple. The argument also covers a linear polynomial by the two endpoint signs. A constant polynomial has zero roots.

I ran `python3 -B scalar-constants.py` and separately checked the rational bootstrap, Fourier damping, localization, and compensation inequalities with exact fractions. I found no gap in the assigned scalar and root steps. The independently reviewed consecutive-quota comparison is the analytic input to those steps.

**Signed** · quota_referee, independent agent-assisted mathematical review.
