# Independent review of the conditioned Fourier tail and logarithmic dimension cutoff

**Verdict.** The tail bound in [direct-row-tail.md](direct-row-tail.md) and the final sign implication hold at $`u=\log n\ge10^6`$ and $`d\ge100n/u`$. Taking the adjacent-quota comparison in [direct-comparison.md](direct-comparison.md) as an input, the argument proves that all $`\lfloor nr/d\rfloor`$ roots are simple and negative for every admissible cap. This is an agent-assisted written review of the tail, scalar curvature estimates, and root count. The row cumulant expansion and the derivation of the adjacent-quota comparison are outside this review. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

## Tail bound after division by the row atoms

For a row of Bernoulli parameters $`p_i=\ell_i/d`$ and mean atom $`b_i`$, integrating the $`\ell_i`$-th Fourier coefficient in its row angle is precisely $`b_i\chi_i(\boldsymbol\theta)`$. Taking absolute values before the row integration is legitimate and the single-cell modulus bound yields

$$
b_i|\chi_i(\boldsymbol\theta)|\le e^{-dv_i}I_0(v_iR),
\qquad R=\left|\sum_j e^{i\theta_j}\right|.
$$

Thus the product is bounded by the stated envelope $`B(R)/\prod_i b_i`$. The column-angle event and the modulus are both invariant under common translations. The map from the fixed-last-column section and the common angle to the full torus preserves normalized Haar measure, so this calculation also gives the bound on the section used in Fourier inversion.

Put $`s=d/n`$, $`\delta=\min(s,1/4)`$ and $`T=100/\delta`$. Then
$`400\le T\le u`$, $`d\ge n/T`$, and $`n^{-1/4}\le\delta/12`$ since
$`e^{u/4}\ge u/4\ge 12/\delta`$. With $`x\in[s/3,1-s/3]`$ this gives
$`p_i\in[\delta/4,1-\delta/4]`$, so $`v_i\ge1/T`$ and $`A=\sum_i v_i\ge n/T`$.
The lower Bessel bound follows by integrating the cosine integral
over $`0\le t\le(1+z)^{-1/2}`$. For the upper bound at $`z\ge10`$, the
change $`w=2\sin(t/2)`$ gives a Gaussian weight times
$`(1-w^2/4)^{-1/2}`$. The latter is bounded by $`1+3w^2/8`$ up to
$`w=\sqrt2`$ by the convex secant inequality. The rest costs at most
$`e^{-z}`$ and $`\sqrt{2\pi z}e^{-z}\le1/(8z)`$ for $`z\ge10`$.
These give the stated $`J(z)`$ bounds.

For $`R<d/2`$, $`B(R)\le e^{-Ad/2}\le e^{-n^2/(2T^2)}`$. The
Gaussian factor $`G`$ contains at most $`2n`$ variance factors of half power,
all with variance at most $`n`$, and includes a factor $`\sqrt d`$. Hence
$`G\ge (2\pi n)^{-n}`$. The diffuse-region relative loss is at most
$`e^{-n^2/(4T^2)}`$, since $`n\ge u^4/24`$ and $`T\le u`$ imply
$`\log(2\pi n)<2u<n/(4T^2)`$.

For $`R\ge d/2`$, the row Bessel arguments are at least $`n/(2T^2)\ge10`$.
Their exponent corrections sum to at most $`Tn/d\le T^2`$.
The ratios of the row Gaussian factors contribute
$`(d/R)^{n/2}\le \exp[(n/d)(d-R)]`$. Thus with $`A'=A-n/d`$ the
envelope is bounded by $`e^{T^2}B_0 e^{-A'(d-R)}`$, and
$`A'\ge n/(2T)`$. The lower Bessel bound converts $`e^{A'R}`$ into
$`6\sqrt{1+A'd}\,I_0(A'R)`$. For each mixture center $`\beta`$ the
integral defining $`I_0(A'R)`$ gives independent von Mises column angles.
Their product normalizer costs $`e^{d/(2A')}\le e^T`$ above the
Gaussian power of $`A'`$. Replacing that power by the one for $`A`$
costs at most $`e^{n/(2A')}\le e^T`$, and the remaining ratio is
$`6\sqrt{(1+A'd)/(2\pi A'd)}\le6`$. This gives a relative envelope
cost at most $`e^{2T^2}`$ times the product-law probability of the
column event, which is independent of the mixture center for $`E_\epsilon`$.

Whenever two columns differ by more than $`\epsilon`$ in circular
distance, at least one of the columns is farther than $`\epsilon/2`$
from any given $`\beta`$. The von Mises tail inequality from
$`1-\cos t\ge t^2/5`$ and the lower Bessel bound therefore gives
$6d\sqrt{1+A'}e^{-A'\epsilon^2/20}\le
6n^{3/2}e^{-n^{1/5}/(40T)}$. The weakened bound
$`n^{3/2}e^{3T^2-n^{1/5}/(40T^2)}`$ on the relative aligned-region
contribution follows since $`T\ge400`$.

The lower Stirling bound for $`d!`$ and the upper bounds for
$`\ell_i!`$ and $`(d-\ell_i)!`$ give
$`b_i\ge(2\pi d v_i)^{-1/2}\exp[-1/(12d v_i)]`$, using the
nonnegative Stirling error in the numerator. Hence
$`B_0/\prod_i b_i\le e^{T^2/12}`$. Covariance in the zero-sum
column subspace is $`\Lambda=dA/(d-1)`$, since the off-diagonal
entries of one row covariance are $`-v_i/(d-1)`$.
In the fixed-last-column gauge the covariance quadratic form has
determinant $`\Lambda^{d-1}/d`$. Changing the Gaussian determinant
power from $`A`$ to $`\Lambda`$ costs the factor
$`(1+1/(d-1))^{(d-1)/2}<e^{1/2}`$. This verifies the full prefactor
after dividing by the atoms.

The sixth exponential series term gives
$`n^{1/5}/(40T^2)\ge u^6/(450000000T^2)>1000u^2`$ since $`T\le u`$ and
$`u\ge10^6`$. The diffuse exponent is at least $`u^6/2304>1000u^2`$.
Even after adding the two terms and restoring the prefactors, the
required margin holds by

$$
(4+1/12)T^2+(23/2)u+1/2+\log2<1000u^2 .
$$

This proves the stated bound $`e^{-T^2}n^{-10}`$ in the true subset
Gaussian units at the exact cutoff.

## Theta tolerance and localization at the cutoff

For the sign argument put $`\delta_\theta=\lambda_\theta=100/u`$
and let $`J`$ be the least odd integer at least $`2/\lambda_\theta`$.
Here $`J+2<u/50+4<u`$. The loss in the theta tolerance is

$$
\log(1/\epsilon_\theta)
=\log(u/25)+\frac{\pi^2 u}{400}
<.035u<.04u.
$$

Indeed $`\log u\le u/100`$ for $`u\ge10^6`$ by differentiating the
difference and checking its lower endpoint using $`\log10<3`$.
Also $`\pi^2<10`$. In particular $`n^{-1/8}<\epsilon_\theta/100`$.
The two explicit row cutoff right sides in
[theta-window.md](theta-window.md) satisfy

$$
\begin{aligned}
\log\frac{10^{12}(J+2)}{\delta_\theta^3\epsilon_\theta}
&<36+.08u<u/2,\\
\log\frac{10^{14}}{\delta_\theta\epsilon_\theta}
&<42+.05u<u/4.
\end{aligned}
$$

In these inequalities $`J+2<u`$, $`\log u\le u/100`$, and the tolerance
loss above apply. The remaining scalar cutoff conditions
$`n\ge10^{200}`$ and $`\lambda_\theta\le2\delta_\theta/(1+2/n)`$
also hold.

Let $`b_k`$ denote the log curvature of the balanced coefficients.
The orientation baseline gives
$`b_k\ge d/(k+1)+d/(n-k+1)\ge4d/(n+2)`$.
For $`d\ge n`$ this exceeds $`\log4`$ in the stated row range, giving
strict separation directly. Otherwise $`s=d/n\in[\delta_\theta,1]`$.
At a difficult internal center $`b_k\le\log4`$, the baseline gives
$`\min(k,n-k)\ge d/\log4-1`$. Since $`\log4<3/2`$, $`J+2<u`$, and
$`d/3\ge(100/3u)n>u+1`$ by $`n\ge u^4/24`$, every index within
$`J+2`$ of $`k`$ has density in $`[s/3,1-s/3]`$. This conclusion
concerns densities and can be used on indices whose feasibility is
already known.

The immediate edges from $`k-1`$ to $`k`$ and from $`k`$ to $`k+1`$ are
feasible by internality, even at exact saturation of the latter.
On their density interval the absolute curvature of
$`\log L_j=-(d-1)\log[2\pi n(j/n)(1-j/n)]/2`$ is at most
$`9/(ns^2)`$ by the second derivative. The two comparison slopes
and the cancellation of $`\sqrt d`$ give for the scalar log curvature

$$
\log\frac{U_k^2}{U_{k-1}U_{k+1}}
\le\log4+2n^{-1/8}+9/(ns^2)<2 .
$$

For the upper bound, $`s\ge100/u`$ and $`n\ge u^4/24`$ give
$`9/(ns^2)\le216/(10000u^2)`$.
The deficit $`h=nr/d-k`$ is at least one at an internal quota,
and the scalar negative-binomial comparison is valid there, with
$`e=dh\in[d,nr-d]`$. It gives the lower bound
$`(n-1)/[(h+1)(h+1+1/\delta_\theta)]`$.
If $`h\le\sqrt n/2`$, the denominator factors are both at most
$`\sqrt n/2+u<.51\sqrt n`$, since $`1+1/\delta_\theta\le u`$
and $`n\ge u^4/24`$ gives $`\sqrt n>100u`$. The lower bound would
exceed two, a contradiction. Hence $`h>\sqrt n/2`$. The full
window of radius $`J+2`$ is now feasible and each local deficit
is at least $`\sqrt n/4`$. All its adjacent pairs lie in the
density interval of direct-comparison.md. This local use is
enough for the proof in theta-window.md, even though its
generic hypothesis is stated over a wider density range.
[Scalar deficit estimate](https://github.com/ProgramComputer/open-math-research/blob/8a0a986e6baeed69b30de189e75c02fd2c8cb955/topics/balanced-arrays/deficit-curvature/scalar.md)

## Scalar curvature and strict signs

In this section write $`\delta=\delta_\theta`$ and $`\epsilon=\epsilon_\theta`$.
The tilted row-size variance is at least
$`dx(\rho-x)/\rho`$ for $`\rho=r/d`$. On the full local interval use
$`x\ge\delta/8`$, $`d/n\ge\delta`$, $`\rho\le1`$ and
$`n(\rho-x)\ge\sqrt n/4`$ to obtain
$`V\ge\delta^2\sqrt n/32`$. In particular
$`\sigma\ge\delta n^{1/4}/\sqrt{32}>10^4`$ by the smaller-power cutoff
already checked, and $`\sigma\le n`$ by support. The means are strictly
interior. The scalar local limit estimate with logarithmic error
$`10^{11}n^{-1/4}`$ and standard-deviation derivative bound $`10^9`$
therefore applies.

Writing $`\mu_j=sj`$, the entropy curvature is
$`B_j=n\int_{-s}^s(s-|t|)/V(\mu_j+t)\,dt`$.
The local limit logarithmic determinant contributes at most
$`2\sqrt{32}\cdot10^9\delta^{-1}n^{-1/4}`$ in each curvature,
by the Lipschitz bound on $`\sigma`$ and the lower bound for it.
The three local limit errors contribute at most $`4\cdot10^{11}n^{-1/4}`$.
Together these are less than
$`(5\cdot10^{11}/\delta)n^{-1/4}<\epsilon/16`$.
The $`L`$ term contributes at most $`64/(n\delta^2)<\epsilon/16`$,
where the last inequality follows by raising
$`n^{1/4}\ge10^{14}/(\delta\epsilon)`$ to the fourth power.
The profile slopes contribute at most $`2n^{-1/8}<\epsilon/50`$.
Hence $`B_k<3`$ at the difficult center.

The triangular weight integrates to $`ns^2`$, so $`\sigma`$ reaches
at least $`\delta\sqrt{n/3}`$ on the center mean interval.
All tested mean intervals are within $`J+2`$ mean units of that point.
The cutoff for $`\sqrt n`$ guarantees the possible loss
$`10^9(J+2)`$ still leaves $`\sigma\ge\delta\sqrt n/2`$ throughout.
Thus $`|(1/V)'|\le16\cdot10^9\delta^{-3}n^{-3/2}`$.
Translating the triangular integral by at most $`Js`$ gives
$`|B_{k+i}-B_k|\le16\cdot10^9J\delta^{-3}/\sqrt n<\epsilon/16`$.
The sum of this bound and the errors at the two curvatures is
less than $`\epsilon`$ for every $`1\le|i|\le J-1`$.

For completeness, in the theta comparison let $`a=b_k/2`$.
The log terms at distance $`j`$ from the geometric node center
differ from $`-a j^2`$ by at most $`\epsilon j(j-1)/2`$ up to $`J`$.
Because $`a\ge\lambda_\theta`$, the signed sum perturbation there
is at most $`3\epsilon\lambda_\theta^{-3/2}`$ by Gaussian
summation. Poisson summation gives an ideal lower bound
$`M=2\sqrt{\pi/\lambda_\theta}e^{-\pi^2/(4\lambda_\theta)}`$,
and this perturbation is smaller than $`M/4`$. The omitted ideal
tail divided by $`M`$ is at most
$`e^{-3/(2\lambda_\theta)}/(1-e^{-4})<1/6`$.
Thus the actual truncation is strictly positive in the central
sign. Since $`J`$ is odd, omitted actual terms start with the
central sign on each side and have decreasing magnitude, so
the rest is nonnegative by alternating pairing. At a center
$`b_k>\log4`$ the combined first neighbors have relative magnitude
smaller than one and the same pairing gives the strict sign
directly. [Independent reconstruction of the finite lemma](review-theta.md)

The coefficients are positive through $`D=\lfloor nr/d\rfloor`$:
assign consecutive blocks of $`k`$ cyclic row labels to the
columns. This produces a matrix of quota $`k`$ and row sizes at
most $`\lceil dk/n\rceil\le r`$. The capacity bound gives degree
$`D`$ and the constant coefficient is one. Global strict
log-concavity makes the geometric nodes strictly increasing.
Their alternating signs, the positive value at zero and the
leading sign $`(-1)^D`$ far to the left yield $`D`$ disjoint
negative sign-change intervals. Degree $`D`$ forces all the
roots to be simple. The endpoint signs also cover $`D=1`$,
and $`D=0`$ is vacuous.

**Signed** · quota_referee, independent agent-assisted mathematical review.
