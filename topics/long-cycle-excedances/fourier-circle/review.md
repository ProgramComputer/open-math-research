# Independent review of the two-step Fourier circle theorem

November 26, 2026. Agent-assisted review of the candidate with proof SHA-256
`9438dfcee55215cfe25b4806ed11cf70899eb02e0749de4a881039a472980d93` and scalar
checker SHA-256 `ba0a7dbdf7dc16461da4b9a22017a76148dd93487ba53fa4c356ae999b6c1288`.
I reconstructed the analytic comparison and the phase and threshold joins. I agree
that the argument proves strict consecutive interlacing of the reduced rows at
the actual next size for every $`n\ge10{,}000`$ and $`n/k\ge44`$, $`k\ge3`$. This is a
partial theorem for the original conjecture. No Lean or Rocq verification is claimed.

## Fourier identities and common normalization

The derivative of the untruncated logarithm has simple poles of residue $`+1`$.
Taking the Taylor remainder of its terms gives $`G'-L'`$ with the denominators
$`w_p-w`$, as in the proof. Differentiation on the fixed contour supplies $`iw`$
and gives $`\partial_\varphi f=i e^{ik\varphi}fD`$ with
$`a_p=R^k/w_p^{k-1}`$. Uniform convergence of the pole sums and their angular
derivatives holds on the selected contour. The $`L^2`$ norm of each pole
kernel squared is the geometric sum $`|R^2-|w_p|^2|^{-1}`$ in either expansion
orientation. A first integration by parts at index $`j`$, followed by one at
$`j-k`$, gives the value bound. The term from differentiating $`D`$ costs
$`R T_0`$ and the term from differentiating $`f`$ costs $`S_0^2`$.

For the contrast, the index $`n+1`$ integration carries its own multiplier
$`n+1`$. Writing it over the common multiplier $`n`$ therefore leaves the
subtraction $`(r/R) f_{n+1}`$ in the exact numerator. After the first
integrations, the modulation is $`r/w-C`$. The decomposition into
$`(z_p-C)/(w_p-w)`$ and $`z_p/w`$ is exact, with the second summand selecting
index $`n+1-k`$ in $`f`$. This accounts for both corrections. The main
contrast derivative requires only $`|z_p-C|\le |p|S`$, and puts the one
power of $`S`$ on the kernel before the norm estimate. The coefficient
contour supplies the common factor $`r(r/R)^n/(2|T_s(w_1)|)`$ after the
$`n+1`$ coefficient carries its $`r/R`$ inside the contrast. The indices
$`n+1-k`$ and $`n+1`$ both exceed $`k`$ throughout the claimed range.

## Envelope and sector checks

I checked the two Taylor contraction splits, including the positive Poisson
tail and the small-radius direct estimate. The lower bounds on the
contracted principal numerator follow separately for the real and sine
parts of the squared modulus. The quotient bound uses the same angle in
both numerator and denominator, so the denominator gap is used only once.
For the refined quotient at $`44\le x\le48`$, the physical distance from the
poles is $`4(.039)r/(9k)<.03`$, allowing the stronger inverse denominator bound.

The pole-radius position spacing is at least $`16/x`$ after the principal
pair. For the finite-aspect contour the enlarged interval has width $`.158`$,
less than $`16/100`$, and one forbidden interval cannot cover the selection
interval of length $`.08`$. The large-aspect forbidden union has length
at most $`9/(4x)+1/40<.2`$. The finite-aspect denominator floor, the
unweighted and weighted pole moments, the two Fourier corrections and
the increasing radius penalty are compatible at both $`x=48`$ and $`x=100`$.

For the large-aspect correction, $`nS\ge\sqrt n\ge10\sqrt x`$ by $`k\ge100`$.
Thus the coefficient multiplying the re-used value bound from
$`f_{n+1-k}`$ is at most $`.9 x/(x-2)`$, with at most $`.01`$ more for the
normalization correction. This reproduces the $`77x^2`$ combined bound.
The resulting $`122x^{5/2}e^{30-.89x}`$ is decreasing for $`x\ge100`$.

For the sharpened gamma mesh estimate, the density ratio bound
$`\exp[-y^2/(2(m+y))]`$ follows by integrating the log derivative on
both sides of the mode $`m=k-1`$. The function $`y/(m+y)`$ increases, so
the distance lower bound $`(2j-1)s/2`$ gives at least $`(2j-1)`$ times
the exponent at $`s/2`$. This justifies the geometric remainder after
the closest mesh point. I checked the final weighted pole sum by
retaining four nonprincipal poles and using an integral from the
last retained index. The unweighted error is below one third of the
weighted bound because each retained pole has $`|p|\ge3`$.

## Small thresholds and phase join

The direct contour errors are sufficient on all $`4\le k<100`$ from old
size $`10{,}000`$. The worst endpoints are $`k=9,49,99`$ in the respective
bands. I explicitly checked all 96 integer thresholds at the proposed
lower height, and monotonicity in $`n`$ thereafter. For $`10\le k<100`$
the outer point $`s_*>2\sqrt n\ge200`$ meets $`\max(50,2k)`$, so the
small phase correction applies there. For the middle angles of these
thresholds the weaker gamma correction is paired with the larger
$`nS^2`$ decay. For $`k\le9`$ the inherited contour uses $`s_*>10\sqrt k`$
at the outer point and its prior pole bound elsewhere. The published
all-size $`k=3`$ theorem covers the final boundary.

Set $`h=\lfloor .35\sqrt n\rfloor`$ and $`\theta_*=(h+5/6)\pi/n`$. The
sine Taylor bound gives $`nS_*^2>1`$ already at the floor $`n=10{,}000`$.
The inherited $`h`$ exterior roots precede $`\theta_*`$ by the midpoint
convexity lower bound on $`\log(1+1/h)`$ and the explicit exterior
modulus constant. The phase starts below $`(h+1)\pi`$ because
$`|\gamma_*|+\theta_*<\pi/6`$. At $`s=0`$, the linear term of $`G`$
gives $`\gamma=\pi/2`$, and the higher odd coefficients vanish, so the
phase is exactly $`n\pi/2`$. The endpoint adjacent to the exterior
part, both center parities and reflection then agree in sign. In
particular the first selected interior zero has $`j=h+1`$ in the phase
gap, and the sign of the next reduced polynomial there is
$`(-1)^{h+1}`$, as required after the $`h`$ exterior roots. The old error
$`.20`$ and contrast error $`.77 S`$ are sufficient since
$`\sqrt{1-.20^2}>.77`$. The full degree count gives simplicity and strict
interlacing by alternation at all old roots.

## Replay

The author's checker replayed with identical stdout. The independent
[checker](check-independent.py) uses Machin's formula for rational bounds on $`\pi`$,
an unscaled unit-interval exponential series with a separate integer
power, and explicit rational lower bounds on square roots. It checks
the Taylor contractions, pole bounds, Fourier scalar endpoints and
small-threshold and exterior joins. See the [recorded output](independent-output.txt).

The repository edition corrects the two lattice-sum separators, updates links, and adjusts GitHub math delimiters.
