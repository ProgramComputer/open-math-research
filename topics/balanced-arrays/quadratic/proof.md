# Real zeros above a quadratic number of rows

**Theorem.** There is an absolute constant $`C`$ such that for every $`d\ge2`$, $`1\le r\le d`$ and $`n\ge C d^2`$, the polynomial counting labeled binary $`n\times d`$ arrays by their common column sum, subject to row sums at most $`r`$, has exactly $`\lfloor nr/d\rfloor`$ distinct negative roots. At $`d=1`$ the polynomial is $`(1+q)^n`$, with a zero of multiplicity $`n`$ for $`n\ge1`$.

**Corollary.** There are absolute constants $`c>0`$ and $`N`$ such that, for every $`n\ge N`$, every dimension $`d\ge2`$ and every admissible row cap $`r\le c\log n`$, all the roots are simple and negative. The constants in the height and rank bounds, including the minimum row count in the corollary, are existential. In particular, in any infinite sequence of distinct counterexamples to the original conjecture, the cap is eventually greater than $`c\log n`$, and the dimension lies between constant multiples of $`\sqrt n`$ and $`n/\log n`$. For bounded $`n`$, coefficient separation covers $`d\ge n`$, leaving finitely many triples. Thus $`n`$ tends to infinity along any such sequence. The upper dimension restriction uses the previously proved high-dimensional bound. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [High-dimensional bound](https://github.com/ProgramComputer/open-math-research/tree/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/dense-regime)

## Reduction to a sequence

Write $`P(q)=\sum_{k=0}^D a_kq^k`$ and $`T=nr/d`$, $`D=\lfloor T\rfloor`$. For every integer $`0\le k\le D`$, fill $`dk`$ slots split into $`n`$ groups of at most $`r`$ with the repeated sequence of columns $`1,\ldots,d`$. This realizes a valid array because no row repeats a column and the total is divisible by $`d`$. Thus all coefficients on $`[0,D]`$ are positive.

If the theorem admitted no such $`C`$, we could select failures with $`n/d^2\to\infty`$. If $`d`$ were bounded along a subsequence, finitely many caps would be involved and the fixed-cap eventual theorem would contradict these failures. The unrestricted case $`r=d\ge2`$ is already covered by the binomial multiplier theorem. We may assume $`d\to\infty`$ and $`1\le r<d`$, allowing $`r`$ to vary. Set $`b=d^2/n\to0`$, $`\phi=\pi/d`$ and $`\nu=(d-1)/2`$. Then $`D/d\to\infty`$. [Fixed-cap theorem](https://github.com/ProgramComputer/open-math-research/tree/f7e10f84dd21fec44ca58c60bae0879d12ebd89b/topics/balanced-arrays/fixed-cap) · [Unrestricted case](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/finite-linear-reduction.md)

## Choosing and locating the phase levels

Under a positive row tilt $`w`$, the size $`S`$ has weights $`\binom ds w^s`$ for $`0\le s\le r`$. Write $`H(w)`$ for their sum, $`\mu=\mathbb ES`$, $`V=\mathrm{Var}(S)`$, $`h=r-\mu`$, $`y=n\mu/d`$ and $`G(s)=s(d-s)/(d(d-1))`$. Let $`w_x`$ denote the tilt with $`y=x`$, unique on $`0<x<T`$ because the derivative of the mean in $`\log w`$ equals $`V>0`$. Write

$$
\lambda_t=\frac{\mathbb E[G(S)e^{itS}]}{\mathbb E e^{itS}},
\qquad \Psi(w)=n\arg H(we^{i\phi})-\nu\arg\lambda_\phi .
$$

Take arguments continuously from angle zero. Both positive sums defining the arguments have angles in $`[0,r\phi]`$ with $`r\phi<\pi`$, so they are nonzero. As $`w`$ increases from zero to infinity, $`\Psi`$ has respective limits $`-\nu\phi`$ and $`T\pi`$, using the first nonzero and last degrees of the numerator defining $`\lambda_\phi`$. Every internal level $`k\pi`$ therefore has a first hitting point $`v_k`$, and continuity gives $`v_k<v_{k+1}`$.

We use two estimates from the derivation of the quartic-log bound that hold without its height assumption. For every tilt,

$$
|\Psi(w)/\pi-y|\le C_0 d+C_0\min(y,T-y)/\sqrt d .
\tag{1}
$$

Indeed the variance bounds $`V\le d/4`$, $`V\le\mu(1+\mu)`$ and $`V\le h(1+h)`$ imply $`V\le C\sqrt d\min(\mu,h)`$. Taylor's inequality gives $`|\arg H(we^{i\phi})-\mu\phi|\le C V/d^2`$, and $`|\arg\lambda_\phi|\le\pi`$. The cited variance bounds follow respectively from the success/failure size-bias comparison for the truncated binomial and from log-concavity of the tail probabilities of $`S`$ and $`r-S`$. [Phase estimates and proof of the variance bounds](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/proof.md)

At $`k/d\to c_0\in(0,\infty)`$, evaluated at $`v_k`$, (1) first gives $`y=O(d)`$, hence $`\mu=O(b)`$. Putting $`u=dw`$ gives $`u\le\mu/(1-\mu)`$ and size weights bounded above by $`u^s/s!`$. Therefore $`\mathbb E|S-\mu|^3=O(\mu)`$, and reweighting with $`G`$ gives expected distance $`O(\mu)`$ from size one. The latter follows from $`G(s)/G(1)\le s`$ and $`\mathbb P(S=1)\asymp\mu`$. Taking the imaginary part after centering at the mean in the characteristic function gives a radial angular error $`O(\mu\phi^3)`$, and $`\arg\lambda_\phi=\phi+O(\mu\phi)`$. Since $`n\mu\phi^3=O(y/d^2)=o(1)`$, the level equation yields $`y(v_k)=k+1/2+o(1)`$. On bounded translates of $`k`$, $`V_x\sim dx/n`$ uniformly and $`\frac{\mathrm d}{\mathrm dx}(d\log w_x)=b/V_x`$. Integration thus shows

$$
d\log v_k=d\log w_k+d/(2k)+o(1).
\tag{2}
$$

If $`k/d\to\infty`$, (1) ensures $`y(v_k)/d\to\infty`$. This implication requires no assumption about the distance from the upper endpoint.

## Signs and order

Put $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$ and $`\Gamma_k=a_k^2/(a_{k-1}a_{k+1})`$. Use the radii $`t_k`$ for $`1\le k\le d`$ and $`v_k^d`$ for $`d<k<D`$. There is only one change of radii. The upper angular estimate treats every internal level near saturation, including the levels within a bounded distance of the degree.

For $`k/d\to0`$, the orientation inequality gives $`\Gamma_k\ge(1+1/k)^d\to\infty`$ and strict log-concavity throughout the support. At $`t_k`$, normalize by $`(-1)^ka_kt_k^k`$. The two neighbors have magnitude $`1/\sqrt{\Gamma_k}`$, and the remaining alternating tails start with a positive term and have decreasing magnitudes. This gives a strictly positive limit inferior. [Orientation inequality](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/orientation-normalization.md)

At $`k/d\to c_0\in(0,\infty)`$, the lower-quota comparison proves $`\log\Gamma_{k+j}\to1/c_0`$ at every fixed integer translate, and $`\log t_k=d\log w_k+d/(2k)+o(1)`$. This uses exact finite differences of the margin normalizing factors and controls the sparse margin correction after conditioning. At $`x=t_k`$ or $`x=v_k^d`$ we therefore have $`\log(x/t_k)=o(1)`$ by (2). For fixed $`j`$, $`a_{k+j}x^j/a_k\to e^{-j^2/(2c_0)}`$ by multiplication of adjacent ratios starting with the two neighbors. Both distances to the support endpoints tend to infinity. By log-concavity the outward consecutive ratios after any large fixed distance $`L`$ are bounded by a geometric factor less than one, using their limits at $`L`$. Sending $`L`$ to infinity gives

$$
\frac{(-1)^kP(-x)}{a_k x^k}\longrightarrow
\sum_{j\in\mathbb Z}(-1)^j e^{-j^2/(2c_0)}
=\sqrt{2\pi c_0}\sum_{m\in\mathbb Z}e^{-2\pi^2 c_0(m+1/2)^2}>0
$$

by Poisson summation. [Lower-quota comparison](quadratic-lower-quota.md)

Now let $`k/d\to\infty`$ and set $`w=v_k`$. Integrating the row polynomial power on the torus $`|z_i|=1`$, $`\prod_i z_i=-1`$ gives $`P(-w^d)`$, since only common column exponents survive. Choose the fixed constant $`h_0>0`$ from the near-full angular lemma. If $`\mu\le1/10`$, then $`n\mu/d^2=y/d\to\infty`$ and the small-mean integral estimate applies. Its only size condition is $`n\mu/d^2\to\infty`$. If $`\mu\ge1/10`$ and $`h\ge h_0`$, the quadratic interior estimate applies. Each gives two conjugate principal terms with sum equal to twice their positive amplitude times $`\cos\Psi(w)`$, with error $`o(1)`$ on the scale of one term. Thus the sign is $`(-1)^k`$. [Small-mean estimate, first section](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/very-tall-nearly-empty.md) · [Quadratic interior estimate](very-tall-quadratic-interior-saddle.md)

For $`h\le h_0`$ the near-full angular lemma gives the same sign at every internal phase level. In this range the equality $`\Psi=k\pi`$ yields $`T-k=(nh/d)(1+O(d^{-2}+d/n))`$, so $`nh`$ is at least of order $`d`$ even at the last internal level. If $`nh/d^2\to\infty`$, just the two principal terms determine the sign. When $`nh/d^2`$ is bounded, an odd multiple $`\ell\phi`$ with $`|\ell\phi|\le M/\sqrt{nh}`$ contributes a phase equal to $`\ell k\pi+o(1)`$ for fixed $`M`$. All such terms have the required sign, and their summed positive amplitudes dominate the remaining Gaussian tail for a sufficiently large $`M`$. This covers both integral and nonintegral $`T`$. [Near-full sign theorem](near-full-all-angular-signs.md)

The geometric points are increasing by strict log-concavity. The phase points are increasing by their first-hitting definition. At the join, $`\log(t_{d+1}/t_d)=(\log\Gamma_d+\log\Gamma_{d+1})/2\to1`$, and at index $`d+1`$ the replacement by the phase point changes its logarithm by $`o(1)`$. So all test points are strictly ordered for large $`d`$. Use zero and positive infinity for the endpoint signs $`1`$ and $`(-1)^D`$. If an interior sign failed along a sequence, a subsequence would have $`k/d`$ tending to zero, a positive finite number or infinity. The three cases exclude such a failure. The alternating signs give $`D`$ distinct negative zeros, proving the theorem.

## Ranks up to a constant times the logarithm

Fix $`\varepsilon=1/10`$ in the rank-dependent column bound and let $`B`$ denote its dimension constant. If $`n\ge N`$ and $`r\le c\log n`$, choose $`N`$ sufficiently large that $`r\le n^{1/10}`$. If $`n\ge Cd^2`$, the quadratic row theorem applies. Otherwise $`d^2>n/C`$, which implies $`d\ge B\sqrt{nr/\log n}`$ whenever $`c\le 1/(CB^2)`$. The rank-dependent bound therefore applies in the other range. The general conjecture remains open. [Rank-dependent theorem](https://github.com/ProgramComputer/open-math-research/tree/ba7ddfd7efb37cac33769f4fdfed749e1b5bf58a/topics/balanced-arrays/dense-regime/rank-dependent)
