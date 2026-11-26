# Upper signs with corank on the subquadratic scale

2026-11-26 · Private research note

Let $`d\to\infty`$, $`n/d^{5/3}\to\infty`$, and $`b=d^2/n\to\infty`$. Equivalently, the height condition is $`b=o(d^{1/3})`$. Suppose $`1\le c=d-r<d`$ and $`c/b\to\gamma\in[0,\infty)`$. Write $`D=\lfloor nr/d\rfloor`$ and take any internal quota $`k`$ with $`j=D-k=O(d)`$. With $`a_k`$ the actual balanced-array coefficient, put

$$
\Gamma_k=\frac{a_k^2}{a_{k-1}a_{k+1}},\qquad
t_k=\sqrt{a_{k-1}/a_{k+1}}.
$$

Then $`(-1)^k P_n(-t_k)>0`$ eventually. If $`j/d\to\beta>0`$, the first angular crossing $`v_k`$ of the phase $`k\pi`$ also has this sign, and $`\log(v_k^d/t_k)\to0`$. The same matching holds at every crossing. This gives an ordered overlap at any fixed positive limit of $`j/d`$.

## Profile summation with growing hole means

Complement each cell. The hole row sum is at least $`c`$ and the column sum is $`\ell=n-k`$. Set

$$
T=nr/d,\qquad m=d\ell/n,\qquad h=m-c,\qquad p=\ell/n.
$$

Here $`h/b=(T-k)/d=j/d+O(1/d)`$ and $`m/b=c/b+h/b`$. If $`\ell/d\to0`$, then $`\log\Gamma_k\ge d\log(1+1/\ell)\to\infty`$ by normalized log-concavity, and the geometric sign follows at once from its first two alternating tails. For the rest, pass to a sequence with $`\ell/d\to B>0`$ finite. Thus $`m\asymp b`$, $`\ell\asymp d`$, $`p=O(b/d)=o(1)`$, and the same estimates hold at bounded available shifts.

Let

$$
G(w)=\sum_{s=c}^d\binom ds w^s,\qquad
U_\ell=[w^{d\ell}]G(w)^n .
$$

Let $`X`$ have probabilities proportional to $`\binom ds w_\ell^s`$, $`s\ge c`$, at the hole tilt with mean $`m`$, and put $`V_\ell=\mathrm{Var}(X)`$. At exact saturation $`m=c`$ take the deterministic law $`X=c`$. The positive tilt is unique at each interior mean because the mean has positive variance as its derivative in log tilt. It is binomial with parameter $`w_\ell/(1+w_\ell)`$ conditioned to be at least $`c`$, so its unrestricted mean is at most $`m`$, and $`dw_\ell=O(m)`$. The mass ratio at the step to size $`s`$ is at most $`C m/s`$. This also implies raw moment bounds $`\mathbb E X^q=O_q(m^q)`$ uniformly for $`m\ge1`$: beyond a sufficiently large fixed multiple of $`m`$ the ratios are at most $`1/2`$, and before that point the sizes are $`O(m)`$.

In actual equal-column arrays let $`A_s`$ count those where a specified row has size $`s`$. For $`s>c`$, move a hole within its column from that row to another row lacking it. There are $`s(n-\ell)`$ choices. A reverse move must choose a column absent from the specified row, then one of at most $`\ell`$ donors in that column. Thus

$$
s(n-\ell)A_s\le (d-s+1)\ell A_{s-1}.
$$

Its mass ratio is at most $`m/[(1-p)s]`$. For both the actual and the candidate law, these ratio estimates give a tail smaller than any prescribed power of $`n^{-1}`$ above $`L=\lceil A(b+\log n)\rceil`$, for a sufficiently large fixed $`A`$. Indeed start the geometric estimate beyond $`C_1 b`$, where each successive ratio is at most $`1/2`$. The bound also applies to any fixed moments of that tail by increasing $`A`$. A union bound therefore removes all actual arrays with a row above $`L`$ at relative cost $`o(1)`$.

For a profile $`\sigma`$ with maximum at most $`L`$, the total number of holes is $`M=d\ell\asymp d^2`$. The maximum-margin product is $`O(dL)=o(M^{2/3})`$ because $`L=o(d^{1/3})`$. The standardized row variance in Greenhill–McKay–Wang is $`V_{\sigma}/[m(1-p)]`$ for $`V_{\sigma}=n^{-1}\sum_i(s_i-m)^2`$, and is $`O(L)`$ since $`\sum_i s_i^2\le Lnm`$. The standardized column variance is zero. Thus Corollary 5.2 applies uniformly with exponent error $`O(dL/M^{2/3})=o(1)`$. The count with this profile equals

$$
\frac{\binom n\ell^d}{\binom{nd}{d\ell}}\prod_i\binom d{s_i}
\exp\left(-\frac12+\frac{V_{\sigma}}{2m(1-p)}+o(1)\right).
$$

[Greenhill, McKay and Wang, Corollary 5.2](https://doi.org/10.1016/j.jcta.2005.03.005) · [Authors’ accessible manuscript, §5](https://users.cecs.anu.edu.au/~bdm/papers/irregular.pdf)

For independent candidate rows, condition on $`\mathcal E=\{\sum_i X_i=d\ell\}`$. The profile masses are proportional to $`\prod_i\binom d{s_i}`$ with normalizer $`U_\ell`$. The conditioning probability is at least $`1/(nd+1)`$, because the sum pmf $`f`$ is log-concave by convolution and Jensen for the concave interpolation of $`\log f`$ gives $`\log f(d\ell)\ge\mathbb E\log f(\sum_iX_i)\ge-\log(nd+1)`$. The last step is the finite-support entropy bound. At exact saturation this probability is one. Candidates with a row above $`L`$ therefore have conditional probability $`o(1)`$ on choosing the tail power large.

The retained profile correction weight is bounded by $`e^{CL}`$, not necessarily a polynomial. To control it, clip $`(X_i-m)^2`$ to zero above $`L`$. Its expectation differs from $`V_\ell`$ by an arbitrarily small polynomial error, and it is bounded by $`O(L^2)`$. At tolerance $`\epsilon m`$ with $`\epsilon=d^{-1/10}`$, Hoeffding gives error $`\exp[-\Omega(n\epsilon^2 m^2/L^4)]`$. This exponent dominates $`L+\log(nd)`$: if $`b\ge\log n`$, use $`n\epsilon^2/b^3\ge d^{7/15}`$ for large $`d`$, since already $`n\ge d^{5/3}`$ and $`b\le d^{1/3}`$ suffice for this estimate. If $`b\le\log n`$, use $`n\epsilon^2/(\log n)^5\to\infty`$. Conditioning and multiplication by the correction weight therefore still leave negligible error. On good profiles the correction differs from its value at $`V_\ell`$ by a relative $`o(1)`$. Summing the profile formula gives

$$
a_k=\frac{\binom n\ell^d}{\binom{nd}{d\ell}}\thinspace
U_\ell\exp\left(-\frac12+\frac{V_\ell}{2m(1-p)}\right)(1+o(1)).
\tag{1}
$$

This is uniform on bounded available lattice shifts, including saturation.

## Scalar limits and stability at quota shifts

The log of the binomial prefactor in (1) has first difference $`-d/(2\ell)+o(1)`$, uniformly at bounded shifts. Indeed the exact difference is

$$
\sum_{i=1}^d\log\frac{\ell+i/d}{\ell+1}
+\sum_{i=1}^d\log\frac{n-\ell}{n-\ell-(i-1)/d}.
$$

The first sum equals $`-(d-1)/(2(\ell+1))+O(d/\ell^2)`$ and the second is $`O(d/n)`$. Its second difference is consequently $`o(1)`$.

The candidate law is log-concave relative both to the binomial law of mean $`m`$ and, after subtracting $`c`$, to the geometric law of mean $`h`$. In each case the ratio is log-concave and the masses and means agree. The signed mass difference is positive on one interval and nonpositive outside; subtracting the chord of a convex function across that interval proves convex-order domination. Thus

$$
V_\ell\le m(1-m/d)\le m,\qquad V_\ell\le h(1+h).
\tag{2}
$$

For a log-concave integer law of variance $`V`$, the absolute third centered moment is at most $`C V(1+\sqrt V)`$. For $`V\ge1`$ this is the modal tail bound in the [repository lattice local limit lemma](https://github.com/ProgramComputer/open-math-research/blob/605cc467a5be93a8408519da331e46f1008df96e/topics/balanced-arrays/dense-regime/uniform-lattice-lemma.md). For $`0<V<1`$, a mode $`s_0`$ has mass $`p_{s_0}\ge c_0`$ by Chebyshev. In either direction, pad the law by zeros and let $`J`$ be the first distance where its mass is at most $`p_{s_0}/2`$. The distance is bounded by $`1+2/p_{s_0}`$. Up to $`J`$ the off-mode masses are bounded by the respective adjacent mass. Beyond $`J`$, log-concavity bounds them by the adjacent mass times $`2^{-(j-J)/J}`$ at distance $`j`$, with zero when the support ends. Thus every fixed positive moment about $`s_0`$ is $`O(p_{s_0-1}+p_{s_0+1})`$. The independent-copy variance identity gives $`V\ge p_{s_0}(1-p_{s_0})\ge c_0(p_{s_0-1}+p_{s_0+1})`$. Jensen and the triangle inequality therefore give the required third moment about the mean. Consequently, differentiating the variance as a function of the tilt mean gives $`|dV/dm|\le C(1+\sqrt V)`$. By (2), on bounded real quota shifts the variance changes by at most

$$
O((1+\sqrt b)b/d)=o(1).
\tag{3}
$$

Continuity extends the derivative bound to the deterministic endpoint by integrating from the interior. The repository lattice local limit lemma also gives conditioning probability $`(1+o(1))/\sqrt{2\pi nV}`$ at an integer mean when $`V\ge1`$. For $`V<1`$ the modal estimate above, applied to the second moment, gives $`V\le C(p_{s_0-1}+p_{s_0+1})`$. In the independent-copy characteristic identity this adjacent pair gives $`|\phi(t)|\le\exp(-cVt^2)`$ on $`[-\pi,\pi]`$. Fourier inversion centered at the integer mean and rescaled by $`\sqrt{nV}`$ now gives the same local limit whenever $`nV\to\infty`$: the centered third moment is $`O(V)`$, so on each bounded rescaled interval the logarithmic error after multiplication by $`n`$ is $`O((nV)^{-1/2})`$. The modulus bound gives an integrable Gaussian majorant. In particular the local limit holds uniformly whenever $`V`$ is bounded below.

At any interior tilt the scalar exponent $`E(\ell)=n\log G(w_\ell)-d\ell\log w_\ell`$ satisfies

$$
E'=-d\log w_\ell,\qquad E''=-b/V_\ell.
\tag{4}
$$

If $`j/d\to\beta>0`$, then $`h/b\to\beta`$ and $`m/b\to\gamma+\beta`$. Take an unrestricted trial binomial of mean $`c+\beta b/2`$. Its mean exceeds $`c`$ by a fixed positive fraction of its order-$`b`$ mean. Chernoff gives lower-tail probability $`e^{-\Omega(b)}`$ there, so conditioning to be at least $`c`$ changes its mean by $`O(be^{-\Omega(b)})`$. The resulting mean lies below $`m`$. Monotonicity in tilt shows the actual unrestricted mean $`m_0`$ lies between this trial mean and $`m`$, hence also stays a positive order-$`b`$ distance above $`c`$. Chernoff and bounded raw moments then give differences $`O_q(b^q e^{-\Omega(b)})`$ between its unconditional and conditional raw moments of fixed order $`q`$. Since its parameter tends to zero, $`V_\ell\sim m`$. This reasoning applies uniformly at bounded real shifts. By (4) the second difference of $`E`$ tends to $`-1/(\gamma+\beta)`$, and its centered first difference is $`-d\log w_\ell+o(1)`$ since the common limit of $`E''`$ cancels across both halves. The local limit prefactor and the correction in (1) have negligible log differences. Hence, at every fixed offset,

$$
\log\Gamma_{k+i}\longrightarrow\frac1{\gamma+\beta},
\qquad
\log t_k=-d\log w_\ell-\frac d{2\ell}+o(1).
\tag{5}
$$

## Vanishing upper offset and the signs

Now suppose $`j/d\to0`$ and $`\ell/d\to\gamma>0`$. Pass to a further sequence on which $`V_\ell/b`$ has a limit.

If $`V_\ell/b\to v>0`$, (2) implies $`h\gtrsim\sqrt b`$ and hence $`j\gtrsim d/\sqrt b\to\infty`$. All fixed neighboring quotas in both directions are available. By (3), (4), the local limit, and (1), $`\log\Gamma_{k+i}\to1/v`$ at every fixed offset.

If $`V_\ell/b\to0`$ and $`h\ge\eta>0`$, there is a uniform positive lower variance bound. In fact very small variance by Chebyshev forces one integer atom to have mass above $`0.9`$. Its location is a mode. At an interior mode $`s`$, the product of the two adjacent mass ratios is $`s(d-s)/[(s+1)(d-s+1)]\ge1/4`$, incompatible with such a large modal mass. The upper endpoint $`d`$ cannot carry that mass because $`m=O(b)=o(d)`$. At the lower endpoint $`c`$, the first forward ratio $`q`$ is small, and log-concavity gives $`h\le Cq`$ and $`V\ge \Pr(X=c)\Pr(X=c+1)\ge c_1q`$. This proves the lower bound in terms of $`\eta`$. The same reasoning applies at bounded shifts since their means change by $`O(b/d)=o(1)`$. Then (3) makes the local limit prefactors have log differences $`o(1)`$; (4) gives a diverging negative second difference of $`E`$ because $`V=o(b)`$ uniformly over the real shifts. The correction in (1) tends to $`e^{-1/2}`$ throughout. Thus $`\Gamma_k\to\infty`$.

Finally, if $`h\to0`$, put $`e=nh=d(T-k)`$, so $`e\ge d`$ at an internal quota. Apply the [scalar negative-binomial step bound](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/very-tall-upper-quota.md#the-last-od-quotas) to the excess size coefficients $`\binom d{c+s}`$. It yields

$$
\log\frac{U_\ell^2}{U_{\ell-1}U_{\ell+1}}
\ge \frac{d(n-1)}{n+e+d-1}\log(1+d/e)
\ge (1-o(1))\frac{d^2}{e+d}
=(1-o(1))\frac{b}{h+b/d}\longrightarrow\infty.
$$

By (2), the variance at each of the three quotas is $`o(1)`$, since $`b/d\to0`$, including a possible saturated neighbor. The correction in (1) again tends to $`e^{-1/2}`$ at each quota, so $`\Gamma_k\to\infty`$.

In either case of divergence the one-term alternating-tail bounds give $`(-1)^kP(-t_k)>0`$. When the local $`\log\Gamma`$ limit at each fixed offset is $`C>0`$, the normalized magnitude of each fixed offset $`i`$ tends to $`e^{-Ci^2/2}`$. Global strict log-concavity from normalized coefficient curvature makes the magnitudes decrease outwards from the center. The two signed tails can be cut with errors bounded by their first omitted terms; taking the quota limit first and then increasing the cutoff gives the positive normalized limit $`\sum_{i\in\mathbb Z}(-1)^i e^{-Ci^2/2}`$ by Gaussian periodization. The argument works at every perturbed node $`t_ke^{o(1)}`$, because the fixed-offset magnitudes still have the same limits and both first outward ratios stay below one. Taking subsequences in the bounded ranges establishes the claimed strict signs.

## Locating the angular node at positive offset

Let $`v`$ be an occupied tilt, $`X`$ the hole row size at $`w=1/v`$, $`S=d-X`$, $`\mu=\mathbb ES`$, $`y=n\mu/d`$ and $`\phi=\pi/d`$. Write $`a_X=X(d-X)/[d(d-1)]`$, and use the phase

$$
\Psi(v)=n\arg H_{\rm occ}(ve^{i\phi})-\frac{d-1}{2}\arg a_\phi,\qquad
a_\phi=\frac{\mathbb E[a_Xe^{-i\phi X}]}{\mathbb E e^{-i\phi X}} .
$$

The positive sums lie in the sector $`[0,r\phi]`$ in the occupied convention, so the continuous arguments exist. The phase has limits $`-(d-1)\phi/2`$ as $`v\downarrow0`$ and $`T\pi`$ as $`v\to\infty`$, giving ordered first crossings at internal targets.

Assume $`j/d\to\beta>0`$. At any crossing $`\Psi=k\pi`$, the preliminary bound

$$
|\Psi/\pi-y|\le C d+C(T-y)/\sqrt d
\tag{6}
$$

gives $`T-y=O(d)`$ since $`T-k=O(d)`$. For (6), the variance is at most $`\min(d/4,h(1+h))\le C\sqrt d\,h`$ by the two convex-order comparisons above, which hold at all tilts. Centering $`S`$ gives a row-angle error $`O(V/d^2)`$ using $`|S-\mu|\le d`$ and the cubic sine remainder. The determinant phase term is bounded by $`O(d)`$ by its sector. Thus at the crossing $`m(v)=d-\mu=c+d(T-y)/n=O(b)`$, while $`m(v)\ge1`$.

The raw hole moments satisfy $`\mathbb E X^q=O_q(m(v)^q)`$ by the factorial ratio and tail argument even before a separation between $`c`$ and the unrestricted mean is known. Consequently $`\mathbb E a_X=m(v)/d+O(m(v)^2/d^2)\ge m(v)/(2d)`$. Comparing the complex weighted means to their values at zero gives $`\arg a_\phi=O(\phi m(v))`$, so the determinant phase term is $`O(b)=o(d)`$. The centered row argument is $`(d-m(v))\phi+O(\phi^3 m(v)^3)`$, and the error multiplied by $`n`$ is $`O(b^2/d)=o(1)`$. It follows that $`y=k+o(d)`$ and hence $`h(v)/b=(T-y)/d\to\beta`$. This justifies applying the trial-binomial argument at every crossing and gives $`V(v)/m(v)\to1`$ there.

Now the first-order curvature-angle coefficient is $`-\mathrm{Cov}(a_X,X)/\mathbb E a_X=-V(v)/m(v)+O(m(v)^2/d)`$. The normalized quadratic remainder in the argument is $`O(\phi^2m(v)^2)=o(\phi)`$. Thus

$$
\arg a_\phi=-\frac{V(v)}{m(v)}\phi+o(\phi),
\qquad
\Psi(v)/\pi=y(v)+1/2+o(1)
$$

at each crossing. In particular $`y(v)=k-1/2+o(1)`$. At $`v_{\rm geo}=t_k^{1/d}`$, (5) shifts its log tilt from $`-\log w_\ell`$ by $`-1/(2\ell)+o(1/d)`$. On this short interval $`m/b\to\gamma+\beta`$ uniformly, since changing the tilt by $`O(1/d)`$ changes $`m`$ by $`O(b/d)`$ using $`V\le m`$. As $`dy/d(d\log v)=V/b\to\gamma+\beta`$, this amounts to the same shift $`y(v_{\rm geo})=k-1/2+o(1)`$. The function $`y`$ is strictly increasing in the log tilt. Throughout the interval between any crossing and $`v_{\rm geo}`$, its values lie between the two endpoint values and therefore $`h/b\to\beta`$ uniformly. The derivative $`dy/d(d\log v)`$ is bounded below there, proving $`\log(v_k^d/t_k)=o(1)`$ even for the first crossing. The geometric sign is stable under that perturbation, as above.

At a join with $`j/d\to\beta>0`$, adjacent geometric log radii differ by $`(\log\Gamma_k+\log\Gamma_{k+1})/2\to1/(\gamma+\beta)>0`$. Replacing the last inner point by the first angular crossing changes its log radius by $`o(1)`$, preserving order. The note supplies only this upper band and overlap; angular and lower-quota signs in the remaining ranges require their separate estimates.
