# Uniform interior saddle at the quadratic row scale

Let $`d\to\infty`$, $`1\le r<d`$, and $`v>0`$. Let $`S`$ have probabilities proportional to $`\binom ds v^s`$ on $`0\le s\le r`$, and given $`S`$, let $`I`$ be a uniformly random $`S`$-subset of $`[d]`$. Put $`H=\sum_{s\le r}\binom ds v^s`$, $`\mu=\mathbb ES`$, $`h=r-\mu`$, $`V=\mathrm{Var}(S)`$, $`\phi(t)=\mathbb E e^{itS}`$, and $`R(\theta)=\mathbb E e^{i\sum_{j\in I}\theta_j}`$. Define $`a_s=s(d-s)/[d(d-1)]`$, $`a=\mathbb E a_S`$, $`a(t)=\mathbb E[a_S e^{itS}]/\phi(t)`$ and $`t_*=\pi/d`$. Fix $`h_0>0`$. Uniformly for $`\mu\ge1/10`$, $`h\ge h_0`$, and $`n/d^2\to\infty`$, one has

$$
\frac{P_n^{(r,d)}(-v^d)}{H^n}
=\frac{2}{\sqrt d}(2\pi n)^{-(d-1)/2}\thinspace
\mathrm{Re}\negthinspace \left(\phi(t_{\ast})^n a(t_{\ast})^{-(d-1)/2}\right)
+o\negthinspace \left(\frac{|\phi(t_{\ast})|^n}{\sqrt d}(2\pi n|a(t_{\ast})|)^{-(d-1)/2}\right).
$$

The error is measured on the size of a single saddle. Constants may depend on $`h_0`$. This is an interior statement; no endpoint or root count follows directly.

## Uniform moments and diagonal loss

Use the success/failure bias comparison and modal-atom proofs in [the fixed-cutoff saddle note](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/very-tall-interior-saddle.md). They give $`c_{h_0}\le V\le\mu(1-\mu/d)\le d/4`$ and $`a\ge \max(V/d,1/(11d))`$.

The symmetric law of $`\Delta=S-S'`$ for an independent copy $`S'`$ is log-concave, by convolution. We make the tail bound uniform in $`V`$. Its one-sided survival $`T(j)=\mathbb P(\Delta\ge j)`$ for integers $`j\ge0`$ is log-concave: $`T(j+1)/T(j)`$ is the weighted average of successive mass ratios at indices at least $`j`$, and those ratios decrease in the index. Omitting the first index decreases this average. Thus $`T(j+m)/T(j)\le T(m)/T(0)`$. With $`m=\lceil 4\sqrt{1+V}\rceil`$, Chebyshev and $`T(0)\ge1/2`$ give $`T(m)/T(0)\le1/4`$. Iterating and using symmetry yields $`\mathbb P(|\Delta|>x)\le C e^{-c x/\sqrt{1+V}}`$. In particular $`\mathbb E\Delta^4\le C(1+V)^2\le C_{h_0}V(1+V)`$. Jensen conditional on $`S`$ gives $`\mathbb E|S-\mu|^j\le\mathbb E|\Delta|^j`$ for all $`j\ge1`$. The tail contribution to $`\mathbb E\Delta^2`$ beyond $`L\sqrt{1+V}`$ can be made less than any specified fraction of $`V`$ by taking $`L`$ large in terms of $`h_0`$.

As in the [fixed-cutoff note](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/very-tall-interior-saddle.md), decompose the symmetric decreasing law of $`\Delta`$ into uniforms on integer intervals $`[-j,j]`$. Uniforms with $`j>2L\sqrt{1+V}`$ contribute only a small fraction of the second moment, since a constant fraction of their second moment lies past $`L\sqrt{1+V}`$. The cosine loss of each uniform is at least $`c\min(j^2t^2,1)`$ for $`|t|\le\pi`$. Thus

$$
1-|\phi(t)|^2\ge c_{h_0}V\min(t^2,(1+V)^{-1}).
$$

For $`0\le t\le t_0=c_0/\sqrt{1+V}`$, differentiating the cosine loss gives $`\mathbb E[\Delta\sin(t\Delta)]\ge 2Vt-\mathbb E[\Delta^4]t^3/6\ge Vt`$ for a sufficiently small $`c_0`$ depending on $`h_0`$. Also $`1-|\phi(t)|^2\le Vt^2\le c_0^2`$. In particular for $`t_*\le |t|\le t_0`$,

$$
|\phi(t)|/|\phi(t_{\ast})|\le\exp[-c V(t^2-t_{\ast}^2)].
$$

At $`|t|\ge t_0`$ there is a constant modulus gap from one, depending on $`h_0`$.

## Charts and expansion

The negative evaluation is the Haar integral of $`R(\theta)^n`$ on the translated torus $`\sum_j\theta_j=\pi\bmod 2\pi`$. Its Euclidean covolume is $`\sqrt d(2\pi)^{d-1}`$ by the basis $`2\pi(e_j-e_d)`$ of its period lattice. Use disjoint charts at the $`d`$ diagonal angles $`t=(2j+1)\pi/d\bmod 2\pi`$, with $`y\in \mathbf1^\perp`$ and $`\|y\|\le\eta`$ for a small fixed $`\eta>0`$. Disjointness follows because two distinct diagonal points differ modulo $`2\pi`$ by a phase vector whose zero-sum lift has at least two coordinates differing by $`2\pi`$. An overlap would give a lift of norm at most $`2\eta`$. Using the nearest-anchor chord argument from the [fixed-cutoff note](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/very-tall-interior-saddle.md), the complement of the charts has $`D_z=\sum_j|e^{i\theta_j}-d^{-1}\sum_i e^{i\theta_i}|^2\ge c\eta^2`$.

The disjoint-pair bound of that note gives a fixed-size modulus loss at least $`c\min(a_sD_z,1)`$, since $`\min(s,d-s)/d`$ is comparable to $`a_s`$ for every size. The $`O(1/d)`$ Lipschitz bound of $`a_s`$ gives $`\mathbb E a_S^2\le a^2+C V/d^2\le C'a^2`$ by $`a\ge \max(V/d,1/(11d))`$. Cauchy–Schwarz yields $`\mathbb P(a_S\ge a/2)\ge1/(4C')`$. Averaging the fixed-size modulus losses therefore gives
$`|R|\le \exp[-c\min(aD_z,1)]`$.

Where $`aD_z>1`$, the bound $`e^{-cn}`$ is negligible relative to the principal size, since $`n\gg d\log n`$ and $`\log(1/|\phi(t_*)|)=O(V/d^2)=o(1)`$. On the remainder of the chart complement split the bound $`e^{-cnaD_z}`$ into two factors, using $`D_z\ge c\eta^2`$ in one. For the other partition by a closest anchor $`j`$ to the mean phase. Since $`\sum_i|z_i-z_j|^2\le2D_z`$, in principal relative angles $`u_i=\arg(z_i/z_j)`$ it is bounded by $`e^{-c'na\sum_{i\ne j}u_i^2}`$. The pushforward of Haar on the translated torus by relative angles at a fixed anchor is normalized Haar on the full $`(d-1)`$-torus. Indeed this map is the restriction of a continuous group homomorphism up to translation, and is surjective because $`d\theta_j=\pi-\sum_{i\ne j}u_i\bmod2\pi`$ has a solution for any angles. Integrating the bound for each of the $`d`$ anchors shows that this part is at most
$`d(C/\sqrt{na})^{d-1}e^{-c_\eta na}`$.
Dividing by the principal Gaussian size costs $`e^{O(d)}`$ and the principal radial modulus costs $`e^{O(nV/d^2)}\le e^{O(na/d)}`$. The relative error thus tends to zero when $`n/d^2\to\infty`$, because $`na\ge n/(11d)\gg d`$.

Write $`Q_j=\sum_i y_i^j`$ and $`L=\sum_{j\in I}y_j`$. Conditional on $`S=s`$, the first moment vanishes, the second is $`a_sQ_2`$, and the third is $`\gamma_s Q_3`$, where $`\gamma_s=a_s(d-2s)/(d-2)`$. The fourth-moment identity in the [fixed-cutoff note](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/very-tall-interior-saddle.md), applied to $`m=\min(s,d-s)`$ and using inclusion $`p_1\le Ca_s`$, $`p_2\le C a_s^2`$, gives $`\mathbb E[L^4\mid S=s]\le C(a_sQ_4+a_s^2 Q_2^2)`$. The functions $`a_s,\gamma_s`$ are $`O(1/d)`$-Lipschitz on $`[0,d]`$ for large $`d`$, and $`|\gamma_s|\le Ca_s`$. Therefore $`\mathbb E a_S^2\le a^2+C V/d^2\le C a^2`$, by combining $`a\ge c/d`$ and $`a\ge V/d`$. Centering $`Z=S-\mu`$, the same Lipschitz estimate gives

$$
\mathbb E[a_S|Z|]\le Ca\sqrt{1+V},\qquad
\mathbb E[a_S Z^2]\le C a(1+V).
$$

Indeed bound $`a_S\le a_\mu+C|Z|/d`$, use $`a_\mu=a+V/[d(d-1)]`$, and use $`\mathbb E|Z|^3\le(\mathbb EZ^2\,\mathbb EZ^4)^{1/2}\le C V\sqrt{1+V}`$. Terms containing $`V/d`$ are bounded by $`a`$.

Throughout each chart, $`|R(t\mathbf1+y)-\phi(t)|\le aQ_2/2`$, by centering the linear term. For $`|t|\ge t_0`$, choosing $`\eta`$ small enough makes this perturbation less than half the uniform diagonal gap. Their normalized integral is negligible by $`n\gg d\log n`$.

Inside a near chart $`|t|\le t_0`$, set $`\gamma(t)=\mathbb E[\gamma_S e^{itS}]/\phi(t)`$. The preceding weighted moments yield $`|\gamma(t)|\le Ca`$, $`|\mathrm{Im}\,\gamma(t)|\le Ca\sqrt{1+V}|t|`$, and

$$
|\mathrm{Re}\thinspace a(t)-a|\le Ca(1+V)t^2,\qquad |\mathrm{Im}\thinspace a(t)|\le Ca\sqrt{1+V}|t|.
$$

For the real bound, center the numerator and denominator at $`\mu`$, use the cosine quadratic bound for their real perturbations, and use the sine linear bounds for imaginary parts when taking the quotient. The denominator modulus is uniformly close to one for small fixed $`c_0`$. Choose $`c_0`$ small enough that $`\alpha_t=\mathrm{Re}\,a(t)\asymp a`$. Then Taylor and expansion of the logarithm on $`\|y\|\le\eta`$ give

$$
\log(R(t\mathbf1+y)/\phi(t))
=-\tfrac12a(t)Q_2-\tfrac i6\gamma(t)Q_3+O(aQ_4+a^2Q_2^2).
$$

The log-square term is $`O(a^2 Q_2^2)`$ because $`|R-\phi|\le aQ_2/2`$.

## Uniform chart integrals

Write $`I_0=(2\pi/(na))^{(d-1)/2}`$ for the unnormalized Gaussian integral. Taking moduli in a near chart leaves a Gaussian of coefficient $`n\alpha_t`$ and a positive exponential whose exponent is bounded by

$$
Cna\left(\sqrt{1+V}|t|\sum_j|y_j|^3+Q_4\right)+Cna^2Q_2^2.
$$

By Cauchy–Schwarz it suffices to bound the expectations of the separated exponentials doubled. For the coordinate terms use $`y_i=Z_i-\bar Z`$ with independent $`N(0,\sigma^2)`$, $`\sigma^2=(n\alpha_t)^{-1}`$. Restrict additionally to $`|\bar Z|\le\eta`$, an independent event of probability tending to one. On the chart this forces $`|Z_i|\le2\eta`$ and $`\sum|y_i|^j\le2^j\sum|Z_i|^j`$. For each one-dimensional integral, $`\exp(C'\sigma^{-2}[\sqrt{1+V}|t||Z_i|^3+Z_i^4])`$ on this interval has expectation at most $`1+C''(\sqrt{1+V}|t|\sigma+\sigma^2)`$. This follows from $`e^u-1\le u e^u`$ and the doubled-variance Gaussian after choosing $`\eta`$ small, using $`\sqrt{1+V}|t|\le c_0`$. Multiplying gives a constant times $`\exp(Cd[\sqrt{1+V}|t|\sigma+\sigma^2])`$, at most $`\exp(O(d(1+V)t^2+d/(na)+1))`$ by Young's inequality.

For the radial term, $`Q_2/\sigma^2`$ has the $`\chi^2_{d-1}`$ law. On $`Q_2\le Ld/(na)`$ the doubled radial exponent is $`O_L(d^2/n)=o(1)`$. Above that threshold but with $`\|y\|\le\eta`$, absorb the doubled radial exponent using $`Ca\eta^2`$ as a small relative weakening of the Gaussian. The Gaussian normalization cost is at most $`e^{C_1d}`$ and the weakened tail is at most $`e^{-cLd}`$ for large fixed $`L`$ by the $`\chi^2`$ exponential moment. This contribution tends to zero for sufficiently large $`L`$.

Finally the ratio between Gaussian integral at $`\alpha_t`$ and $`I_0`$ is at most $`\exp(Cd(1+V)t^2)`$. Thus each near chart integral in modulus is at most

$$
C I_0|\phi(t)|^n\exp(Cd(1+V)t^2).
$$

The principal Gaussian factor in modulus is comparable to $`I_0`$, since $`|\mathrm{Re}\,a(t_*)/a-1|=O((1+V)/d^2)`$ and $`\mathrm{Im}\,a(t_*)/a=O(\sqrt{1+V}/d)`$. For $`|t|=j\pi/d`$ at odd $`j\ge3`$, combine the last bound with the radial comparison. Since $`nV\gg d(1+V)`$, the relative bound is $`\exp(-c n V(j^2-1)/d^2)`$ up to an absolute constant. Summing over these phases gives $`o(1)`$.

At the principal chart the same exponential expectation bounds are uniform constants. For a real Gaussian of coefficient $`n\alpha_{t_*}`$ on the hyperplane, Wick and the zero sum give $`\|Q_3\|_2=O(\sqrt d\,\sigma^3)`$, as in the [fixed-cap saddle calculations](https://github.com/ProgramComputer/open-math-research/blob/f7e10f84dd21fec44ca58c60bae0879d12ebd89b/topics/balanced-arrays/fixed-cap/tall-sparse-transverse-saddle.md). The triangle inequality for moments gives $`\|Q_4\|_2=O(d\sigma^4)`$ and $`\|Q_2^2\|_2=O(d^2\sigma^4)`$. Thus the $`L^2`$ size of the log correction to the full complex quadratic, multiplied by $`n`$, is $`O(d/\sqrt n+d^2/n)`$, using $`a\ge1/(11d)`$. Apply Cauchy–Schwarz to $`|e^B-1|\le|B|e^{(\mathrm{Re} B)_+}`$. The Gaussian tail beyond $`\|y\|=\eta`$ is negligible since $`na\gg d`$. The real Gaussian normalization and absolute complex Gaussian normalization are comparable by the principal estimates above. This proves the principal local relative $`o(1)`$ and the two-saddle formula after dividing by the torus covolume.


## Quantitative consequence for a large fixed quadratic constant

With $`h_0`$ fixed, the proof also works for sign testing uniformly at $`n\ge C_*d^2`$ with $`C_*`$ sufficiently large depending on $`h_0`$. Relative to one saddle the local error is $`O_{h_0}(C_*^{-1/2}+C_*^{-1})`$ for large $`d`$, and the total near nonprincipal error is $`O_{h_0}(e^{-c_{h_0}C_*})`$, by the summable bound in odd $`j`$. In the radial $`\chi^2`$ estimate the central region contributes $`e^{O_{h_0,L}(1/C_*)}`$, still a bounded factor. Both far errors tend to zero as $`d\to\infty`$ for sufficiently large fixed $`C_*`$, since $`na\ge C_*d/11`$. Thus the absolute error on one-saddle scale can be made as small as desired by increasing $`C_*`$. An asymptotic relative $`o(1)`$ is asserted only when $`n/d^2\to\infty`$.
