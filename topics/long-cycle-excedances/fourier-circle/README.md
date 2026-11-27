# A common-circle comparison without a height loss

**Theorem.** For every $`n\ge10{,}000`$ and $`3\le k\le n`$ with $`n/k\ge44`$, the nonzero roots of the minimum-cycle-length excedance rows at $`n`$ and $`n+1`$ are simple, negative and strictly interlace. This is a partial theorem for Alexandersson's conjecture about the actual consecutive rows. Formal coverage is 🟨 Partial · Lean 4. Lean checks the signed Fourier coefficient identity under its differential hypotheses and the integral bound for products of infinite complex pole sums with summable weights. The individual pole factor is exact. The differential equations for the original rows and their quantitative pole-weight bounds remain open formal obligations. [Formal statements and verification](../lean/fourier-circle/README.md)

Use the notation and coefficient identity of the [wider-circle proof](../radial-taylor.md). Thus $`t=-e^{-s}`$, $`w_p=s+ip\pi`$ for odd $`p`$, $`r=|w_1|`$, $`S=\pi/r=\sin\theta`$, $`C=\cos\theta`$, and $`z_p=r/w_p`$. On the first half-axis take $`s\ge0`$ and write $`T_s=e^G`$, where $`G`$ is the Taylor polynomial of degree $`(k-1)`$ for $`L(w)=\log((1+e^{w-s})/(1+e^{-s}))`$. We assume $`nS^2\ge1`$ throughout the contour estimates. Reuse the [phase join](../lower-circle/README.md) at $`\theta_*=(\lfloor7\sqrt n/20\rfloor+5/6)\pi/n`$ and the established exterior-root result.

## Two Fourier integrations

Let $`f(w)=e^{G(w)}/(1+e^{w-s})`$. Fix a circle $`w=Re^{i\varphi}`$ avoiding every pole. Write $`f_j`$ for the Fourier coefficient of $`f(Re^{i\varphi})`$ at index $`j`$, using the factor $`e^{-ij\varphi}`$ and normalized angular measure. Put

$$
 a_p=R^k/w_p^{k-1},\qquad
 D(\varphi)=\sum_p\frac{a_p}{w_p-w},\qquad
 K(p)=|R^2-|w_p|^2|^{-1/2}.
$$

The Eulerian simple-pole formula for $`L'`$ gives the exact Taylor remainder $`G'-L'=\sum_p(w/w_p)^{k-1}/(w_p-w)`$. It follows first for $`|w|<r`$ from the Taylor coefficients of the simple poles and then throughout the pole-free domain by absolute convergence and analytic continuation. Consequently $`\partial_\varphi f=i e^{ik\varphi}fD`$. For $`j>k`$ the first integration by parts gives $`j f_j=\widehat{fD}(j-k)`$. Before taking absolute values, integrate by parts at frequency $`j-k`$. Since $`\Vert (w_p-w)^{-1}\Vert _2=K(p)`$ and $`\Vert (w_p-w)^{-2}\Vert _1=K(p)^2`$, the Cauchy–Schwarz inequality gives

$$
 |f_j|\le\frac{\Vert f\Vert _\infty}{j(j-k)}(S_0^2+R T_0),
 \qquad
 S_i=\sum_p |a_p|\cdot |p|^i K(p),\quad
 T_i=\sum_p |a_p|\cdot |p|^i K(p)^2 .
$$

The two kernel integrals follow by the geometric-series formula on the circle about the origin, with the powers reversed when the pole is enclosed. These formulas require only $`R\ne|w_p|`$.

For the consecutive-row contrast use the exact identity

$$
 \frac{r/w-C}{w_p-w}
 =\frac{z_p-C}{w_p-w}+\frac{z_p}{w}.
$$

In fact $`n((r/R)f_{n+1}-C f_n)=\widehat{f(r/w-C)D}(n-k)-(r/R)f_{n+1}`$ by the first integrations. Integrating the first kernel term at $`n-k`$, bounding $`|z_p-C|\le |p|S`$, and evaluating the term proportional to $`1/w`$ gives

$$
 \left|(r/R)f_{n+1}-C f_n\right|
 \le\frac{\Vert f\Vert _\infty S}{n(n-k)}(S_0 S_1+R T_1)
 +\frac{|\sum_p a_pz_p|}{nR}|f_{n+1-k}|
 +\frac{r}{nR}|f_{n+1}|.
$$

All the sums used in these two integrations converge absolutely for the thresholds below. Both the old circle error and the contrast circle error are obtained by multiplying the corresponding Fourier expression by $`r(r/R)^n/(2|T_s(w_1)|)`$, apart from the harmless factor $`r/R`$ when normalizing the following row alone.

## Bounding the numerator and denominator at the same angle

For $`r\le|w|\le(1+1/k)r`$, set $`\widehat w=(1-1/k)r w/|w|`$. The Taylor contraction below bounds

$$
 |G(w)-L(\widehat w)|+|G(w_1)-L((1-1/k)w_1)|<M_k ,
$$

where $`M_k=30`$ for $`k\ge100`$, $`32`$ for $`50\le k<100`$, and $`60`$ for $`10\le k<50`$.

For small $`s\le\beta\sqrt k`$, use the wider-circle pole bound with $`U=1/(S\sqrt k)`$. Convexity of $`\sinh`$, $`(1+1/k)^j\le e^{j/k}`$, and $`(1-1/k)^j\ge e^{-j/k}-j/[k(k-1)]`$ give

$$
 \frac{(1+1/k)^j-(1-1/k)^j}{j}
 \le\frac{2\sinh(1)+1/(k-1)}{k},\qquad 1\le j<k .
$$

Use $`1/k`$ for the analogous linearized change from the principal radius and $`1/[e(1-1/(2k))]`$ for the two contracted tails. The small-$`s`$ sum is bounded by $`12/k+(a+1)(2+4.5U)+2b(2+2.25U)`$ with $`a=2\sinh(1)+1/(k-1)`$ and $`b=1/[e(1-1/(2k))]`$. The checked splits use $`\beta=4,4,8`$ for the three ranges, respectively.

For $`s>\beta\sqrt k`$, use the positive Poisson radial sums in the wider-circle proof. Here $`r-s<ds/k`$, $`r/s<q`$, and $`R_*-s<(d+q)s/k`$ for $`R_*=(1+1/k)r`$. Split the Poisson frequencies at $`a=u k/s`$ and use the lower-tail exponent $`v`$ on the remaining frequencies. Below the split the radial costs at $`|w|`$ and $`w_1`$ are bounded by $`2qu e^{(d+q)u}`$ and $`qu e^{du}`$. Above it the analogous costs are at most $`2q/(k(v-(d+q)/k))`$ and $`q/(k(v-d/k))`$, by a geometric sum. Each contracted Taylor tail is bounded by $`(1+\log k)e^{-k/6}+2/(1-d)`$. The exact constants used are as follows.

| Minimum $`k`$ | $`\beta`$ | $`d`$ | $`q`$ | $`u`$ | $`v`$ |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 100 | 4 | $`.31`$ | $`1.004`$ | $`5/4`$ | $`1/50`$ |
| 50 | 4 | $`.31`$ | $`1.007`$ | $`7/5`$ | $`9/200`$ |
| 10 | 8 | $`.078`$ | $`1.008`$ | $`2`$ | $`1/8`$ |

For $`k\ge100`$ we use the actual quotient. If the circle is at distance at least $`\delta`$ from all poles and $`\Delta=|w-\widehat w|\le 2r/k`$, then

$$
 \frac{|1+e^{\widehat w-s}|}{|1+e^{w-s}|}\le1+4\Delta/\delta .
$$

Indeed if $`\Re w\ge0`$, divide the difference of the exponentials by $`e^{w-s}`$, and use $`|e^{\widehat w-w}-1|\le\Delta`$ together with the inverse denominator bound for $`e^{s-w}`$. If $`\Re w\le0`$, directly bound the exponential difference by $`\Delta`$ since the two real parts after subtracting $`s`$ are nonpositive. The same bound holds with $`2`$ in place of $`4`$ if $`\delta\le.03`$. To see this write the squared denominator as $`4e^u(\sinh^2(u/2)+\sin^2(y/2))`$, with $`u=\Re(w-s)`$ and $`y`$ the distance of its imaginary part from an odd multiple of $`\pi`$. For $`|u|\le .4`$ this gives modulus at least $`2e^{-.2}\sqrt{u^2+y^2}/\pi\ge\delta/2`$. For larger $`|u|`$ the modulus is at least $`1-e^{-.4}`$. The same argument works for the negative exponent.

The contraction then gives

$$
 \frac{r\Vert f\Vert _\infty}{|T_s(w_1)|}
 \le\frac{r e^{30}(1+4\Delta/\delta)}
              {|1-e^{-(s+i\pi)/k}|},
$$

with the same improvement in the coefficient of $`\Delta/\delta`$ where applicable.

## Quantitative circle choice for $`k\ge100`$

Write $`x=n/k`$ and let $`a=k(R^2-r^2)/r^2`$ be the squared shift. The projected positive pole radii have positions $`kS^2(p^2-1)`$ for odd $`p\ge1`$. Adjacent nonprincipal positions have gap at least $`16/x`$. Throughout $`R/r<1.01`$, and $`|a_p|\le 3r|z_p|^{k-1}`$.

For $`48\le x\le100`$, choose $`a\in[1.92,2]`$ at projected distance at least $`.039`$ from the poles. At most one nonprincipal position can lie in the enlarged interval and its excluded subinterval has length less than $`.08`$. Set $`c=.039`$. This gives $`K(p)\le(1/\sqrt c)\sqrt k/r<5.07\sqrt k/r`$ and physical distance at least $`cr/(4k)`$ from every pole, by subtraction of squares for $`|w_p|\le2r`$ and direct comparison for the others. The factor $`(r/R)^n`$ is at most $`e^{-.95x}`$. If $`u=s/k`$ and $`v=\pi/k`$, use $`(1-e^{-u})\ge u/(1+u)`$ and $`2e^{-u/2}\sin(v/2)\ge e^{-u/2}v(1-v^2/24)`$ in the squared modulus to obtain $`|1-e^{-u-iv}|\ge r/(5k)`$ since $`r/k\le\pi`$. Thus $`r\Vert f\Vert _\infty/|T_s(w_1)|<4110 k e^{30}`$.

The established pole moments with $`\nu=(k-1)S^2\ge.99/100`$ give $`\sum|z_p|^{k-1}<23`$ and $`\sum|p||z_p|^{k-1}<326`$. Therefore $`(S_0^2+RT_0)/k<125000`$. The effective contrast constant is below $`1860000`$: the first term gives $`(S_0 S_1+RT_1)/k`$, the correction from $`f_{n+1-k}`$ costs at most $`.69(48/46)\cdot125000`$, and the last correction costs at most $`.01\cdot125000`$. These bounds use $`nS\ge100`$ and $`(n(n-k))/((n+1-k)(n+1-2k))\le x/(x-2)`$. Consequently the old circle error is below $`.02`$ and the contrast error below $`.29 S`$, by substituting $`x=48`$ into $`4110 e^{30-.95x}/(2x(x-1))`$ times the respective constants.

For $`44\le x\le48`$ keep the same projected gap, using physical distance $`\delta=4cr/(9k)`$ by the squared-radius gap for $`|w_p|\le1.1r`$ and direct comparison otherwise. This $`\delta`$ is below $`.03`$. Use $`r/k\le .48\pi`$ to get principal contraction modulus at least $`r/(3k)`$ in the same two squares. The quotient bound becomes $`696 k e^{30}`$. Here the zeroth pole moment is below $`16`$. The first moment is below $`74`$: for $`|p|\ge3`$ Bernoulli at exponent $`(k-1)/96`$ gives the envelope $`(1+\nu p^2/108)^{-48}`$. For $`g(u)=u(1+\nu u^2/108)^{-48}`$ the odd-lattice contribution is at most $`2\max g+\int_0^\infty g`$, by unimodality and mesh two. These terms are at most $`2\sqrt{9/(8\nu)}`$ and $`108/(94\nu)`$. Include the two principal poles and take $`\nu\ge.99/48`$. Repeating the displayed Fourier estimates gives old constant $`61000`$ and contrast constant $`313000`$; the two smaller corrections now cost at most $`(.48(44/42)+.01)61000`$. Evaluate $`696 e^{30-.95x}/(2x(x-1))`$ at $`x=44`$ to get circle errors below $`.09`$ and $`.44 S`$.

For $`x\ge100`$, use $`a\in[1.8,2]`$ with projected gap at least $`1/x`$. The enlarged interval of width $`.2+2/x`$ contains at most $`9/8+x/80`$ positions, with total excluded length at most $`9/(4x)+1/40<.2`$. The physical gap may be taken as $`r/(4kx)`$. We have $`|1-e^{-u-iv}|\ge (r/k)/(2+r/k)`$: if $`s\ge r/2`$ use $`1-e^{-u}\ge u/(1+u)`$, and otherwise $`s<\pi/\sqrt3<2`$ and $`\pi\ge\sqrt3 r/2`$, so the sine contribution is at least $`.8 r/k`$. The quotient bound is therefore $`2 k x^2 e^{30}`$, since $`r/k\le\pi x/100`$ and the denominator ratio is at most $`1+32x`$. Also $`(r/R)^n\le e^{-.89x}`$. Use pole moments $`3\sqrt x,4x`$ from $`\nu\ge.99/x`$ and kernel bound $`\sqrt{kx}/r`$. They give $`S_0\le9x\sqrt k`$, $`S_1\le12x^{3/2}\sqrt k`$, $`(S_0^2+RT_0)/k\le82 x^2`$ and $`(S_0 S_1+RT_1)/k\le110 x^{5/2}`$. The remaining contrast terms add at most $`77x^2`$ to the last constant. Both normalized circle errors, with the contrast divided by $`S`$, are at most

$$
 122 x^{5/2} e^{30-.89 x}<.01 .
$$

The endpoint check is at $`x=100`$, and this function decreases thereafter.

## Small thresholds and the enclosed residues

For $`10\le k<100`$, the direct Cauchy estimate with $`R/r\in[1+.9/k,1+1/k]`$ has normalized error at most $`1300 n^2e^{M_k-\eta x}`$, by the wider-circle argument using the Taylor contractions proved above. Here $`\eta=.89`$ for $`50\le k<100`$ and $`.85`$ for $`10\le k<50`$. These give error below $`S/100`$ from $`n=10{,}000`$ in both ranges: $`\eta n/k>M_k+13+2.5\log n`$ at that height for the largest $`k`$ of each range, and the difference increases thereafter. For $`4\le k\le9`$, the first variable contour in the [lower-height proof](../lower-circle/README.md) already passes its circle-error bound from $`n=10{,}000`$ with $`k\le9`$. The established all-size result gives $`k=3`$.

For $`k\ge100`$ and the Fourier circles, a nonprincipal enclosed pole forces $`s>6.27\sqrt k`$ since $`R^2-r^2\le2r^2/k`$. On each enclosed pole segment, $`k\log(|w|/s)<1.126`$. The gamma density of shape $`k`$ at the real mesh $`bs`$, $`b\ge1`$, has sum below $`1.05`$ times its maximum. Indeed let $`m=k-1`$ be the mode. Relative to the maximum, points at distance $`y`$ from $`m`$ have density at most $`\exp[-y^2/(2(m+y))]`$ on either side, using the log derivative of the density. Apart from one closest point, mesh points occur in pairs with distances at least $`(j-1/2)s`$ for $`j\ge1`$. The exponents are at least $`3.7(2j-1)`$ for $`s>6.27\sqrt k`$ and $`k\ge100`$. Their geometric sum is below $`.05`$. Thus the gamma formula for $`H'`$ gives $`\pi|H'|<.42`$ throughout the segments. The same estimate applies to the principal pole segment at the outer phase point $`s_*>2\sqrt n`$. For enclosed poles, $`(p^2-1)S^2\le2/k`$ gives decay $`|z_p|^n\le e^{-.49(p^2-1)}`$. The amplitude ratio is at most $`e^{.42(p+1)}`$. The weighted sum of nonprincipal terms divided by the principal pair amplitude is below $`.33`$, using $`p=3`$ separately and the decreasing integral beyond $`5`$. The unweighted sum is below $`.11`$.

For $`10\le k<100`$, a nonprincipal pole enclosed by $`R/r\le1+1/k`$ forces $`s>6\sqrt k`$, and the vertical log-ratio bound is $`k\log(|w|/s)<1.14`$. When $`s\ge\max(50,2k)`$ the Poisson lower-tail estimate yields $`\pi|H'|<.02`$. In the complementary regime the simpler gamma density sum bound gives $`\pi |H'|<2`$ for $`k\le49`$ and $`.82`$ for $`50\le k<100`$. In these respective regimes $`s<98`$ or $`s<198`$, so $`nS^2>10`$ or $`nS^2>2.5`$. The decay $`|z_p|^n\le e^{-.44 nS^2(p^2-1)}`$ compensates for these larger phase bounds, giving weighted nonprincipal error below $`.11`$ in all three cases. The outer phase point $`s_*>200`$ always meets the small phase bound. For $`4\le k\le9`$ the previous contour's weighted sum is below $`.42`$ and the outer phase check is unchanged.

## Consecutive sign and degree count

Write $`Y_j`$ for the common normalization from the wider-circle proof, $`\gamma=\Im G(w_1)`$ and $`\Psi=(n+1)\theta-\gamma`$. The principal pair gives $`\cos\Psi`$ in the old row. Subtracting $`C Y_n`$ from $`Y_{n+1}`$ multiplies each common residue by $`z_p-C`$, and the principal pair gives $`-S\sin\Psi`$. The circle errors and residue terms above give throughout this range

$$
 |Y_n-\cos\Psi|<.20,\qquad
 |Y_{n+1}-C Y_n+S\sin\Psi|<.77 S.
$$

At an integer phase hit the value has the principal sign. At an old zero between consecutive integer phase levels, $`|\sin\Psi|\ge\sqrt{1-.20^2}>.77`$, which gives the required actual next-row sign. The first-hit proof therefore applies with precisely the same exterior and central endpoints. Reflection and degree exhaustion give all simple old roots and the actual next-root order. The theorem concerns only the stated aspect range.

Run `python3 -I -B check.py` for the scalar comparisons. It uses rational exponential and logarithm enclosures. [Recorded output](output.txt)

[Independent review](review.md) · [Independent checker](check-independent.py) · [Independent output](independent-output.txt)
