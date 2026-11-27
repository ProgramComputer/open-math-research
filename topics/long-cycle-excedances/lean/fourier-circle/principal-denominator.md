# The principal denominator on the comparison circle

Put $z=(s+i\pi)/k$ and $q=r/k$, where $s\ge0$, $r=\sqrt{s^2+\pi^2}$ and $k\ge100$. For every height,

$$
|1-e^{-z}|\ge \frac{q}{2+q}.
$$

If $q\le\pi$, the modulus is at least $q/5$. If $q\le12\pi/25$, it is at least $q/3$. These are the three principal denominator estimates used in the large-aspect interlacing proof. [Original quantitative comparison](../../fourier-circle/README.md) · [Formal statement](FourierExponentialGap.lean)

For $u=\Re z\ge0$ and $0\le v=\Im z\le\pi/2$, integrate $e^{-tz}$ over $0\le t\le1$. Its real part is at least $e^{-tu}\cos v$. The integral of $e^{-tu}$ is at least $1/(1+u)$ by $e^u\ge1+u$. Multiplying by $|z|$ gives the bound $|1-e^{-z}|\ge |z|\cos(v)/(1+u)$. Here $v\le1/10$, so $\cos v\ge99/100$. This proves the two bounded-height estimates and the first estimate for $q\le1$. For $q>1$, use $q\le u+v\le u+1/10$ and $|1-e^{-z}|\ge1-e^{-u}\ge u/(1+u)$.

## The entire comparison circle

Suppose $w$ is at distance at least $\delta>0$ from every pole $s+(2\ell+1)\pi i$. For $s\ge0$, $0\le\alpha\le1$ and $\Delta=|w-\alpha w|$, one has

$$
\frac{|1+e^{\alpha w-s}|}{|1+e^{w-s}|}
\le 1+\frac{(1+\delta)\Delta}{\delta}.
$$

This gives a factor at most $2\Delta/\delta$ beyond one whenever $\delta\le1$. To see the denominator estimate, if $|1-e^v|<1$, the principal logarithm of $e^v$ has modulus at most $|1-e^v|/(1-|1-e^v|)$ by its Taylor remainder at one. It equals $v-2\ell\pi i$ for some integer $\ell$. Thus a distance of at least $\delta$ from every period implies $|1-e^v|\ge\delta/(1+\delta)$, also valid when $|1-e^v|\ge1$. Translating by $\pi i$ gives the corresponding odd-pole estimate for $1+e^v$. On the closed left half-plane the exponential is 1-Lipschitz by the derivative bound. Apply that fact directly if both real parts are nonpositive and after division by $e^{w-s}$ if $\Re(\alpha w)\le\Re w$. [Checked contraction theorem](FourierLogarithmicGap.lean)

On the two candidate circles the squared-radius estimate also gives an ordinary distance of at least
$\delta=(49/100)cr/k$ from every point of the selected circle to every pole, where $c=\min(1/25,4/x)$. Indeed $R\le1.01r$. A pole at distance less than $\delta$ would satisfy $|P_\ell|+R\le 2R+\delta\le2.03r$. Multiplying the radial difference by this sum would give a squared-radius gap strictly below $cr^2/k$. The formal theorem selects the circle and proves the ratio bound for every angle and every contraction on that same circle. [Combined original-circle statement](FourierOriginalDenominators.lean)

## Verification

The three principal estimates and five logarithm, contraction and circle statements passed Lean 4.19.0 at `6caaee842e94` and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All eight transitive axiom reports listed `propext`, `Classical.choice` and `Quot.sound`. The [initial hosted check](https://github.com/ProgramComputer/open-math-research/actions/runs/46008917250) passed 42 audits across 21 source modules for the principal estimates. The hosted rebuild including the five additional declarations is pending. The numerator contraction enters separately in the comparison.

~~~sh
cd shared/lean
lake env python3 -I ../../topics/long-cycle-excedances/lean/fourier-circle/check.py
~~~
