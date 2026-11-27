# Bounding the Fourier amplitude on the selected circle

Let $K\ge100$, $x\ge44$, $s\ge0$, $p=s+\pi i$, $r=|p|$ and $xK(\pi/r)^2\ge1$. Write $q=r/K$ and $c=\min(1/25,4/x)$. Let $L(z)=\log(1+e^{z-s})-\log(1+e^{-s})$ be the principal logarithm difference on $|z|\lt r$. Suppose the cutoff logarithm $G$ satisfies

$$
|G(w)-L(\widehat w)|+|G(p)-L((1-1/K)p)|\le M,
\qquad \widehat w=(1-1/K)rw/|w|
$$

for $r\le |w|\le (1+1/K)r$. There is a single choice $a=2-2c$ or $a=2$ such that every point of $|w|=r\sqrt{1+a/K}$ satisfies

$$
\frac{r\left|e^{G(w)}/(1+e^{w-s})\right|}{|e^{G(p)}|}
\le Ke^M(1+q)\left(1+\frac{425}{98c}\right).
$$

The factor multiplying $Ke^M$ is at most $457$ for $44\le x\le100$ and at most $(46/100)x\sqrt{x}$ for $x\ge100$. [Circle theorem](FourierSelectedAmplitude.lean) · [Scalar bounds](FourierAmplitudeScalars.lean)

The real part of the difference of the two logarithmic errors is at most $M$. Exponentiation bounds the ratio of the two errors by $e^M$. The common normalization $1+e^{-s}$ cancels. For $|\Im v|\le\pi$, zero is a nearest point to $v$ among the periods $2\pi i\ell$. Applying the period-gap inequality with distance $|v|$ yields $|1-e^v|\ge |v|/(1+|v|)$. Taking $v=-p/K$ gives the required principal bound for every $K\ge1$. [Principal strip lemma](FourierPrincipalPeriod.lean)

At the contracted principal point the remaining denominator is exactly $|1-e^{-p/K}|\ge q/(1+q)$. On the comparison circle the denominator ratio is at most $1+\Delta(1+\delta)/\delta$, with $\delta=(49/100)cq$ and $\Delta=|w-\widehat w|\le 2q$. Since $c^2x\le4/25$ and $q^2\le \pi^2x/K$, one has $\delta\le1/16$. Substitution gives the stated factor $425/98$. [Logarithmic comparison](FourierAmplitudeComparison.lean) · [Pole separation and principal denominator](../fourier-circle/principal-denominator.md)

## Verification

The four new modules compiled with warnings treated as errors on Lean 4.19.0, compiler `6caaee842e94` (short hash), mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine named transitive axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. A separate agent checked the denominator identity, use of the same circle for every angle, and rational constants at both ends of the ranges for the preliminary bound using $q/(2+q)$. The strengthened denominator and the two current constants also passed the local Lean check. [Independent review](review.md) The geometric theorem takes the displayed numerator-contraction inequality as a hypothesis. The [original finite numerator](FourierOriginalContraction.lean) uses the [full-disk logarithm](../fourier-stable/analytic-log-series.md), the [small-height estimate](../fourier-numerator/README.md) and the [high-height estimate](../fourier-high-height/README.md) to supply $M=2997/100$ for every $s\ge0$. The joined production replay on Lean 4.33.1 is pending. [Original selected-circle theorem](FourierOriginalAmplitude.lean)

From the repository root with Lean 4.33.1 on the path, use a new directory for the production run.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-amplitude/check.py /tmp/fourier-amplitude
~~~
