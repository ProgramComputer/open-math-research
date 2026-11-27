# Identifying the all-degree numerator series

Put $r=\sqrt{s^2+\pi^2}$ for $s\ge0$ and $p_\ell=s+(2\ell+1)\pi i$. Let $c_0=0$, $c_1=r/(1+e^s)$ and $c_j=-\sum_\ell(r/p_\ell)^j/j$ for $j\ge2$. These are the normalized coefficients used in the small-height numerator estimate. For every complex $z$ with $|z|<1$ the series sums absolutely and satisfies

$$
\sum_{j\ge0}c_j z^j=\log(1+e^{rz-s})-\log(1+e^{-s}).
$$

Both logarithms use the principal branch. For $|w|<r$, if $\Re w<s$, then $1+e^{w-s}$ has positive real part. Otherwise $|\Im w|<\pi$. In the latter case the imaginary part of $1+e^{w-s}$ is nonzero except on the real axis, where the value is positive. Thus this formula defines a single analytic logarithm throughout the disk, vanishing at zero. [Disk logarithm and derivative](FourierDiskLog.lean)

The derivative of the finite logarithm of degree $m+1$ differs from the logistic function by an exact geometric remainder over the poles. On the closed disk of radius $\rho<r$, this remainder has norm at most

$$
(\rho/r)^m\frac{\rho}{1-\rho/r}\sum_{\ell\in\mathbb Z}|p_\ell|^{-2}.
$$

The mean-value inequality applied on that disk gives uniform convergence of the finite logarithms to the displayed analytic branch. For absolute convergence of the normalized series, $|r/p_\ell|\le1$ bounds every pole moment of degree at least two by its second moment. The remaining powers of $|z|$ form a summable geometric series. [Remainder estimate](FourierDiskRemainder.lean) · [Limit of finite logarithms](FourierDiskConvergence.lean) · [Absolute convergence and series identity](FourierNumeratorSeries.lean)

## Verification record

The analytic argument and identification with the actual normalized coefficient definition compiled on Lean 4.19.0, mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. At that stage the final theorem has two hypotheses from the supplying proof, the real-ray formula and inverse-square summability. The production adapter discharges these using the frozen real-axis release and full odd lattice on Lean 4.33.1, compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The [production rebuild](https://github.com/ProgramComputer/open-math-research/actions/runs/46015393010) matched all 20 repository inputs at `b567c86d81fea475e488e6ba7110ae3c9ba1b75e`. All 26 named transitive axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. The bundled checker replayed 16 modules, including `FourierOriginalLogSeries`. The final `original_log_series_hasSum` needs only nonnegative height and a point in the open unit disk. The [separate Fourier inventory](https://github.com/ProgramComputer/open-math-research/actions/runs/46015392740) also passed. [Original theorem](FourierOriginalLogSeries.lean) · [Real-axis source](README.md) · [Small-height estimate](../fourier-circle/numerator-small-height-verification.md)

From the repository root, use the production toolchain and a fresh output directory.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-stable/check-real-axis.py /tmp/fourier-log-series --continuation
~~~
