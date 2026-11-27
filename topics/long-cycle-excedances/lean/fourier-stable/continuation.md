# Angular derivative of the original cutoff generating function

Write $p_\ell=s+(2\ell+1)\pi i$ and $w=Re^{ix}$. Let $G_k$ be the finite cutoff logarithm with the coefficients of the original permutation generating function at $t=-e^{-s}$. Put $f(z)=e^{G_k(z)}/(1+e^{z-s})$. The theorem proposed for the production pin is the following angular derivative, for $k\ge2$, $s\ge0$ and every real $R,x$ with $w\ne p_\ell$ for all $\ell$.

$$
\frac{d}{dx} f(Re^{ix})
=i e^{ikx} f(w)\sum_{\ell\in\mathbb Z}
  \frac{R^k}{p_\ell^{k-1}(p_\ell-w)} .
$$

The anchored sum $A(z)=\sum_\ell z/[p_\ell(p_\ell-z)]$ vanishes at zero. On a disk away from the poles, the series of derivatives has a summable majorant by a constant times $\sum_\ell |p_\ell|^{-2}$. Its sum agrees on the real ray $x<s$ with the negative derivative of $H(z)=e^{z-s}/(1+e^{z-s})$, by Bowen Zuo’s squared-pole identity. The complement of the lattice is connected. The complex identity theorem followed by evaluation at zero gives $A(z)=H(0)-H(z)$ throughout that complement. Removing the first $k-2$ terms of the exact geometric expansion gives $G_k'(z)-H(z)$. The chain rule supplies the factor $iw$ in the angular derivative. [Real-axis source and replay](README.md) · [Finite logarithm coefficients](original-log.md)

The exported target uses the power-series numerator from the original cycle profiles. The permutation-coefficient identification is recorded in `original_logistic_coefficient`. Quantitative estimates for this angular equation are a separate obligation in the all-cutoff proof. [Angular statement](FourierOriginalAngularRow.lean) · [Permutation coefficient](../common-pin/RepositoryCoherentPoles.lean)

## Verification record

A compatibility implementation of the continuation, local convergence, finite geometric remainder and conditional angular formula compiled on Lean 4.19.0. The latter takes the real-ray equality and finite logarithm coefficients as hypotheses. The production adapter instantiates those inputs on Lean 4.33.1, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` with mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The production rebuild, axiom reports and bundled checker replay for the joined theorem are pending.

From the repository root, with the pinned Linux toolchain on the path, run the following command with a fresh directory.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-stable/check-real-axis.py /tmp/fourier-continuation --continuation
~~~
