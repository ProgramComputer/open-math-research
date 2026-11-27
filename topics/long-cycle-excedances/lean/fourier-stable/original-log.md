# Pole coefficients of the original cutoff logarithm

Put $t=-e^{-s}$ and let $g_j$ denote the repository’s `cutoffLogCoefficient k t j`. Its defining linear term gives $g_1=e^{-s}/(1+e^{-s})$, the logistic factor at zero. For $s\ge0$ and $2\le j<k$, the nonlinear terms satisfy

$$
j g_j=-\sum_{\ell\in\mathbb Z}\frac{1}{(s+i(2\ell+1)\pi)^j}.
$$

The proof uses Bowen Zuo’s `LongCycleBounds.Band.moment_poles` for the Eulerian moment with index $j$. The factor $(j-1)!$ from that formula cancels against $j!$ after multiplication by $j$. The formula includes $s=0$. These are the coefficients used by the finite logarithm for the original permutation enumerator. [Lean coefficient identities](FourierOriginalLog.lean) · [Supplying release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.2.0)

Use the [same pinned build](README.md) with the extra flag to verify both modules.

```sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-stable/check-real-axis.py /tmp/fourier-original-log-check --original-log
```
