# Squared poles on the real axis

For real $x<s$, the signed odd-pole sum is

$$
\sum_{\ell\in\mathbb Z}
\frac{1}{\bigl(s+i(2\ell+1)\pi-x\bigr)^2}
=
-\frac{e^{x-s}}{(1+e^{x-s})^2}.
$$

The proof uses the $m=1$ instance of Bowen Zuo’s `LongCycleBounds.oddPoleSum_eq_powerSeries_of_pos` at $s-x>0$. The factor $1!$ is one. Mathlib sums the resulting series $\sum_{j\ge0}j q^j$ at $q=-e^{x-s}$, whose modulus is strictly below one. [Lean statement and proof](FourierRealAxis.lean) · [Supplying cutoff-six release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.2.0)

The proof is the real-axis input to the [common-circle argument](../../fourier-circle/README.md). It supplies the squared-pole formula strictly to the left of the pole line. The analytic continuation and original-row differential identity require separate arguments.

The build uses Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. It authenticates the supplying source archive and lock from `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`, builds the imported partial-fractions module, audits the bridge’s transitive axioms and replays the bridge. [Source checker](check-real-axis.py)

From the repository root, with the pinned toolchain on PATH, pass a new output directory to the checker.

```sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-stable/check-real-axis.py /tmp/fourier-real-axis-check
```
