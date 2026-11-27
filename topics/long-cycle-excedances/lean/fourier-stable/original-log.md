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

The first Linux job reached its 30-minute limit while compiling mathlib dependencies after a targeted cache download. The proof itself had not yet elaborated. The retry uses the full pinned mathlib cache and the authenticated common-pin proof objects, then builds the remaining eight supplied logistic modules. [Cold-build timeout](https://github.com/ProgramComputer/open-math-research/actions/runs/46005139024)

The retry passed on Lean 4.33.1 at PR head `5036d3430ab21b25fb78d5a77653239028cb4805` and GitHub checkout `1610188679c6cef3cc03134dffd31a9e03f0ba4d`. The two Fourier modules passed same-toolchain kernel replay. All three named declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The report verified all nine dependency revisions and all 15 printed source hashes, including repeated accounting for the supplied `CycleProfileLogistic` target. The SHA-256 of `FourierOriginalLog.lean` was `922f618eb220244567c73746d6f352e558259ab49c9bba86fda52efbec41ab76`. The report ZIP, artifact `15202872930`, matched SHA-256 `aea295061d0faa4788528d4cbf8bd8114be67f40ac5fcb09f64e80931fb6deee`. [Compiler, dependencies, axioms and kernel report](https://github.com/ProgramComputer/open-math-research/actions/runs/46010337218)
