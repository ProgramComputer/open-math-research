# One normalized Fourier error bound for every aspect from 48

For $x=n/k\ge48$, the old row and signed adjacent contrast both admit a scalar error bound below $1/25$, after dividing the contrast by $S=\pi/r$, **provided their kernel estimates satisfy the hypotheses below**. The reduction uses the improved amplitude constants and a single exponential comparison for the whole range.

Let $s_i=S_i/\sqrt{k}$ and $t_i=RT_i/k$ denote scaled masses of the Fourier kernels. Suppose

$$
0\le s_0\le9x,\qquad 0\le s_1\le12x\sqrt{x},\qquad
t_0\le10x\sqrt{x},\qquad t_1\le13x^2 .
$$

Then $O=s_0^2+t_0\le83x^2$ and $J=s_0s_1+t_1\le110x^2\sqrt{x}$. The adjacent bound has corrections from the shifted Fourier coefficients at $n+1-k$ and $n+1$. Suppose their signed multiplier and endpoint multiplier have moduli at most $(9/10)nS$ and $nS/50$, respectively. Applying the old bound at these two indices adds at most $((9/10)x/(x-2)+1/50)O$. The resulting budget is at most $x^2(110\sqrt{x}+80)$. [Kernel arithmetic](FourierKernelScalars.lean) · [Shifted coefficients](FourierAdjacentBudget.lean)

Suppose the amplitude factor after extracting $ke^{2997/100}$ is at most $457$ for $x\le100$ and $(46/100)x\sqrt{x}$ for $x\ge100$. The selected radius satisfies $(r/R)^n\le e^{-(19/20)x}$ for $48/25\le a\le2$ and $k\ge100$, by the lower bound $2u/(2+u)\le\log(1+u)$ with $u=a/k$. Under these hypotheses the common bound is

$$
100x^2\exp(2997/100-(19/20)x)\lt 1/25 .
$$

To check the endpoint exactly, the first 28 Taylor terms of $e^{1563/100}$ sum to more than $25\cdot100\cdot48^2$. For $x=48+y$ with $y\ge0$, the inequality $1+y/48\le e^{y/48}$ bounds the quadratic growth. The exponential decrease then bounds the expression by its value at 48. The final step cancels the two cutoff factors against $n(n-k)$. [Radial decay and endpoint](FourierUniformDecay.lean) · [Normalized conclusion](FourierNormalizedError.lean)

The four modules and six named transitive axiom reports passed locally on Lean 4.19.0, compiler `6caaee842e94` (short hash), mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All reports contained only `propext`, `Classical.choice` and `Quot.sound`. The common-pin replay and application to the exact kernel sums of the original permutations are pending. [Original amplitude](https://github.com/ProgramComputer/open-math-research/pull/317) · [Original kernel inequalities](https://github.com/ProgramComputer/open-math-research/pull/318) · [Odd-pole moments](https://github.com/ProgramComputer/open-math-research/pull/320)

From the repository root, with Lean 4.33.1 on the path, run the following command with a new directory.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-errors/check.py /tmp/fourier-errors
~~~
