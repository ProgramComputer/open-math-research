# Fourier coefficient bounds for the original numerator

The trace is the repository's original cutoff numerator evaluated on the circle and divided by the logistic denominator. For a cutoff $k\ge3$, a real parameter $s\ge0$, a positive circle radius $R$ avoiding the full signed pole lattice, and $r=\sqrt{s^2+\pi^2}$, Lean specializes the two integrations by parts to this trace.

The hypotheses give an amplitude $M$ and the four angular integrals of the pole products and their derivative factors. The proof supplies the derivative of the original trace and the two differentiated pole kernels. The older coefficient can use any integer Fourier index. The adjacent contrast uses $r/R$ on the new coefficient, $s/r$ on the old coefficient, and keeps the two corrections at indices $n+1-k$ and $n+1$ separately. The inequalities retain the factors $j(j-k)$ and $n(n-k)$, so the formal statements do not divide at a zero Fourier index. [Original coefficient bounds](FourierOriginalCoefficientBounds.lean) · [Signed-kernel derivative](FourierOddKernelCalculus.lean) · [Common-circle proof](../../fourier-circle/README.md)

The moment form takes just the amplitude bound. Its old coefficient has pole factor $S_0^2+RT_0$, and its adjacent contrast has pole factor $SS_0S_1+RST_1$, where $S=\pi/r$. Here $S_i$ uses the inverse square root of the squared pole gap and $T_i$ uses its inverse. Evaluating these moments and combining the Fourier error with the enclosed residues remain separate steps. [Moment specialization](FourierOddKernelMoments.lean)

Run on the stable Lean 4.33.1 pin from the repository root with a fresh output directory.

```sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-stable/check-original-coefficients.py /tmp/fourier-original-coefficients
```
