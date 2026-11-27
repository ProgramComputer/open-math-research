# Fourier coefficient bounds for the original numerator

The trace is the repository's original cutoff numerator evaluated on the circle and divided by the logistic denominator. For a cutoff $k\ge3$, a real parameter $s\ge0$, a positive circle radius $R$ avoiding the full signed pole lattice, and $r=\sqrt{s^2+\pi^2}$, Lean specializes the two integrations by parts to this trace.

The hypotheses give an amplitude $M$ and the four angular integrals of the pole products and their derivative factors. The proof supplies the derivative of the original trace and the two differentiated pole kernels. The older coefficient can use any integer Fourier index. The adjacent contrast uses $r/R$ on the new coefficient, $s/r$ on the old coefficient, and keeps the two corrections at indices $n+1-k$ and $n+1$ separately. The inequalities retain the factors $j(j-k)$ and $n(n-k)$, so the formal statements do not divide at a zero Fourier index. [Original coefficient bounds](FourierOriginalCoefficientBounds.lean) · [Signed-kernel derivative](FourierOddKernelCalculus.lean) · [Common-circle proof](../../fourier-circle/README.md)

The moment form takes just the amplitude bound. Its old coefficient has pole factor $S_0^2+RT_0$, and its adjacent contrast has pole factor $SS_0S_1+RST_1$, where $S=\pi/r$. Here $S_i$ uses the inverse square root of the squared pole gap and $T_i$ uses its inverse. Evaluating these moments and combining the Fourier error with the enclosed residues remain separate steps. [Moment specialization](FourierOddKernelMoments.lean)

Run on the stable Lean 4.33.1 pin from the repository root with a fresh output directory.

```sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-stable/check-original-coefficients.py /tmp/fourier-original-coefficients
```

The stable job passed at PR head `edca56be001970ca5fdc867c39284994dc03e0af` and GitHub checkout `215b1aabd0527a9c854bf5f7e59e384baaaa2c36`. Lean was pinned to 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`. All 52 compiler input digests matched the checkout or the authenticated cutoff-six archive, and all 19 bundled replay markers were present. The 95 axiom reports, including the five new declarations, use only `propext`, `Classical.choice`, and `Quot.sound`. The report ZIP, artifact `15211444995`, matched SHA-256 `23e72fa247c67570b6e0a56b98173aa88f1a0e0ad5091ab99675bd029667ddf2`. [Compiler, dependency, axiom and replay report](https://github.com/ProgramComputer/open-math-research/actions/runs/46026934213)

| Source | Compiler input SHA-256 |
| --- | --- |
| `FourierOddKernelCalculus.lean` | `07afc0575f8a01b056c5163f27d4fb6df41c92e6035a2ca77d26554724d4b691` |
| `FourierOddKernelMoments.lean` | `d12b3ae8fed907c6c81067dae662d70fc9f8139265af6e3aa34dedca3f85d402` |
| `FourierOriginalCoefficientBounds.lean` | `135057615acc1f23af5c7bac8c6bc12db57114b5c3cdac9e8c8b43404eb91715` |
