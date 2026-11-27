# Fourier coefficient errors on the comparison circle

For $w=Re^{ix}$, write $P_\ell=s+(2\ell+1)\pi i$, $c_\ell=R^k/P_\ell^{k-1}$, and $D(x)=\sum_\ell c_\ell/(P_\ell-w)$. Suppose $R>0$, $k\ge3$ and $|P_\ell|\ne R$ for every integer $\ell$. For any multipliers with $|t_\ell|\le |2\ell+1|S$, the differentiated contrast kernel satisfies

$$
\int_0^{2\pi}\left|\frac{d}{dx}\sum_\ell\frac{t_\ell c_\ell}{P_\ell-w}\right|dx
\le 2\pi R S\sum_\ell \frac{|2\ell+1|\,|c_\ell|}{\bigl||P_\ell|^2-R^2\bigr|}.
$$

The two tails converge because eventually $|P_\ell|\ge2(R+1)$, where each squared-pole weight is bounded by its ordinary pole weight. For $t_\ell=r/P_\ell-C$, the unintegrated partial fraction has an additional frequency $-1$ term. The proof sums the identity before taking absolute values and proves convergence of both separated sums. [Derivative estimate](FourierLatticeDerivative.lean) · [Signed split and frequency shift](FourierLatticeSplit.lean)

The old-row and adjacent-row inequalities bound Fourier coefficients using two integrations by parts. They take the periodicity, differential identities, amplitude bound, signed split (for the adjacent pair), and the estimates for the two kernel integrals as explicit inputs. The estimate on the common integral is $M(U+V)$ when the supremum of $|f|$ is at most $M$ and the two unnormalized kernel masses are at most $2\pi U$ and $2\pi V$. The adjacent-row theorem retains the two correction terms at frequencies $n+1-k$ and $n+1$. [Coefficient inequalities](FourierNormComparison.lean)

## Verification

All eight new declarations compiled on Lean 4.19.0, compiler commit `6caaee842e94`, mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with transitive axioms `propext`, `Classical.choice` and `Quot.sound`. The Linux run checks their full import closure and hashes each input. Its receipt is pending. To reproduce from the repository root with the installed research toolchain, run

~~~sh
cd shared/lean
lake env python3 -I ../../topics/long-cycle-excedances/lean/fourier-circle/check.py
~~~

The original angular equation is being integrated on the distinct source pin. Applying the inequalities to the row and proving a sufficiently small numerical error uniformly for large aspect are further formal obligations. [Original angular equation](https://github.com/ProgramComputer/open-math-research/pull/310)
