# Numerical bounds for the original Fourier pole kernels

Let $k\ge100$, $x=n/k\ge48$, $r=\sqrt{s^2+\pi^2}$ and $P_l=s+(2l+1)i\pi$ for $l\in\mathbb Z$. Assume $n(\pi/r)^2\ge1$ and $r\le R\le(1+1/k)r$. The selected circle has squared gap

$$
 \Delta_l=\bigl||P_l|^2-R^2\bigr| \ge \frac{c r^2}{k}
 \quad\text{for all }l\in\mathbb Z,\qquad c\ge\frac1x .
$$

For the original row coefficient $a_l=R^k/P_l^{k-1}$, let $S_0$ sum $|a_l|/\sqrt{\Delta_l}$ and $T_0$ sum $|a_l|/\Delta_l$. Let $S_1,T_1$ be the respective sums with the extra factor $|2l+1|$. The exact endpoint correction in the adjacent coefficient estimate is $A=R^{-1}\sum_l (r/P_l)a_l$.

The bound $(R/r)^k\le e<3$ gives $|a_l|\le 3r\,|r/P_l|^{k-1}$. The squared gap gives $\Delta_l^{-1/2}\le\sqrt{kx}/r$ and $\Delta_l^{-1}\le kx/r^2$. Applying the [signed odd-pole moment bounds](../fourier-odd-moments/verification.md) gives the following estimates:

$$
 \frac{S_0}{\sqrt{k}}\le9x,\qquad
 \frac{S_1}{\sqrt{k}}\le12x\sqrt{x},\qquad
 \frac{RT_0}{k}\le10x\sqrt{x},\qquad
 \frac{RT_1}{k}\le13x^2,\qquad |A|\le9\sqrt{x}.
$$

The two bounds involving $T_j$ use $R/r\le101/100$. For $A$ use $|r/P_l|\le1$ and $r/R\le1$. The checked theorem also supplies summability of the four nonnegative kernels and absolute summability in the endpoint sum, as well as nonnegativity of the two scaled $S_j$ terms.

[Pointwise coefficient and gap estimates](FourierPolePointwiseBudget.lean) · [Literal row budget theorem](FourierLiteralKernelBudgets.lean)

The [common-pin checker](check.py) uses the original coefficient driver and checked discrete moments. Run from the repository root with Lean 4.33.1 first on the path.

    python3 -Bu topics/long-cycle-excedances/lean/fourier-kernel-budgets/check.py /tmp/fourier-kernel-budgets

The [hosted workflow](../../../../.github/workflows/long-cycle-literal-kernel-budgets.yml) can reuse the authenticated common-pin import archive. The project compiler entry point for an already prepared project is compile_kernel_budgets.
