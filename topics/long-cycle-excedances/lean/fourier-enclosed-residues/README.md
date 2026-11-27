# Enclosed nonprincipal Fourier residues

For cutoff $k\ge100$ and height $s>0$, put $w_p=s+i\pi p$ for odd integers $p$, $r=|w_1|$ and $S=\pi/r$. Assume $nS^2\ge1$ and the contour radius satisfies $R^2\le r^2(1+2/k)$. For any finite set of positive odd labels $p\ge3$ with $|w_p|\le R$, define

$$
F_p=\left(\frac{r}{|w_p|}\right)^n\left|\frac{T(w_p)}{T(w_1)}\right|,
$$

where $T$ is the original finite tilt from the common-pin row generating function. The weighted sum of $F_p$ with weights $p$ is at most $1/4$, and the unweighted sum is at most $1/12$. The same normalized bounds apply to conjugate pairs by real coefficients. The Fourier contrast satisfies $|r/w_p-C|\le pS$ for $C=s/r$, so these budgets are below the $0.33S$ and $0.11$ targets. [Literal tilt and residue theorems](RepositoryWideResidues.lean) · [Fourier contrast bound](../fourier-circle/FourierPoleContrast.lean)

The existence of an enclosed nonprincipal pole gives $s\ge125/2$ and $R^{k-1}\le(31/10)s^{k-1}$. The existing one-sided gamma mesh bound adds at most $1/s$ to the height of the density peak. Monotonicity of the peak from degree $99$ bounds it by $41/1000$. It follows that the log numerator changes by less than $(14/25)(p-1)$ along the vertical chord from $w_1$ to $w_p$. This uses the actual log coefficients and the differences of their Poisson modes. The radial exponent is at most $-(49/100)(p^2-1)$. Writing $p=2j+1$, the combined exponent is at most $-14j/5$ and $p\le3^j$. Since $\exp(14/5)>15$, summing the weighted geometric bound gives $1/4$. Dividing by the smallest weight, $3$, gives the unweighted bound. [Fourier-circle argument](../../fourier-circle/README.md)

This component covers the enclosed nonprincipal residues at cutoff $k\ge100$. The phase at the initial angle, outer-circle integral, and sign composition are separate.

Run `python3 -I -B check.py /path/to/new/project` with Lean 4.33.1 on Linux and the common-pin dependencies prepared by the driver. The optional `--retained-imports` argument reuses the authenticated import archive. The driver compiles on the common pin and checks the named declarations' axioms and bundled LeanChecker replay.

[Independent statement review](review.md)
