# The original Fourier contour coefficient

Fix a cutoff $k\ge2$ and a height $s\ge0$. Write $t=-e^{-s}$, let $E_{n,k}(t)$ be the original permutation enumerator, and put $A_n=E_{n,k}(t)/((1-t)^{n+1}n!)$. Let $T$ be the exact finite tilt in the common-pin generating function. Write $f(w)=T(w)/(1+e^{w-s})$ and let $f_n$ be the normalized angular Fourier coefficient on a circle of radius $R>0$. For a regular circle, let $P$ consist of the enclosed poles $p=s+(2\ell+1)\pi i$. Then

$$
A_n=\frac{f_n}{R^n}+\sum_{p\in P}\frac{T(p)}{p^{n+1}}.
$$

The successor contrast for any scalars $r,C$ is

$$
rA_{n+1}-C A_n
=\frac{(r/R) f_{n+1}-C f_n}{R^n}
 +\sum_{p\in P}(r/p-C)\frac{T(p)}{p^{n+1}}.
$$

Both terms use the same $R$, $P$ and $t$. The residue of $f(w)/w^{n+1}$ at $p$ is $-T(p)/p^{n+1}$, since the logistic denominator has derivative $-1$ there. Thus transferring the outer boundary inward adds the displayed positive-sign pole contributions. The identity allows $s=0$ and applies at any original old-row zero without dividing by a row value. It has no estimates on the size of the Fourier boundary or enclosed-pole terms.

The anchored logistic resolvent has a Taylor series obtained by an absolutely summable double geometric expansion. Its degree-zero term is $1/(1-t)$, and the positive-degree terms use the existing signed odd-pole identity. The Cauchy product with the entire tilt identifies the analytic coefficient with the original permutation coefficient. On the annulus, subtract the finite principal parts and extend analytically through the former poles by analytic divided differences. Mathlib's annular integral equality then gives the transfer to the selected outer circle. [Original coefficient and contrast](RepositoryContourCoefficient.lean) · [Absolute Taylor expansion](AnchoredPoleTaylor.lean) · [Annular transfer](AnnularPrincipalParts.lean) · [Existing enclosed-residue estimate](../fourier-enclosed-residues/README.md)

Run `python3 -I -B check.py /path/to/new/project` on Linux with Lean 4.33.1. The optional `--retained-imports` argument reuses authenticated common-pin import objects. The local Lean 4.19.0 build covers the generic analytic, cutoff-logistic, and algebraic components. The hosted driver checks the literal permutation adapter against the common production pin, including the frozen release supplying the original Eulerian and cycle-profile identities.

[Independent mathematical comparison](review.md) · [Hosted verification record](verification.md)
