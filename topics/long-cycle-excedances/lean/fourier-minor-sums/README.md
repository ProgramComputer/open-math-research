# Normalized nonprincipal residues

Let $P_j=s+(2j+1)\pi i$, $r=|P_0|$, $S=\pi/r$, and $C=s/r$. Let $T$ be the numerator of the exponential generating function for the original minimum-cycle-length excedance polynomials. For $k\ge100$, $s\ge0$, $nS^2\ge1$ and $0\le R$ with $R^2\le r^2(1+2/k)$, let $J$ be any finite set of positive nonprincipal indices $j\ge1$ satisfying $|P_j|\le R$. Write $z_j=r/P_j$ and $u_j=T(P_j)z_j^{n+1}/|T(P_0)|$. The proposed Lean result gives both bounds

$$
\left|\sum_{j\in J}u_j\right|\le\frac1{12},\qquad
\left|\sum_{j\in J}(z_j-C)u_j\right|\le\frac S4.
$$

The extra power of $z_j$ contracts each term in the [weighted residue bound](../fourier-enclosed-residues/README.md). At $s=0$ every positive nonprincipal pole has modulus at least $3\pi$ and the cap gives $R^2\le2\pi^2$. The allowed index set is empty. [Original theorem](RepositoryFourierMinorSums.lean) · [Endpoint geometry](FourierMinorGeometry.lean)

The scalar sign lemmas take the paired residue identities as hypotheses. Adding boundary errors smaller than $1/25$ and $S/25$ gives errors smaller than $37/300$ and $29S/100$. At an old root the normalized principal term has imaginary part of magnitude greater than $99/100$, and the new row has the sign of that imaginary part. [Error and sign lemmas](FourierMinorSum.lean)

## Verification

Common-pin verification of the original theorem is pending. From this directory on Linux with Lean 4.33.1 installed, run `python3 -Bu check.py /path/to/fresh/project`. The driver rebuilds the earlier residue and moment arguments and checks the axiom reports and bundled kernel replays.
