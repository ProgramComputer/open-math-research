# Signed phase margins for consecutive permutation rows

Let $k\ge100$, $n/k\ge48$, $s\ge0$, $t=-\exp(-s)$, $p=s+\pi i$, $r=|p|$, $S=\pi/r$, and $C=s/r$. Assume $nS^2\ge1$. Write $T$ for the numerator of the row generating function and $U=|T(p)|$. The principal term and normalized rows are

$$
a=\frac{T(p)}U\left(\frac rp\right)^{n+1},\qquad
Y_j=\frac{r^{j+1}E_{j,k}(t)}{2U(1-t)^{j+1}j!}.
$$

The proposed original-row theorem gives

$$
|Y_n-\Re a|<\frac{37}{300},\qquad
|Y_{n+1}-C Y_n-S\Im a|<\frac{29}{100}S.
$$

At a zero of $E_{n,k}(t)$ this yields $|\Im a|>99/100$ and $E_{n+1,k}(t)\Im a>0$. The proof pairs both finite residue sums on the same contour. The old coefficient and the signed adjacent coefficient use the same positive scaling. [Original statement](RepositoryFourierPairedRows.lean) · [Finite pairing and sign calculation](FourierPairedRows.lean)

## Verification

The algebraic composition passed a local Lean 4.19 compatibility check with the four supplying estimates and identities as explicit hypotheses. Compilation against the original permutation objects on the research pin is pending. Run `python3 -Bu check.py /path/to/fresh/project` in this folder with Lean 4.33.1 on Linux. [Independent sign and scope review](review.md)
