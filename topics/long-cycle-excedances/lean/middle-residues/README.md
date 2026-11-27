# Successor signs at middle roots of the long-cycle excedance polynomial

Let $E_{n,k}(t)$ count excedances of permutations in which every cycle has length at least $k$. Assume $7\le k\le n$, $n\ge100$ and $n/(200k)>30\log n+20$. For $x\ge0$ write $t=-e^{-x}$, $r=|x+i\pi|$, $S=\pi/r$ and $C=x/r$. The middle region is $nS^2\ge1$. With the finite tilt logarithm $G$ in the generating function and $\theta=\pi/2-\arctan(x/\pi)$, define

$$
\Psi=(n+1)\theta-\Im G(x+i\pi).
$$

At every old zero $E_{n,k}(-e^{-x})=0$ in this region, the proposed Lean proof gives $E_{n+1,k}(-e^{-x})(-\sin\Psi)>0$. A complete interval between consecutive multiples of $\pi$ in the decreasing phase contains an old zero. All old zeros in that interval give the same strict successor sign. This supplies the middle signs in the [uniform interlacing proof](../../effective-uniform.md). The exterior roots still require separate estimates. [Literal row theorem](RepositoryCenteredRows.lean) · [Phase cells](RepositoryMiddleCells.lean)

## A coefficient proof of the middle signs

The exact coefficient formula for a row is an absolutely convergent sum of truncated Taylor series over the poles $w_p=x+ip\pi$ with odd $p$, plus a top Taylor coefficient. Put $R_1=r(1+1/(100k))$, $R_0=r(1+3/(200k))$ and $R_*=r(1+1/(50k))$. At poles of modulus at most $R_0$ replace the truncation by the full Taylor series. At the other poles use zero. The inner Taylor-tail bound and the outer finite geometric bound both give

$$
(200k+3)A\left(\frac{r}{R_1}\right)^{q-1}\left(\frac{r}{|w_p|}\right)^2,
\qquad A=\exp(6+9\log k)
$$

for the error in the contribution of one pole at row $q$. The squared radius ratios sum to at most $2+n/2$ over the signed lattice. This single estimate applies to both $q=n$ and $q=n+1$, with the same set of enclosed poles. It avoids a choice of contour separated from every pole. After division by the principal amplitude the resulting error in each row is at most $1/(100n)$. [Per-pole bounds](NestedPoleRadii.lean) · [Lattice sum](NestedPoleLattice.lean) · [Actual row](RepositoryNestedRow.lean) · [Normalized budget](NestedNormalized.lean)

The principal mode has modulus one after normalization. For a positive enclosed odd pole, $|r/w_p-C|\le pS$. Passing to the next row multiplies its old contribution by $r/w_p$. The same weighted sum over the positive nonprincipal poles is at most one fifth of the principal amplitude. Together these bounds give the following estimates for the positively normalized rows $Y_q$.

$$
|Y_n-\cos\Psi|\le\frac14,
\qquad |Y_{n+1}-CY_n+S\sin\Psi|\le\frac S4 .
$$

At an old root the first bound implies $|\sin\Psi|\ge\sqrt{15}/4$. The second fixes the sign of the actual successor. At the exact phase levels the first bound also fixes the alternating old-row signs. The intermediate value theorem and strict decrease of the phase give the cell statement. [Weighted sum](../vertical-tilt/README.md) · [Matching adjacent modes](CenteredPoleReadout.lean) · [Phase-to-row comparison](PolePhaseReadout.lean) · [Signed phase cell](ExactPhaseCell.lean)

## Verification

An independent agent reviewed the original permutation definition, both row normalizations, the pole estimates and the successor sign. [Independent review](independent-review.md)

The generic bounds have local Lean 4.19 checks. The genuine shared-pin build of the full assembly is pending. The all-cutoff interlacing theorem retains 🟨 Partial · Lean 4 coverage. The common driver stages the frozen upstream source and checks the declarations and their axioms.

~~~sh
python3 -I topics/long-cycle-excedances/lean/common-pin/check.py /tmp/long-cycle-middle-proof
~~~
