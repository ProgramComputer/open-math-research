# Strict long-cycle interlacing from exterior coefficient inequalities

Let $E_{n,k}$ count strict excedances on permutations with every cycle of length at least $k$. Write $P=E_{n,k}$, $Q=E_{n+1,k}$ and $H=\lfloor7\sqrt n/20\rfloor$. Assume $n\ge10^4$, $7\le k\le n$ and $n/(200k)>30\log n+20$. Under those hypotheses, Lean reduces full strict interlacing of $P/t$ and $Q/t$ to **two finite coefficient inequalities per exterior rank**, together with order and size bounds on the chosen scales. It also gives a second criterion using the original insertion recurrence. The all-cutoff theorem has 🟨 Partial · Lean 4 coverage. [Statements in Lean](RepositoryExteriorCertificates.lean) · [Written all-cutoff proof](../../all-cutoffs/README.md) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

## The certificate

At rank $1\le h\le H$, choose $a,u>0$ and a polynomial $G$. Put $L=7u/8$ and $U=9u/8$. For a polynomial $R=\sum_j r_jt^j$ define

$$
M_h(R)=\sum_{j<h}\frac{|r_j|}{L^{h-j}}+\sum_{j\ge h}|r_j|U^{j-h}.
$$

This bounds $|R(-v)|/v^h$ throughout $[L,U]$. With rational coefficients and rational choices of $a,u,G$, each test uses rational arithmetic. The two residual polynomials are

$$
T=P-a t^h(1+t/u),\qquad W=Q-GP+(1-t)a t^h .
$$

If $M_h(T)<a/8$, the signed old values at $-L$ and $-U$ have opposite signs. There is a root $-w$ with $L<w<U$. At every such root, $W(-w)=Q(-w)+(1+w)a(-w)^h$. Thus $M_h(W)<a$ forces $(-1)^{h+1}Q(-w)>0$. Consecutive boxes may touch at their endpoints. Require their interiors to be disjoint in increasing modulus and every right endpoint to be at most $(459/40)(H/(H+1))^n$. These explicit bounds and the two coefficient tests suffice for the complete quotient root lists to be simple, negative, and strictly interlacing. Adjoining the shared zero yields weak interlacing of the literal rows. [Coefficient norm](FrontCoefficientNorm.lean) · [One signed root](CoefficientFrontWindow.lean) · [Assembly](RepositoryExteriorCertificates.lean)

Natural choices are $a=[t^h]P$, $u=a/[t^{h+1}]P$ and $G=(h+1)+(n-h-1)t$. The second residual then equals $(1-t)(tP'-(h+1)P+a t^h)$ plus the lag term of the insertion recurrence. Exact calculations on 47 windows across 23 small row pairs passed both tests. Two independent coefficient recurrences agreed and literal permutation enumeration checked the small-row convention. These tests certify the specified exterior windows. The global size inequality is a separate hypothesis of the interlacing theorem. [Experiment, commands and complete coefficient ledger](experiment/README.md)

## Joining the roots

The middle-root theorem gives the successor sign at each old root in a complete interval of the true phase. Take the boundary angle $\theta=(H+5/6)\pi/n$ and $b=\pi/\tan\theta$. At this boundary the phase is less than $(H+1)\pi$. At the center it equals $n\pi/2$. Selecting one old root in each intervening complete interval gives $\lfloor n/2\rfloor-H-1$ signed roots of modulus between $e^{-b}$ and 1. [Boundary geometry](RepositoryJoinAngle.lean) · [Phase levels and ordered roots](RepositoryMiddleLevelSelection.lean) · [Middle-root proof](../middle-residues/README.md)

For the exterior roots, $\log(1+1/H)\ge1/(H+1/2)$ and $(H+1)^2\le (9/25)^2n$ give

$$
n\log(1+1/H)-\frac{n}{H+5/6}>\frac52>\log(459/40).
$$

Since $b<n/(H+5/6)$, every exterior box lies strictly below $e^{-b}$ in modulus. Dividing by the negative root reverses the sign of the successor. Its reduced signs are $(-1)^H$ at the last exterior rank and $(-1)^{H+1}$ at the first middle rank. The combined list has $\lfloor(n-2)/2\rfloor$ entries. Reciprocity supplies the other half, the proven central sign handles odd old degree, and the degrees force both root lists to be complete. [Separation](FrontModulusJoin.lean) · [Ordered concatenation](FrontMiddleWitnesses.lean) · [Original polynomials and both conclusions](OriginalLiteralHalfRoots.lean)

The alternative analytic criterion uses the old two-term estimate, its centered derivative estimate and a bound on the lag polynomial. The real intermediate value theorem gives one signed old root in each box. The rank count above then gives simplicity. The remaining analytic obligation is to deduce the required bounds on all the boxes from the original coefficients. [Real window](RealFront.lean) · [Polynomial inequalities](PolynomialFront.lean) · [Permutation insertion recurrence](RepositoryPolynomialFront.lean)

## Verification

An agent who developed the phase-level selector separately reviewed the two parities, the orientation of both signs, and the coefficient residuals. The reports distinguish mathematical review from Lean compilation. [Join and scope review](independent-review.md) · [Coefficient review](coefficient-review.md)

Lean 4.33.1 compiled and replayed all 14 modules at commit `f6b7d8e014eccf97644690523312fd4dbee3bd5f`. The 31 named declarations use only `propext`, `Classical.choice` and `Quot.sound`. The first build found three redundant tactic calls after `field_simp` had already closed their goals. Removing them left the statements unchanged. This run used Lean’s own kernel checker. [Verification record with source hashes and pins](verification.txt) · [Hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/45948370622)

Reproduce the build from the repository root in a fresh directory with the pinned Lean installation and frozen upstream sources.

~~~sh
python3 -I topics/long-cycle-excedances/lean/common-pin/check.py /tmp/long-cycle-exterior-join
~~~
