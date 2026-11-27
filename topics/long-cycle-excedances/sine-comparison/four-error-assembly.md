# Joining the four error bounds on the original adjacent rows

Let $F_n$ be the normalized strict-excedance enumerator defined in the [topic statement](README.md). Fix $n\ge10000$, one of the nine intervals $\ell\le n/k\le X$ with $4\le\ell<X\le48$, and a middle angle $0<\theta\le\pi/2$ with $n\sin^2\theta\ge6/5$. Put $S=\sin\theta$. The signed quantity of interest is

$$
\frac{k}{S}\bigl(\sin((n+1)\theta)F_n-\sin(n\theta)F_{n+1}\bigr).
$$

**Where cancellation occurs.** On the symmetric window of integer pole indices from $-M-1$ to $M$, reflection $q\mapsto-q-1$ exchanges the principal indices $0$ and $-1$ and conjugates the entire occupied product. For $w=\cos\theta+iS$ and occupied degree $t\le n+1$,

$$
w^{-(n+1-t)}\bigl(w\sin((n+1)\theta)-\sin(n\theta)\bigr)=S w^t.
$$

Thus the two principal value contributions sum to twice the real part of the same centered row, multiplied by $S$. This identity accounts for their relative phase at both adjacent sizes. [Conjugation on the finite window](../lean/paired-profile/PrincipalConjugation.lean) · [Angular identity](../lean/paired-profile/PrincipalPhase.lean) · [Exact principal pair](../lean/paired-profile/ActualPrincipalPair.lean)

**From the finite product to the actual rows.** The finite adjacent identity splits each pole term into a value and a numerator difference. Its absolute numerator sum divides exactly at $s=n+1-t=k$. Use the regular bound at $s>k$, the isolated jump at $s=k$, and the vanishing difference below the cutoff. Summing the resulting inequalities gives the scaled determinant of the finite window at least its principal contribution less the four error bounds. The finite principal contribution and both complete adjacent rows converge on the same sequence of windows. Taking that limit preserves the lower bound. [Finite determinant identity](../lean/paired-profile/ActualWindowParts.lean) · [Exact numerator partition](../lean/paired-profile/ActualNumeratorCost.lean) · [Four-error theorem](../lean/paired-profile/FourWindowErrors.lean) · [Permutation specialization](../lean/paired-profile/RepositoryFourErrorDeterminant.lean)

**The finite arithmetic obligation.** For each interval, the formal analytic statement uses a table $q_0,\ldots,q_{240}$ satisfying the integer product inequalities. To deduce the stated numerical margin in Lean one must bound the four explicit finite heads for that table. The separate outward millionth bounds sum to 537946, 408948, 87610, 71365, 84423, 106923, 137598, 161483 and 164202 in interval order. With the principal lower bound $54/55$ on the first two intervals and $6000/12243$ on the remaining seven, these integer bounds give a uniform margin greater than $325873/10^6$. The exact rational replay checks these nine total costs. Providing all nine inequalities to the kernel is a separate verification step. [Rational checker](check-four-errors.py) · [All nine margins](four-errors-output.txt) · [Integer product verification](https://github.com/ProgramComputer/open-math-research/pull/298)

Local Lean 4.19 checked the finite-window comparison, conjugation, phase cancellation and limit transfer with the standard axioms. The production specialization uses the original normalized permutation enumerators. This estimate applies to the bounded-aspect angular sector. The all-size root-list theorem has further cases. [All-cutoff tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)
