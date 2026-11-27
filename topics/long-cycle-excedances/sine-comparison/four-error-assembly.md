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

## Verification of the determinant reduction

At commit `1a099e36ed966e958ef09f5c7462bd2dff2a3c92`, Lean 4.33.1 on Linux (compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and mathlib `0df444a360eaa60ab8c11dca51a86af692955474` checked `RepositoryQuotientAudit.original_four_error_determinant` and `original_determinant_margin` for the original strict-excedance enumerators. The second theorem assumes a bound on the explicit four-error sum and the rounded recurrence. [Exact source](https://github.com/ProgramComputer/open-math-research/blob/1a099e36ed966e958ef09f5c7462bd2dff2a3c92/topics/long-cycle-excedances/lean/paired-profile/RepositoryFourErrorDeterminant.lean)

The paired-profile check matched all 108 source hashes to the commit, replayed those 108 modules with Lean’s bundled checker, and audited 180 named declarations. The primitive-envelope check matched 41 source hashes, replayed its 18 root modules and audited 38 declarations. Both audits found only `propext`, `Classical.choice` and `Quot.sound` among the allowed axioms. GitHub’s archive digests matched the downloaded verification artifacts, respectively `46ba73c3a8fb490c210e3bdfd640e67ca90bb85a5b3bd495009e4cc4d9e00803` and `e3a536e368d18232655a224b035d5e8ab35012f283ab8a1277c1aa61655d6c3e`. [Paired-profile run](https://github.com/ProgramComputer/open-math-research/actions/runs/45995242680) · [Primitive-envelope run](https://github.com/ProgramComputer/open-math-research/actions/runs/45995242718)

Reproduce in a checkout at the verified commit with the pinned toolchain, separate fresh build directories and the retained common-pin import archive supplied by the workflows.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/paired-profile/check.py /tmp/four-errors-profile "$IMPORT_ARCHIVE"
python3 -Bu topics/long-cycle-excedances/lean/sine-comparison/check-primitive-envelope.py /tmp/four-errors-primitive --import-archive "$IMPORT_ARCHIVE"
~~~

On the source revision integrating the verified cutoff-jump and principal-cost modules, all 113 input digests matched their Git blobs, all 113 kernel replays passed, and the 192 named axiom reports contained only the standard axioms. The paired report ZIP has SHA-256 `0e8db79565cd98cdcd4f7e8d2de7b9e3a060c9df7ceb1a2b4fef2a12f9594ce0`. The same commands above reproduce the combined check at `953a222a2610a2d22b89fda48cc2c9a44ce4b39b`. [Combined run](https://github.com/ProgramComputer/open-math-research/actions/runs/45998725306) · [Report archive](https://github.com/ProgramComputer/open-math-research/actions/runs/45998725306/artifacts/15197529067)

After incorporating the coarse recurrence and moment packages, the [combined paired-profile audit](https://github.com/ProgramComputer/open-math-research/actions/runs/46004272222) passed at `127476e0405abe71a8da6f22445f3e202db30d1e`. All 147 compiled or evaluated Lean source digests match the integrated Git inputs. Lean’s bundled LeanChecker replayed 143 modules, and the workflow passed all 224 required axiom audits. The console SHA-256 is `d5dbafd7480ba408aefa713ad2cba2e743ebf6794633e029f0ea92a8b302c7ee`. The primitive-envelope and rational workflows also passed on that proof source.
