# Coverage below lower size four times the cutoff

Here $n$ is the lower row size, $k$ is the same cutoff for both rows, and $E_{n,k}$ counts excedances of permutations whose cycles all have length at least $k$. The [original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) concerns the literal pair $E_{n,k},E_{n+1,k}$. The coverage ledger uses strict negative interlacing for the quotients by the common factor $t$ and weak real interlacing for the literal pair. Both outer negative roots belong to the successor.

## Supplied Lean results

These results come from Bowen Zuo’s [cutoff-six release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.2.0), using the repository’s frozen source at `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. The adapter supplies the canonical quotient statement used by the repository’s other sector theorems.

| Lower size $n$ | Reusable result and remaining conditions |
|---|---|
| $k\le n\le2k-2$ | `InitialRows.beforeSplitRow` identifies both original rows with $t$ times ordinary Eulerian rows. `EulerianSturm.eulerian_consecutive_strict` gives strict quotient interlacing at old degree $n-2$. `InitialRows.beforeSplitInterlacing` gives the weak original result directly. |
| $n=2k-1$, $k\ge55$ | `CoefficientRows.firstSplit_quotients` identifies the actual factor for each row, and `EulerianSturm.firstSplit55_strict` supplies strict interlacing at old degree $2k-3$. Multiplication by $t$ gives weak interlacing of the literal rows. The supplier's direct weak `InitialRows.throughFirstSplit` uses $k\ge201$. |
| $n=2k-1$, $8\le k\le54$ | `Assembly.firstSplitStrict_of_checked` and `Assembly.firstSplit_of_checked` are available. Their checked-window input has no instance for these pairs in the pinned Lean sources. This is a finite certificate obligation for 47 pairs. |
| $2k\le n\le3k-2$ | `BandFormula.actual_band_row` identifies quotient rows for actual size below $3k$. `BandEndpoint.actual_adjacent_of_separated` indexes by upper size $N=n+1=2k+d$, requires $402\le N$ and $d+1\le\sqrt N/400$, and consumes `SeparatedOnLegs`. No declaration in the pin supplies this separation predicate. This endpoint theorem therefore leaves even its narrow positive-width sub-band conditional. |
| $3k-1\le n\le4k-2$ | `ThreeCycleQuotient.actual_threeCycle_row` gives exact factors for both rows. `extend_threeCycle_actual_interlacing` asks for the preceding strict pair and the normalized sign at every old zero with nonnegative log-coordinate. Its bound $N<4k$ is on the upper size $N=n+1$. |
| $n=4k-1$ | The upper size $4k$ can contain four cycles. `GeneralCycleQuotient.actual_general_cycle_row` and `extend_general_actual_interlacing` use the actual all-cycle rows with the same sign premise. The three-cycle row formula may only be used for the old row here. |

At any step after the first split, the relevant sign premise has the form

$$
0 < F_{n+1}(s)(-F'_n(s))
\quad\text{when }s\ge0\text{ and }F_n(s)=0,
$$

Here $F_j$ is the supplier's actual normalized enumerator at $t=-e^{-s}$. At such a root, the derivative of the normalization contributes zero. The derivative of $t$ with respect to $s$ is positive. In the reduced variable, the reviewed paper obtains the sign by bounding the insertion term strictly below the magnitude of $t(1-t)P_n'(t)$ at every old root, where $P_n=E_{n,k}/t$. Thus the first missing post-split formal input is that comparison for lower size $n=2k$. The proof on paper covers the entire [two-cycle interval](../../two-cycle-band.md) and the [range through the first four-cycle row](../../three-cycle-complete.md). The exact arithmetic ledgers from those proofs are finite evidence and certificate inputs for future Lean verification.

## Other repository dependencies

The checked all-aspect exterior theorem supplies ordered exterior roots and literal successor signs for $n\ge10000$ and $k\le n$, including in this sector. The checked center theorem supplies the odd-degree center sign at $t=-1$ for all $k\le n$. With the checked reciprocal half-axis assembly, an alternative to the insertion induction is a proof of the correctly indexed remaining interior signs and locations. The checked complete bounded-aspect theorem starts at lower size $n=4k$, so it begins with the pair immediately after this sector. The checked sparse theorem and the ongoing wide-sector proof apply at larger aspects. The finite dyadic replay at cutoff eight starts with lower size 32. Neither that replay nor the live cutoff-eight Lean finite bridge covers the pair $(15,16)$ or any later pair strictly below lower size 32.

## Verification

The [Lean adapter](RepositoryEarlySector.lean) passed on Linux with Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The hosted checkout `e0f602d2bf5053a65ec0cd562d66b596dfe566bf` used PR head `2d79a1a0a2e058d5989a8abe9b1de4d7c559d8a0`. The source digests matched the frozen upstream archive and PR head. Leanchecker replayed both directly built modules. The four upstream declarations and two adapter declarations used only `propext`, `Classical.choice`, and `Quot.sound`. The downloaded report artifact `15216271526` matched SHA-256 `ac1ba9ce1f8928547ea8951f4ef50b0cf3db4668b40c8f5b409d70ca9ccd401f`. [Pinned build and replay](https://github.com/ProgramComputer/open-math-research/actions/runs/46034663786)

| Source | Compiler input SHA-256 |
| --- | --- |
| `LongCycleBounds/InitialRows.lean` | `da3836a0cd6a46aeceaf87d84b0362c79d96ec88cca7f18d11769b51fdc01e6e` |
| `RepositoryEarlySector.lean` | `5d67d3c141a6c6bdc8473aed21c4801d82e0e1dcf0f71d26e00a5d456f31c064` |

Run the audit from the repository root with the pinned compiler. The checker authenticates the released source archive and can either build the required upstream module or reuse the object archive from [common-pin run 45917288503](https://github.com/ProgramComputer/open-math-research/actions/runs/45917288503).

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/early-sector/check.py /tmp/long-cycle-early-sector
~~~
