# Consecutive interlacing at aspect at least 20

For integers $7\le k\le n$ with $n/k\ge20$, let $E_{n,k}(t)$ count permutations by excedances when every cycle has length at least $k$. The two consecutive reduced rows $E_{n,k}(t)/t$ and $E_{n+1,k}(t)/t$, with the same cutoff $k$, have simple negative roots and strictly interlace. This proves the aspect-at-least-20 part of [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) at these thresholds. Formal verification is ⬜ None.

Bowen Zuo reports all-size proofs at $k=4,5,6$ in release v1.2.0. Repository verification of those claims is pending. [Zuo’s release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.2.0)

## Proof and independent checks

- Old sizes $n\le250$ are covered by the [exact finite prefix and independent replay](../finite-prefix/README.md).
- From old size $10{,}000$, the published [principal residue comparison](../paired-residues/README.md) applies when $20\le n/k\le48$, and the [Fourier comparison](../fourier-circle/README.md) applies when $n/k\ge44$.
- For $251\le n\le1000$, the [finite exterior certificate](finite-exterior/README.md) and its [independent replay](finite-exterior/review.md) establish the first $H=\lfloor7\sqrt n/20\rfloor$ old roots, their actual next-row signs and their position before $\theta_{\ast}=(H+5/6)\pi/n$. The historical calculations cover 114,750 pairs and 991,894 exterior ranks on one side.
- For $1001\le n\le9999$, the [uniform exterior comparison](high-exterior/README.md) and its [independent review](high-exterior/review.md) give the same exterior input.
- For the whole interval $251\le n\le9999$, the [middle comparison](middle/README.md) controls the common contour and the enclosed poles. The [amplitude review](middle/amplitude-review/review.md) and [vertical estimate review](middle/phase/review.md) independently check the two estimates.

For the join, write $P_j=E_{j,k}/t$, set $S=\sin\theta$, and use the normalized rows $Y_j$ and phase $\Psi$ from the middle comparison. The front supplies negative simple roots of ranks $1$ through $H$ in modulus. The sign of $P_{n+1}$ at rank $h$ is $(-1)^h$. All front roots have modulus less than $|t(\theta_{\ast})|$, where $n\sin^2\theta_{\ast}>1$ and $\Psi(\theta_{\ast})<(H+1)\pi$.

The phase is continuous and reaches $n\pi/2$ at $t=-1$. At this endpoint the linear term of $G_0(w)$ is $w/2$ and the higher terms are even, since the full logarithm is $w/2+\log\cosh(w/2)$. Use the first hits after $\theta_{\ast}$ of $j\pi$ for $H+1\le j\le\lfloor n/2\rfloor$. For each successive pair, take the last hit of the lower level before the first hit of the upper level. Between these two points the phase is strictly between the levels, and the old row has opposite signs at the endpoints. At a selected old zero in this gap, the actual next reduced row has sign $(-1)^j$ by the common contrast. The first such sign, at $j=H+1$, continues the front alternation.

Reflect the selected roots and the front roots by $t\mapsto1/t$. When $n$ is odd, reciprocity adds the old zero at $-1$ and the middle estimate gives its alternating next-row sign there. For even $n$, the selection and reflection alone account for all roots. In either parity this constructs $n-2$ distinct old roots with alternating next-row signs. Degree exhaustion gives their simplicity. The constant and leading coefficients of the next reduced polynomial are one. The alternating signs, with the signs at zero and at the negative infinite end, give $n-1$ distinct intervening next roots by the intermediate value theorem. This is strict interlacing of the actual consecutive rows.

The remaining range for thresholds $k\ge7$ is $251\le n<10{,}000$ and $4\le n/k<20$. The all-size three-cycle theorem covers $n/k<4$. [Three-cycle theorem](../three-cycle-complete.md)

## Source screening

On November 26, 2026 we rechecked the statement on SymCat and the author’s GitHub tracking issue. The target uses the ordinary excedance enumerator with every cycle length at least $k$, and compares consecutive sizes at fixed $k$. The corresponding ordinary-descent problem concerns a different statistic. [SymCat statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Alexandersson’s research issue](https://github.com/PerAlexandersson/RealRooted/issues/2590)

We repeated the source screening from the size-10,000 theorem and searched GitHub issues for “minimum cycle length”, “excedance” and “interlacing”, including the independent repository’s long-cycle investigation. We searched indexed X posts for “Alexandersson”, “excedances”, “minimum cycle length”, “real-rootedness” and “interlacing”. The GitHub results include Zuo’s reported fixed-threshold proofs. The sources reviewed did not give an external resolution of the stated range $n/k\ge20$ at all $k\ge7$. Public X indexing is incomplete. [Size-10,000 PR](https://github.com/ProgramComputer/open-math-research/pull/210) · [Independent investigation](https://github.com/1337isnot1337/solved-conjectures/issues/81) · [GitHub search](https://github.com/search?q=%22minimum+cycle+length%22+excedance+interlacing&type=issues) · [X query](https://x.com/search?q=Alexandersson%20excedance%20cycles%20interlacing&src=typed_query)
