# Independent scope and finite replay audit of Zuo's cutoffs four through six

Agent-assisted review by Codex, 2026-11-26. The three pinned releases address Alexandersson's actual strict-excedance polynomials for the respective fixed minimum cycle lengths. The source statements match the unweighted claims in the supplying manuscripts and the finite endpoints below. This local audit covers statement scope, sign transport, and the indicated exact computations. The supplying theorems and original formal proofs are by Bowen Zuo. The independent Lean rebuild and axiom reports remain pending in PR #216. [Alexandersson's original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles) · [Separate rebuild record](https://github.com/ProgramComputer/open-math-research/pull/216)

| Cutoff | Supplying manuscript and source | All-size lower index | Finite replay upper index | First analytic pair |
| --- | --- | ---: | ---: | --- |
| 4 | Theorem 4, v1.0.0 at `f8fef864286a1bbc59f96484074f28d77b1a027f`, `LongCycleBounds.fixed_four_all_sizes` | $p\ge4$ | $5\le n\le511$ | $(511,512)$ |
| 5 | Theorem 5, v1.1.0 at `70cad373bce521d78d6de9bcff3d29d07fc7fe9f`, `LongCycleBounds.FiveCutoff.all_sizes` | $p\ge5$ | $6\le n\le48$ | $(48,49)$ |
| 6 | Theorem 6, v1.2.0 at `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`, `LongCycleBounds.SixCutoff.all_sizes` | $p\ge6$ | $7\le n\le48$ | $(48,49)$ |

Here $n$ is Zuo's upper size and $p=n-1$ is Alexandersson's old size. Thus the hard-cutoff finite ranges in old-size notation are $4\le p\le510$, $5\le p\le47$, and $6\le p\le47$. The all-size entries start at the first pair of two nonempty rows. The analytic branches begin at upper size 512 for cutoff four and 49 for cutoffs five and six. There is no omitted transition at these joins. [Cutoff four supplying release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.0.0) · [Cutoff five supplying release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.1.0) · [Cutoff six supplying release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.2.0)

## Original statistic and complete root statement

Zuo's `LongCycles.excedances` counts labels $i$ with $i<\sigma(i)$ on the original ordered `Fin n`. Shifting the labels to $1,\ldots,n$ preserves these strict inequalities. The admissibility test forbids positive returns $\sigma^j(i)=i$ for $0<j<k$. The minimum positive return time is the length of the cycle through $i$, so this says precisely that every cycle length is at least $k$. The original `enumerator` sums $t^{\mathrm{exc}(\sigma)}$ on this predicate. At the analytic branch, `profile k 0` assigns zero to every forbidden short cycle and one to every cycle of length at least $k$. Its weighted row equals this original enumerator at both sizes.

For an allowed size $j\ge k$, every cycle contributes at least one excedance. Exactly one admissible permutation contributes at exponent one, the single $j$-cycle whose cyclic word has its unique ascent at the closing edge from the smallest to the largest label. Thus $[t]E_{j,k}=1$ and the common $t$ factor is simple. The unique cycle with $j-1$ excedances similarly gives the monic quotient of degree $j-2$. The quotient identity in the supplying sources is $E_{j,k}=t P_{j,k}$. The strict statement factors each quotient over complete, strictly increasing lists of negative roots. The old and next list lengths are $n-3$ and $n-2$, and next-root endpoints enclose each old root by strict inequalities. Appending the common simple root $0$ gives the weak adjacent interlacing of the full rows that is needed for the original conjecture.

The cutoff-four wrapper first chooses the finite certificate at upper $n\le511$, and otherwise uses the analytic original-row result at $n\ge512$. The cutoff-five and cutoff-six `OriginalPair` conclusions identify both original rows as $t$ times their quotients and include the strict quotient and weak original-row claims. Their branch at $n\le48$ uses the finite original-row theorem, and $n\ge49$ uses the analytic original-row theorem. [Cutoff four source map](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/f8fef864286a1bbc59f96484074f28d77b1a027f/verification/README.md) · [Cutoff five source map](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/70cad373bce521d78d6de9bcff3d29d07fc7fe9f/cutoff-five/verification/README.md) · [Cutoff six source map](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/cutoff-six/verification/STATEMENT-MAP.md)

## Signed comparison and transport

Use $t=-e^{-x}$, so $dt/dx=-t>0$, and $H_j(x)=E_{j,k}(t)/(1-t)^j$ at the hard cutoff. At an old zero of $P_{p,k}$ the denominator derivative contributes zero. One has

$$
-H'_p(x)=\frac{t^2 P'_{p,k}(t)}{(1-t)^p},
\qquad
H_{p+1}(x)(-H'_p(x))
=\frac{t^3 P_{p+1,k}(t)P'_{p,k}(t)}{(1-t)^{2p+1}}.
$$

Thus the declared normalized inequality $`H_{p+1}(-H'_p)>0`$ is equivalent to $`P_{p+1,k}(t)P'_{p,k}(t)<0`$. This is the orientation with the next polynomial supplying both outer roots. In the scaled insertion comparison, $`Z`$ and $`Y_n`$ are $`H_n+H'_p`$ and $`H_n`$, respectively, multiplied by the same positive factor $`\rho^{n+1}/((1-t)n!)`$. A term $`(p)_a C_a H_{p-a}`$ contributes $`C_a\rho^{a+1}Y_{p-a}/n`$ after that scaling, since $`p=n-1`$. Therefore $`|Z|<|Y_n|`$ gives the normalized strict sign. The paper's signed differences between adjacent cycle weights may have either sign and the bounds take their absolute values. At $`x=0`$ the sign is part of the same statement. For $`t<-1`$, reciprocity gives a factor $`-t^{2p-5}>0`$ on the quotient sign product when passing to $`1/t`$. This supplies the other half of the negative axis.

The analytic cutoff-four theorem combines a compact comparison through $x=16$, its middle interval through $3\sqrt p$, and the exterior. Cutoff five uses $x=11$ for the first join and cutoff six uses $x=13$. Both make the same exterior join. The top-level declarations apply the normalized sign to actual predecessor zeros for the whole closed weight cube, including the hard cutoff. A continuous path to the derangement profile preserves the common short-weight assumptions at both sizes. The strict sign at every real old root excludes collisions, the derangement anchor gives a full real splitting, and the next-row signs give strict interlacing. I checked this sign wiring and the elementary budgets listed below. The upstream analytic proofs supply the complex-contour and exterior estimates.

## Local exact replays

I verified the release tags against the exact commit IDs, and checked each downloaded byte count and Git blob digest against its pinned commit tree. The cutoff-six frozen inner archive and its top-level theorem module also match the SHA-256 values in the supplying release. Only the needed source excerpts and certificates were retrieved. [Pinned source inventory](pinned-sources.tsv) · [Reproduction script](fetch-pinned.py)

- **Cutoff four.** The supplied checker passed with `--last 511`. It reconstructed original ordinary rows 4–511 by the insertion formula and checked direct permutations through size 8. It checked 507 consecutive pairs, 64,770 gamma brackets and 129,540 integer endpoint signs. The disjoint bracket count fills the gamma degree, and the increasing map from $-1<t<0$ to $t/(1+t)^2$ plus parity and reciprocity recovers all quotient roots. The release archive extends to row 1023. The local full-prefix command used the theorem's cap 511. A separate rational spot-check confirmed elementary bounds in the cutoff-four compact, middle and exterior sign budgets. [Finite replay](k4-finite-replay.txt) · [Scalar check](check-four-scalars.py) · [Scalar replay](k4-printed-scalars-replay.txt)
- **Cutoff five.** The supplied `certificates/finite.py` passed for 43 pairs at upper sizes 6–48. Two coefficient recurrences agreed, and literal permutations checked sizes 5–8. Its 1,032 strict primitive remainder drops gave SHA-256 `05f624d90c8a66d686f30504f3eea7b201b26dbb971a1531af6dfc176051a7d7`. Each signed remainder has degree one less and positive leading coefficient, with a positive terminal constant. Backward sign alternation gives all simple real roots and strict interlacing, and positive quotient coefficients exclude nonnegative roots. The supplied scalar, 88-cell compact and middle checks also passed. [Finite replay](k5-finite-replay.txt) · [Scalar replay](k5-scalar-replay.txt) · [Compact replay](k5-compact-replay.txt) · [Middle replay](k5-middle-replay.txt)
- **Cutoff six.** The supplied `numerics/fixed-six-effective/check.py` passed for 42 pairs at upper sizes 7–48. It checked both exact row recurrences, literal permutations at sizes 6–9, and 1,029 signed remainder drops with SHA-256 `a313525d598cd2ec7a934937e9fe325c33757342d9bcf21ca8eafdc2307a3074`. Its 104-cell compact, middle and exterior scalar checks passed, as did the separate check for the manuscript's printed scalar budgets. The two combined outputs match the upstream arithmetic log byte for byte. [Finite and interval replay](k6-finite-replay.txt) · [Printed scalar replay](k6-printed-scalars-replay.txt)
- **First analytic pairs.** A separate endpoint script tested $(511,512)$ using the stored cutoff-four certificate. It checked all 509 stored gamma brackets and their exact ordering against reconstructed rows. That script used the supplied ordinary row recurrences and remainder procedures to test $(48,49)$ for cutoffs five and six. Each has 46 positive signed remainder drops. These supplemental checks use supplying arithmetic and witness data beyond each finite theorem cap. [Endpoint check](verify-analytic-joins.py) · [Endpoint replay](analytic-joins-replay.txt)

The local commands use Python 3.13.5 and standard-library integer or rational arithmetic. Start in this directory and run the scripts from a temporary directory for the downloaded sources.

~~~sh
scope_source=$PWD
scope_replay=$(mktemp -d)
cp fetch-pinned.py check-four-scalars.py verify-analytic-joins.py "$scope_replay/"
cd "$scope_replay"
python3 -I -B fetch-pinned.py
cmp pinned-sources.tsv "$scope_source/pinned-sources.tsv"
(cd 4 && python3 -I -B certificates/k4/verify.py certificates/k4/certificate.txt.gz --last 511)
(cd 5/cutoff-five && python3 -I -B certificates/finite.py)
(cd 5/cutoff-five && python3 -I -B certificates/check.py)
(cd 5/cutoff-five && python3 -I -B certificates/compact/verify.py)
(cd 5/cutoff-five && python3 -I -B certificates/middle/verify.py)
(cd 6/cutoff-six && python3 -I -B numerics/fixed-six-effective/check.py)
(cd 6/cutoff-six && python3 -I -B cutoff-six-scalar-check.py)
python3 -I -B check-four-scalars.py
python3 -I -B verify-analytic-joins.py
~~~

## Upstream formal evidence

The cutoff-four release reports a Spark audit with 128 verified tail objects matched byte for byte, 295 other modules rebuilt and individually replayed, and 12 declaration audits. The cutoff-five release identifies an isolated frozen source closure of 180 Lean files and the separate `CutoffFiveFinalAudit` entry. The cutoff-six release records a source-cold Spark run on its frozen archive, independently replaying 182 modules and checking 13 declarations. Its errata correct two comments about the smallest coefficient order without changing the signatures or bodies. These are the supplying release's formal records. This audit inspected source and performed the arithmetic checks above. Build and axiom outcomes from this repository's independent Lean jobs are recorded in the separate PR. [Cutoff four upstream receipts](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/tree/f8fef864286a1bbc59f96484074f28d77b1a027f/verification) · [Cutoff five frozen entry](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/70cad373bce521d78d6de9bcff3d29d07fc7fe9f/cutoff-five/formal/CutoffFiveFinalAudit.lean) · [Cutoff six upstream receipts](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/cutoff-six/verification/FORMAL-STATUS.md)

The independent pinned rebuilds of all three supplying projects passed. The final receipts give the original lower-size comparison theorems and their transitive axiom reports. [Complete rebuilt release records](../README.md)
