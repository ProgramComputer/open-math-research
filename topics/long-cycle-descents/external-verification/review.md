# Independent audit of Bowen Zuo’s ordinary-descent release

**Agent-assisted review, 26–27 November 2026.** I compared Theorems 1 and 2 of release v1.0.0 with Alexandersson’s ordinary-descent question and the Lean theorem types at commit `e632c19bc246b819cd6b882cbf22c2fa9bc453de`. The mathematical statement is an exact match for the original row real-rootedness question. The stronger assertion concerns nonnegative mixtures of entire cutoff rows at a single size. [Original question](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles) · [Reviewed release](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/releases/tag/v1.0.0)

## Original objects and theorem scope

The Lean admissibility predicate `LongCycles.Allowed` requires every label to avoid a positive return under the permutation in fewer than $k$ steps. Since the least positive return time is the cycle length, this is exactly the minimum-cycle-length restriction. `LongCycles.descents` counts pairs of original one-line positions $x$ and $x+1$ with a strict descent. The last position has no successor in `Fin n`. `LongCycleBounds.DescentTwoLetters.row` sums $X$ raised to this descent count over the admissible finite permutations, with neither normalization nor change of statistic. `DescentBoundary.realRow` maps its integral coefficients into the reals. `DescentBoundary.mixture` sums precisely over `Finset.Icc 1 n` for one fixed $n$.

Theorem 1 splits the original row over the reals for every integer pair $3\le k\le n$. For $n\ne5$, the formal all-size root assertion gives degree $n-2$, distinct roots in the multiplicity-counting roots multiset, a root at zero, and $n-3$ negative roots. It therefore certifies a simple common factor $t$. The formal common-interval predicate gives one root per disjoint open negative interval for every supported mixture at that same size. For $n=5$ the factorization is $6t(1+t)^2$ for each $k$ from 3 through 5. Dividing by the simple factor $t$ leaves the double root at $-1$. At $n=3$ the open-interval family has size zero and the only root is zero.

Theorem 2 is formally stated with nonnegative weights on $1,\ldots,n$ and a positive sum. Its conclusion includes a nonzero polynomial, real splitting, and a nonpositive bound on every root. The `Nodup` equivalence gives exactly the two exceptional supports. The corresponding four- and five-letter identities identify the double factors. If $w_1$ is positive the constant term is positive and zero is absent. If $w_1$ is zero, the one-descent $n$-cycle gives a simple root at zero whenever a cutoff row has positive weight. The $n=1$ mixture is a positive constant.

These statements quantify over the cutoffs at a fixed $n$. For comparison, consecutive interlacing holds $k$ fixed and compares size $n$ with size $n+1$. The shared isolating intervals can depend on $n$. In particular, the weak consecutive ordinary-descent interlacing condition fails at old size 5 for $k=4$ and $k=5$, even after division by $t$. The old row has two copies of $-1$ and the new row has value $8$ at $-1$ before division by $t$, whereas an alternating ordered list with the degree increasing by one would require a new root between the copies. A separate literal enumeration computes both statistics in these cases and confirms that the ordinary descents and excedances give different polynomials. [Direct traversal](arithmetic/compare.py) · [Output](arithmetic/output.txt)

## Independent checks completed locally

The clone was clean and at the exact tag commit. I checked the manuscript bridge from admissible increasing labelings to primitive necklace inventories. The binomial factor indexed by the ordinary descent count sends a permutation with $r$ descents to $t^r/(1-t)^{n+1}$, which matches the generating function and the Lean bridge `original_eq_descentTransform`. The ambient reversal changes the alphabet polynomial by a sign and $q$ to $-q$ and gives the opposite half-axis signs at the same size. The alternating same-size signs, zero root and degree bound give the required root count. For the mixture theorem the endpoints are $P(0)=w_1$ and the coefficient of $t^{n-1}$ is $w_1$ plus $w_2$ for even $n$. These identities give the extra outer roots required by the degree count. The weak endpoint cases at sizes four and five are resolved by the exact exceptional factorizations.

Running the two commands below reproduced the 531 artifact hashes and 499 proof-source receipts. The finite test recovered 8,001 nonempty rows represented by 4,032 distinct input cases through size 127, with no failed real-rootedness test. It replayed 327,451 exact shared signs and 15,740 boundary-family signs. Additional arithmetic checks include the derivative-free tail margins and the two exceptional supports. [Release integrity log](release-replay.log) · [Finite replay log](finite-replay.log)

~~~sh
python3 -I -B scripts/verify.py
python3 -I -B paper/reproduce.py finite
~~~

## Formal reproduction status

Lean pin is 4.33.1, toolchain commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. The lock SHA-256 is e130828f38a395281f51f4cec3ad5f3e08784f5e7dd973aa85d7efb9f2267a21. The nine dependency revisions are:

| Dependency | Revision |
| --- | --- |
| Mathlib | 0df444a360eaa60ab8c11dca51a86af692955474 |
| plausible | b7eb3304aeae834b12dda98993a37f6a41f6f0bb |
| LeanSearchClient | 5f4d51b81cbd3f6b32b156bfad9056621a040404 |
| importGraph | 16f02aa7642864af59f1ff0e384a015994db9118 |
| proofwidgets | 4be2e3d5087eeb272cf5a8853b8f9dd025ef5957 |
| aesop | 3448c0bcc5ce01b2d1546e483ec3620e32df3d0e |
| Qq | 92c15be17b7caf78c2ad767ec40f89052d908d81 |
| batteries | 4488d40d070b9700d4d5a6aa342f0d40c31b2a2d |
| Cli | 6130a47896ce867c6a4a55373441e59e565bad0f |

The supplied transcript records the author’s strict 499-module build and a separate run of LeanChecker. In our first independent job all 499 modules compiled, and the 22 transitive axiom reports matched the release. Its print wrapper selected a pretty-print option unavailable on this Lean release. Removing that option allowed the clean retry to complete. Both independent runs printed the same six definitions and eight theorem types. Each audited declaration uses only `propext`, `Classical.choice` and `Quot.sound`. The retry also confirmed that the checked-out release source stayed clean. The independent jobs used strict compiler builds with cached objects for the pinned dependencies. [Original audit module](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/blob/e632c19bc246b819cd6b882cbf22c2fa9bc453de/formal/AllCutoffsManuscriptAudit.lean) · [Clean hosted check](https://github.com/ProgramComputer/open-math-research/actions/runs/45925826846) · [Exported statements, pins and audit record](ordinary-retry-compiled.txt)

**Conclusion.** Bowen Zuo’s release proves Alexandersson’s ordinary-descent real-rootedness conjecture at every admissible size and cutoff. The exact statement comparison and the independent pinned Lean rebuild pass. The release also establishes the stated fixed-size cutoff-mixture theorem. [Reproduction commands and arithmetic checks](README.md)
