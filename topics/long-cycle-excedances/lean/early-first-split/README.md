# Strict interlacing through the first cycle split

For each cutoff $k\ge8$ and lower size $k\le n<2k$, the original consecutive excedance rows have strictly interlacing negative roots after removal of their shared simple zero. Their literal rows weakly interlace. The upper size is $n+1$, so the range includes $(2k-1,2k)$, the first pair for which the successor can contain two cycles. The Lean theorem is `OpenMathResearch.LongCycleExcedances.original_through_first_split`. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Lean theorem](RepositoryThroughFirstSplit.lean)

The single-cycle interval and the first split for $k\ge55$ use Bowen Zuo’s pinned theorems through the [canonical quotient adapter](../early-sector/README.md). For $8\le k\le54$, each case uses Zuo’s exact original factorizations and `LongCycleFinite.firstSplitStrict_of_checked` from commit `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. The finite data supplies the gamma coefficients, the outer dyadic point, and disjoint dyadic windows around the old gamma roots. Lean checks window order, directed Horner signs window by window, both coefficient identities, and the reduction to the original permutation rows. The generated Lean source uses one module per cutoff. [Zuo’s release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.2.0) · [Certificate data](first-split.jsonl) · [Source emitter](emit.py)

The finite cases are every integer cutoff from 8 through 54. Their 47 pairs contain 1,363 windows and 5,546 sign evaluations. The independent Python checker derives the original coefficients via the Eulerian recurrence and the cycle of label one, reconstructs the gamma expansion via binomial coefficients, and uses exact homogeneous Horner evaluation. The generator uses real root approximations to locate candidate endpoints and accepts them only after rational and directed-integer checks. The production Lean checker uses the frozen data, so neither approximation software nor the Python verifier is in the Lean proof’s trust base. [Independent verifier](verify.py) · [Generator](generate.py)

An agent-assisted review checked the bridge against the literal rows and both quotient factorizations. It confirmed the lower and upper sizes, the reduced degree $2k-3$, the partition at cutoff 55, and the two cases $n+1<2k$ and $n=2k-1$. The reviewer developed the certificate data independently of the bridge and ran the integer verifier separately. The reviewer also checked that the exponent equals the suffix length at every window, so the separate kernel decisions assemble the exact upstream `signsOK` and `caseOK` propositions.

The first uncovered lower size in the small-aspect Lean ledger is now $n=2k$. That pair requires a checked successor-sign argument at the old roots. The broader two-cycle and three-cycle intervals are addressed by the reviewed paper proofs. [Small-aspect scope ledger](../early-sector/README.md) · [Two-cycle proof](../../two-cycle-band.md)

From the repository root, run the arithmetic replay and the pinned Lean audit.

~~~sh
python3 -I topics/long-cycle-excedances/lean/early-first-split/verify.py \
  topics/long-cycle-excedances/lean/early-first-split/first-split.jsonl
python3 -Bu topics/long-cycle-excedances/lean/early-first-split/check.py /tmp/long-cycle-first-split
~~~

The optional generator reproduced the frozen file byte for byte with Python 3.13.5, python-flint 0.9.0, and FLINT 3.6.0.

~~~sh
uv run --with python-flint==0.9.0 python \
  topics/long-cycle-excedances/lean/early-first-split/generate.py 8 54 \
  > /tmp/first-split-regenerated.jsonl
cmp /tmp/first-split-regenerated.jsonl \
  topics/long-cycle-excedances/lean/early-first-split/first-split.jsonl
~~~

## Verification

The pinned Linux build passed with Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. GitHub checkout `13fc084f211bc39810687f7ad47d5d610413f99e` used PR head `5fd30cfe8089037ae7148193ef80e8ee176bbd09`. The receipt matches 51 compiler input hashes and 51 bundled Leanchecker replays, including each of the 47 case modules, the finite aggregation, the literal-row theorem, and the two early-sector inputs. All 56 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Report artifact `15219691926` matched SHA-256 `4a73b713c8defb4dc43e7ec839bb296d4be87ba54c047c5f01fc542b97fd0128`. [Pinned build and replay](https://github.com/ProgramComputer/open-math-research/actions/runs/46036154137) · [Complete input digest ledger](receipt.json)

The first production attempt reached the certificate emitter and found a name collision between two types called `Dyadic`. Qualifying Zuo’s type resolved the port. The retry with a single kernel decision for all the signs in each case was superseded by the successful run with a separate decision per window. Both retries used the same certificate data and theorem statements. [Initial diagnostic](https://github.com/ProgramComputer/open-math-research/actions/runs/46035388113) · [Superseded retry](https://github.com/ProgramComputer/open-math-research/actions/runs/46035724126)
