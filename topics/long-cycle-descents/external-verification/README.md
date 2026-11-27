# Independent replay of Zuo’s ordinary-descent result

Bowen Zuo’s v1.0.0 release settles real-rootedness for the ordinary-descent row for every integer pair with cutoff at least three and at most the row size. The admissible permutations have every cycle length at least the cutoff, and the exponent counts strict descents in the original one-line permutation. The same release proves that every nonzero nonnegative mixture of the cutoff rows at a single size, including the Eulerian and derangement rows, has only real nonpositive roots. Its printed theorems include the repeated-root exceptions at sizes four and five. Consecutive-size interlacing for excedances is a separate assertion. [Supplying release](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/releases/tag/v1.0.0) · [Alexandersson’s statement and attribution](https://www.symmetricfunctions.com/realRootedWords.htm#longCycleDescentsRealRooted) · [Independent comparison with the original statement](review.md)

## Hosted result

The corrected ordinary-only retry passed its strict build, axiom audit and theorem-print wrapper. It independently reproduced all 499 local compiler receipts and 22 transitive axiom reports on the same frozen source and toolchain pins and confirmed that the tracked release source remained clean. Its six definitions and eight theorem types match the output below from the first job. The pinned external proof has been independently rebuilt and checked against Alexandersson’s ordinary-descent statement. [Successful retry](https://github.com/ProgramComputer/open-math-research/actions/runs/45925826846/job/140266811471) · [Clean retry record](ordinary-retry-compiled.txt)

### First run

The read-only Linux x86_64 job completed a fresh strict build of all 499 local Lean modules, with warnings treated as errors. The evidence check matched each compilation receipt to the exact source digest in the frozen release. The checked release commit is `e632c19bc246b819cd6b882cbf22c2fa9bc453de`. The separately downloaded distribution ZIP matched SHA-256 `9a6adec1f312d874b7716b1393eb45361d8cb78c78058a75bfeb9da895706a97`. The job used Lean 4.33.1 at compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. All nine external source pins and the uploaded artifact digest matched. Each of the 22 distinct transitive axiom reports recovered from the strict compiler log lists only `propext`, `Classical.choice` and `Quot.sound`. [Hosted job](https://github.com/ProgramComputer/open-math-research/actions/runs/45907318583/job/140207053788) · [Durable console record, exported definitions and theorem types](ordinary-compiled.txt)

The overall job exited with failure after the strict build and axiom audit had passed. The print-only wrapper used the unsupported Lean option `pp.width`. Lean still printed all requested definitions and theorem types. The later axiom-copy and tracked-source-status steps were skipped. The compact record includes the complete axiom block from the successful strict compiler log and checks its hash against the audit module receipt. Removing the unsupported option fixed the print wrapper in the clean retry above. The hosted log bundle and the supplying release contain no compiled objects, so there are no matching objects available for a standalone print rerun.

Both runs used `build` mode, with Mathlib dependency objects from its artifact cache. The upstream transcript records a separate LeanChecker pass and the independent hosted runs record the strict Lean rebuilds. The upstream release contains no Rocq proof. The independent comparison in [the review](review.md) was written before the hosted job finished. Its scope assessment matches the complete types printed after the option diagnostic.

## Finite arithmetic

The local replay verified 531 release artifact hashes and independently reproduced the finite certificate through size 127. It covered 8,001 nonempty rows represented by 4,032 cases, 327,451 exact shared-grid signs and 15,740 boundary-family signs. Literal one-line enumeration independently checked the definitions and exceptional cases. [Release replay](release-replay.log) · [Finite replay](finite-replay.log) · [Literal permutation enumeration](arithmetic/compare.py) · [Enumeration output](arithmetic/output.txt)

## Reproduction

Run the hosted entrypoint on Linux x86_64 with `PrintOrdinary.lean` beside it. It requires Git, curl, GNU tar with zstd, sha256sum, Python 3.11 or newer, and about 35 GiB of free disk space. The hosted job used two workers with swap and a soft open-file limit of 65,536. The upstream guidance budgets about 10 GiB of memory per compiler or replayer and at least 24 GiB for two workers. The default is one worker. Set `ORDINARY_AUDIT_MODE=full` and allow a longer run to include the release driver’s separate LeanChecker process per module.

~~~sh
ORDINARY_AUDIT_JOBS=2 ORDINARY_AUDIT_MODE=build \
  ORDINARY_AUDIT_LOG_DIR=/tmp/ordinary-audit-logs bash run-ordinary.sh
~~~

The finite reproduction commands run from the pinned upstream checkout.

~~~sh
python3 -I -B scripts/verify.py
python3 -I -B paper/reproduce.py finite
~~~
