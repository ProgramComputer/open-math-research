# Finite dyadic windows for the original excedance rows

The files here target the literal cutoff-eight pair on 32 and 33 labels. They
use the 15 positive-modulus brackets for old size 32 from the independent
[compact archive in PR #331](https://github.com/ProgramComputer/open-math-research/pull/331).
The check authenticates the uncompressed archive and compares each embedded
window with its corresponding archive record.

- [Exact insertion table](ExactInsertionTable.lean) certifies zero-padded
  coefficient lists against the original permutation counts. It uses the
  checked original insertion formula and single-cycle seed from the
  [compact row package](../compact-rows/README.md).
- [Dyadic consumer](HalfAxisDyadic.lean) uses Bowen Zuo's verified directed
  Horner arithmetic and the existing
  [half-axis assembly](../common-pin/RepositoryHalfAxisAssembly.lean).
  The [strict promotion](RepositoryStrictHalfWindows.lean) reuses its complete
  root lists before adjoining the common root at zero.
- [Block consumer](HalfAxisBlock.lean) applies one certified table and a
  family of checked window lists to an interval of old sizes.
- [First-pair specialization](CutoffEightFirstPair.lean) targets
  strict negative interlacing of the reduced rows and
  `WeakRealInterlacing (enumerator 32 8) (enumerator 33 8)` for the original rows.
  The reduced old and next rows have degrees 30 and 31, respectively.
  The original rows share a root at zero.

Run `python3 -Bu topics/long-cycle-excedances/lean/finite-halfaxis/check.py /tmp/halfaxis-pin`
from the repository root with Lean 4.33.1 available. The optional second argument
is the authenticated common-pin import archive. The runner logs source hashes,
the frozen pins, named axiom audits and bundled LeanChecker replay.
See the [exact-source Lean verification receipt](verification.md). The archive
also covers larger sizes outside this first-pair verification.
