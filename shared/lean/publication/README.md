# Recheck a published Lean result

The baseline is the public research release at commit `312293aa850010e9d9509d6850a482b9c7b7966f`. The release audit uses Lean 4.36.0 at `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` and mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The manifest pins each Lake dependency. The independent kernel is the Rust implementation Nanoda at `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, bundled with the Linux Lean release. [Lean release](https://github.com/leanprover/lean4/releases/tag/v4.36.0) · [Mathlib revision](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842) · [Nanoda source](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27)

## Published claims

| Claim | Stable build and axiom audit | Independent kernel |
|---|---|---|
| [Strict peaks in Catalan words](../../../topics/catalan-word-peaks/verification.json) | Port in progress | Pending |
| [Splitting a prism-slice bound](../../../topics/prism-splitting/verification.json) | Passed, 64 declarations | Passed, 28,385 declarations |
| [Balanced binary arrays](../../../topics/balanced-arrays/verification.json) | Passed, 30 declarations | Outside the Partial audit |
| [Ordered partitions with large blocks](../../../topics/ordered-large-blocks/verification.json) | Passed, 30 declarations | Outside the Partial audit |
| [Eulerian matrix square](../../../topics/eulerian-matrix-square/verification.json) | Passed, 5 declarations | Outside the Partial audit |
| [Ribbon matroids](../../../topics/ribbon-matroids/verification.json) | Passed, 13 declarations | Outside the Partial audit |

The four Partial rows cover the components identified in their topic records. A separate [upstream source rebuild](https://github.com/ProgramComputer/open-math-research/actions/runs/45762866977/job/139716713982) completed all 5,930 Lake jobs for the 75 distinct direct mathlib imports and their prerequisites. The manifest records 2,671 rebuilt mathlib objects. [Import list](upstream/roots.txt) · [Object hashes](upstream/olean-sha256.txt.gz)

## Reproduction

Use a checkout containing the baseline Git object, Python 3, Git, GNU patch and the pinned Lean toolchain. From the repository root, choose one of `catalan`, `prism`, `balanced`, `ordered`, `eulerian` or `ribbon`. Start with an empty build directory.

~~~sh
topic=catalan
build_dir=$(mktemp -d)
python3 shared/lean/publication/prepare.py "$topic" "$build_dir"
(
  cd "$build_dir"
  lean --version
  lake exe cache get $(cat cache-imports.txt)
  test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
  lake build $(cat targets.txt)
)
python3 shared/lean/publication/audit_axioms.py "$topic" "$build_dir"
~~~

The staging script reads published sources from Git, applies the stable-version ports, and records a SHA-256 digest for each file it hands to Lean. The build compiles the repository modules and their local imports from source. The fast replay fetches exact-version mathlib objects. The separate upstream rebuild compiles the union of the imported mathlib modules and their prerequisites from source. The release toolchain supplies Lean's standard library. [Package audit workflow](../../../.github/workflows/publication-lean.yml) · [Upstream rebuild](../../../.github/workflows/publication-dependencies.yml)

Each named declaration has a fresh `#print axioms` report. The check fails on a missing report or an axiom outside `propext`, `Classical.choice` and `Quot.sound`. A narrower axiom set is recorded verbatim. [Declaration inventory](declarations.json)

For the two Full entries, use the Linux release's exporter and both checkers. Use a fresh artifact directory. The exported roots include the original public theorem and the separate statement-comparison declarations.

~~~sh
artifact_dir=$(mktemp -d)
bash shared/lean/publication/replay-kernel.sh "$build_dir" "$artifact_dir" "$topic"
~~~

The replay records the export hash, reachable declarations, axiom set, checker binary hashes, and verdicts. A passing Lean build alone does not certify a Nanoda replay. See each topic's verification record for executed commands and outcomes.
