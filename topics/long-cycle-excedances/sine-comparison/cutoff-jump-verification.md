# Lean verification of the cutoff jump

The proof uses Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The frozen upstream source is `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. The dependency check authenticates the optional retained upstream object archive with SHA-256 `000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05`.

The paired-profile job compiled and separately replayed 98 modules with the pinned toolchain’s kernel checker and audited 160 declarations. GitHub reported PR head `5126b37e1236d093d36b52564fff715c471e9f30` and checked out merge commit `c2fc665fd032c809e1d2e76d1bb2bb9c0b2afd6d`. All 98 compiler inputs matched that checkout. The cutoff modules also matched the PR head byte for byte. The report ZIP, artifact `15195928528`, matched SHA-256 `f0086d61f1c4eb60695242be631d1763f99a5f654888dd2972a41577cffd5df7`. [Pinned paired-profile job](https://github.com/ProgramComputer/open-math-research/actions/runs/45994181880)

| Source | Compiler input SHA-256 |
| --- | --- |
| `CutoffSinglePrimitive.lean` | `f5263e5b8a32282153104e338cbc72d6802f05117204998630455a4d56f01525` |
| `CutoffSingleSlabs.lean` | `32f3918f4cdb288548b7921c241e50569a7510491fd99800968178550f1e6b68` |
| `RepositoryCutoffJump.lean` | `a02be250c28574c2dfff0369c063cee7ae428e20811378ba56cbe4ff352b371c` |

The audited theorems include `single_cutoff_primitive_lattice`, `single_cutoff_slab_of_spec`, `cutoff_jump_split` and `original_cutoff_jump_head`. Their transitive axioms are `propext`, `Classical.choice` and `Quot.sound`. The primitive-envelope job independently checked 41 source hashes, replayed 17 roots and audited 37 declarations. Its report ZIP, artifact `15194469286`, matched SHA-256 `efaca53d638ae0376024a9ffda17b4d1bb635152516298e776f69beedc1cda08`. The exact arithmetic job reproduced the stored interval bounds. [Primitive-envelope job](https://github.com/ProgramComputer/open-math-research/actions/runs/45994181744) · [Exact arithmetic job](https://github.com/ProgramComputer/open-math-research/actions/runs/45994182131)

The combined cutoff and principal-cost driver passed from PR head `721de6ef75f86eee3bbaf2438924a497d94d1c02`. GitHub checked out the identical tree at merge commit `d72fb25b2924ab1d8269623e888a3f0188b7d7be`. All 103 source hashes, all 103 kernel replay markers and all 172 named axiom reports matched. The combined report ZIP, artifact `15197586973`, matched SHA-256 `8d535ac6fce02b929b4c97d67247f0138a26e4f2ee7afc5677565b5826958d04`. The primitive-envelope and exact arithmetic jobs also passed on this head. [Combined paired-profile job](https://github.com/ProgramComputer/open-math-research/actions/runs/45997691035) · [Primitive-envelope job](https://github.com/ProgramComputer/open-math-research/actions/runs/45997690957) · [Exact arithmetic job](https://github.com/ProgramComputer/open-math-research/actions/runs/45997690969)

With the pinned Linux toolchain on PATH, run from the repository root using fresh output directories.

```sh
python3 -Bu topics/long-cycle-excedances/lean/paired-profile/check.py "$RUNNER_TEMP/cutoff-profile"
python3 -Bu topics/long-cycle-excedances/lean/sine-comparison/check-primitive-envelope.py "$RUNNER_TEMP/cutoff-primitive"
cd topics/long-cycle-excedances/sine-comparison
python3 -I -B check-cutoff-jump.py > "$RUNNER_TEMP/cutoff-jump.txt"
diff -u cutoff-jump-output.txt "$RUNNER_TEMP/cutoff-jump.txt"
```
