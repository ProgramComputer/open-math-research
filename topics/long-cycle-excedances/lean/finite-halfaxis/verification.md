# Lean receipt for the first cutoff-eight finite pair

[Hosted audit 46035691089](https://github.com/ProgramComputer/open-math-research/actions/runs/46035691089)
passed at source commit `c29022c88df03e8e48b9e0cfdfc0c5ba7e68f821`.
Lean 4.33.1 reported compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
on Linux x86-64. Mathlib is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`.
The supplying cutoff-six source by Bowen Zuo is frozen at
[`46dc6e9`](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/tree/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554).
The driver verified its archived source and package lock, and verified the
retained import-object archive with SHA-256
`000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05`.

The exact statement is
[`RepositoryQuotientAudit.HalfAxisFirst.original_strict_and_weak_cutoff8_size32`](CutoffEightFirstPair.lean).
It proves strict negative interlacing for the quotients of the original
permutation excedance rows at cutoff eight, with degrees 30 and 31. It also
proves weak real interlacing for the original rows, which share a root at zero.
Twenty-five checked insertion steps and the checked seed identify the two
literal coefficient lists. The proof checks 15 half-axis windows with four
strict signs per window, then accounts for all roots by the existing reciprocal
half-axis assembly. The generic interval consumer is proved with certificate
premises. Only the pair with old size 32 is instantiated here.

The 15 window literals match the first pair in the compact archive from
[#331](https://github.com/ProgramComputer/open-math-research/pull/331).
Its uncompressed SHA-256 is
`95f445fa4e7864984c33ca44eb2f83a8295a628721e0b65bf523fb55265490e8`.
An independent exact-arithmetic check used the recurrence that distinguishes
the cycle containing label 1. It matched all 832 zero-padded coefficient slots
for sizes 8 through 33 and verified all 60 endpoint signs.

Reproduce by running the following command from the repository root with the
pinned Lean on the path. Omit the second argument to rebuild the imports.

```sh
python3 -Bu topics/long-cycle-excedances/lean/finite-halfaxis/check.py \
  /tmp/halfaxis-pin /path/to/quotient-import-objects.tar.zst
```

The driver compiled the new modules with `-DwarningAsError=true` and replayed
each with the toolchain's bundled `leanchecker --verbose`. All six new module
replays returned zero. All seven named declarations used only `propext`,
`Classical.choice`, and `Quot.sound`. This receipt uses the bundled checker.

| Module | Checked source SHA-256 |
| --- | --- |
| `ExactInsertionTable` | `a28021a313c639063f97d7ebca058a5e3ca31ef22a68bed41cfa71cf1486d5a9` |
| `RepositoryStrictHalfWindows` | `6fe280ccdd77762fae11736bce1373435c12d7c4d7d429f40cc78254bbb6f502` |
| `HalfAxisDyadic` | `69990ec3b6e63bc2769729880a434b8a27002597bfa36f6d83547a84462813ff` |
| `HalfAxisBlock` | `e643f03680343c0bb8a529eec311854390e076e81eea7da683eceedfe8f8479b` |
| `CutoffEightRows` | `509fe257619eb585cf2c026cedba8dfc7ae51fc62515fdc95a6acfe3b243c035` |
| `CutoffEightFirstPair` | `5988859dfbe5dc8feab665a1e741fa0a452a78deccf7c848a6523f5cc603b9b3` |

The hosted `finite-halfaxis.log` has SHA-256
`8a2f5cd676583300f95bf34c8f7203428204066d9fed9e307b47c3f4f9b4e6bf`.
Its source digests and axiom readouts match the listed commit.
