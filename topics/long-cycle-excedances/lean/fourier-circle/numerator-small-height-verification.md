# Verification of the small-height numerator contraction

The hosted Lean 4.19.0 build compiled all five numerator modules at [commit a21568d](https://github.com/ProgramComputer/open-math-research/tree/a21568d6df22bc228bdbe5901ce953367f8d5665). The compiler commit is 6caaee842e94 and the mathlib revision is c44e0c8ee63ca166450922a373c7409c5d26b00b. The full dependency set is in the [Lake manifest](../../../../shared/lean/lake-manifest.json). [Hosted run 46011222686](https://github.com/ProgramComputer/open-math-research/actions/runs/46011222686).

The [checker](check.py) hashes the exact Lean inputs, compiles each source to an object with Lean, and checks its named axiom reports. All ten new declarations report only propext, Classical.choice, and Quot.sound. The source digests matched the Git blobs. [Reproduction instructions](numerator-small-height.md#formal-scope).

The exported [contraction theorem](NumeratorLogSeries.lean) bounds the two Taylor contractions of the explicit odd-pole log series together by 2997/100. Its hypotheses are cutoff at least 100, height between zero and four times the square root of the cutoff, outer radius between one and one plus the reciprocal cutoff in normalized coordinates, and two unit complex directions. The analytic logarithm identification, finite cutoff-polynomial bridge and large-height estimates are separate parts of the numerator argument.

The authenticated CI job log has SHA-256 50a38fd212aefb4e29cbb2b1a3e17d41b8fd2ee3eee16e73adddda73911242aa. [Job 140546931485](https://github.com/ProgramComputer/open-math-research/actions/runs/46011222686/job/140546931485).

| Lean source | SHA-256 |
| --- | --- |
| [NumeratorPoleVolume.lean](NumeratorPoleVolume.lean) | dd2d7143c5a5c18b86a56dbadc40b4c193463e2e93c5183041cd1108a702b478 |
| [NumeratorOddPoleMoment.lean](NumeratorOddPoleMoment.lean) | 66d3dd3c9501a666a8d7b5418ada87e4a58a902d128c27ee3ce01fdf6617522c |
| [NumeratorRadialScalars.lean](NumeratorRadialScalars.lean) | 9464a351b9852405e20e7e7ac0856e2d935a61668dc623d61ef8a0c48108696c |
| [NumeratorTaylorContraction.lean](NumeratorTaylorContraction.lean) | 8a59d7be02856be4b99c7897def6ac1b88adc03d1cf375d4d2df3e204de492de |
| [NumeratorLogSeries.lean](NumeratorLogSeries.lean) | 573fce24a85075a73bd3a5af6e2d61661ad3d0688afc95ef564a35954c93b14a |

Integration preserved the exact Fourier source hashes, compiler and dependency pins, and module order within both previously hosted manifests. The merged checker includes all 47 denominator-package declarations and the ten numerator additions. [Denominator-package verification](principal-denominator.md).
