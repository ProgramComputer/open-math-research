# Verification of the full principal pole product

**Passed on Lean 4.33.1.** The checked source commit is `4002b359a2fcf768249a94a4d0fc1c2e794bff83`. The hosted Linux build used Lean compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. [Source comparison](https://github.com/ProgramComputer/open-math-research/pull/289/files) · [Successful build](https://github.com/ProgramComputer/open-math-research/actions/runs/45978721324)

For every cutoff at least two, the literal probability differences defining the cycle numerator give an absolutely convergent series at every complex argument. At the principal angular denominator the product of the actual occupied factors over all other signed poles equals the exponential of the sum of their radial logarithms. These logarithms are absolutely summable, including the term at the conjugate pole. The real-part estimate in this package takes a scalar lattice bound as a hypothesis. The quantitative bounds for that sum and the full adjacent-row determinant are outside this audit. [Statements and mathematical proof](entire-numerator.md) · [Whole-lattice theorems](PrincipalLatticeProduct.lean)

The driver checked all 38 compiled source files by recording their SHA-256 digests and replaying each module with the Lean distribution’s `leanchecker`. The 74 registered axiom reports contained only `propext`, `Classical.choice` and `Quot.sound` or a subset. The hosted driver authenticated its shared import archive as `000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05`. The downloaded build log was separately matched against the checked commit for every input hash, replay exit and registered axiom report. This was an agent-assisted verification.

| Record | SHA-256 |
|---|---|
| [Archived job output](https://github.com/ProgramComputer/open-math-research/actions/runs/45978721324/artifacts/15188362972) | `b76bd20e53c9a479a97a7796feaadbd3ae4426bee3cb3ef3adc4cad6372e39ab` |
| Extracted `paired-profile.log` | `c12913a82e1122f1753058d3d9e91ccda5c695fd3af8a8866bd8c5693276196d` |
| `EntireCycleEvaluation.lean` | `23f6db1d9e4ca3fa6a117b85fd8eb0c56ff1caf967459378056b8f884e5e62c8` |
| `RepositoryPrincipalFactor.lean` | `6767d29a30e110b13beaa6a639e55b612dbab0b2ec45e255653f6adcd4e9f582` |
| `PrincipalLatticeProduct.lean` | `4fc81ccdd9308cbd899fa3a8976a834196a6c0970bf82fd446cbea9289f75a9c` |

From the repository root run

~~~sh
python3 -I topics/long-cycle-excedances/lean/paired-profile/check.py /tmp/principal-verification
python3 -I topics/long-cycle-excedances/lean/paired-profile/check-entire-numerator.py
~~~

The second command reconstructs all 90 arithmetic examples from permutations and an independent finite product. Earlier port failures involved the elaboration of complex derivatives, changed power-series notation, and the side on which an addition lemma places its constant. The successful rebuild includes the corrected source.
