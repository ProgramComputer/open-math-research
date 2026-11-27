# Integer endpoint signs for long-cycle permutations

For the cutoff $k=13$, the proposed Lean check evaluates the two original reduced rows of sizes 251 and 252 at both endpoints of 26 specified intervals. The intervals have ranks 6 through 31 in the [checked witness shard](../../intermediate/witness-ledger/README.md). The assertion concerns 104 strict signs. The remaining pairs and the analytic regions of the interlacing proof are outside its scope.

The integer table starts at the unique empty permutation. The frozen insertion recurrence updates its first 61 coefficients from the two preceding sizes it needs. Removing the constant coefficient gives the first 60 coefficients of the quotient by $X$. The checkpoint generator writes Lean equalities for all 252 steps. Each equality is proved by kernel reduction. For the discarded coefficients, a geometric upper bound and an absolute error bound of two for integer Horner evaluation reduce the strict sign test to integer arithmetic.

[Insertion recurrence](InsertionTable.lean) · [Rounding bound](RoundedHorner.lean) · [Tail bound](IntegerTail.lean) · [Connection to the original sum](OriginalInsertionSigns.lean) · [First-pair theorem](FirstPairOriginal.lean)

The endpoint reductions are split into five short blocks, separate from the model that connects the checkpoint entries to the literal permutation rows. The final theorem combines the checked blocks with that model.

The hosted workflow can reuse the three arithmetic artifacts from run 45930417212. Before importing any object, it checks the producing ZIP, insertion source, generator and generated source hashes, compiler and dependency pins, producer kernel receipts and object digests. Each reused artifact retains its original unmodified compiler log. If reuse is unavailable, the workflow builds and replays the arithmetic modules from source. [Producing run](https://github.com/ProgramComputer/open-math-research/actions/runs/45930417212)

## Verification

The source targets Lean 4.33.1 with mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, the supplying release's own pins. On Linux with its pinned Lean on the search path, run the following from the repository root. The target directory must be new. A second, optional argument may point to the authenticated 65-module upstream archive described in the [common-pin record](../common-pin/README.md).

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/fast-insertion/check.py /tmp/long-cycle-endpoints
~~~

The complete pinned replay is pending. The certificate uses the original labelled-permutation enumerator, and the proposed formal statement is in `RepositoryQuotientAudit.firstPair_original_signs`.
