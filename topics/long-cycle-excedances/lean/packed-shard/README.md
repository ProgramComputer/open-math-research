# The first packed endpoint shard

The Lean theorem `RepositoryQuotientAudit.firstShard_original_signs` checks four strict signs for each of the 131 records in the existing [witness shard](../../intermediate/witness-ledger/shard.csv). The old sizes are 251 through 255 and the cutoff stays at 13. At each record the original reduced row at size $n$ has opposite signs at the two endpoints, and the original reduced row at size $n+1$ has the prescribed common sign at both endpoints. The claim comprises 524 signs. Root selection, the joins with the analytic windows, and the other finite shards are separate obligations.

The generator stores 50 words per row. Each word holds its significand and binary shift. Lean checks the recorded shift and quotient using powers of two, then proves that decoding gives the rounded coefficient. The fast step uses the 12 nonzero Eulerian weights and the descending-factorial form of the binomial coefficient. Its agreement with the rounded recurrence is proved in Lean. The seed and consecutive steps through size 256 establish all coefficients used by the endpoint proof. [Rounded row enclosure](../compact-rows/README.md) · [Endpoint sign implication](../packed-endpoints/README.md)

The 243 row transitions are assigned to 21 independent modules. The five old sizes have independent endpoint modules. Each module receives strict compilation and its own kernel replay. The final Lean module combines their theorems and applies the endpoint implication to the literal permutation polynomials. The driver authenticates the archived shard and generated proof-source manifest.

## Reproduction

On Linux, put the pinned Lean 4.33.1 toolchain on the search path and run from the repository root. The target must be a new directory. A second, optional argument supplies the authenticated object archive described in the [common pin record](../common-pin/README.md).

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/packed-shard/check.py /tmp/packed-shard-audit
~~~

The independent arithmetic replay constructs the full rows by distinguishing the cycle containing the least label. It evaluates the full degree at every rational endpoint, with integer Horner arithmetic. It passed all 524 signs.

~~~sh
uv run --no-project --with python-flint==0.9.0 python -B \
  topics/long-cycle-excedances/lean/packed-shard/replay-full-signs.py \
  topics/long-cycle-excedances/intermediate/witness-ledger/shard.csv
~~~

The hosted Lean 4.33.1 build passed strict compilation and kernel replay of every module on code commit `bde40d8`. The two exported declarations use only `propext`, `Classical.choice` and `Quot.sound`. [Hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/45931609250) · [Audit excerpt](hosted-audit.txt) · [Independent scope review](independent-review.md)
