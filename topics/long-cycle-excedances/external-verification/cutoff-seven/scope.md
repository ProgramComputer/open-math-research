# Independent scope audit of cutoff seven

27 November 2026. Agent-assisted, read-only comparison of Bowen Zuo's v1.3.0 source at `84418bbac7f071f49394c9dc297501671e1a2052`, the independently stated lower-size comparison, and Alexandersson's original definition. I found no mathematical discrepancy in the claims or pair boundaries. This review checks source scope. The independent Lean rebuild is a separate audit. [Supplying release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.3.0) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

- In `LongCycles/Statement.lean`, `Allowed 7` excludes all positive return times below seven. The least positive return time is the cycle length, so seven itself is allowed. `excedances` counts original labels $i<\sigma(i)$. `enumerator` includes each admissible permutation exactly once with no cycle weight.
- `K7Prefix.OriginalPair N` explicitly factors both original rows as $X$ times quotient polynomials and orders them as sizes $N-1,N$. The strict predicate gives complete factorizations, negative roots, strictly increasing lists and $s_i<r_i<s_{i+1}$ in actual root order, with both outer roots in the larger row. The old quotient has degree $N-3$ and the new quotient degree $N-2$. The unreduced weak predicate allows the shared zero at the largest root. The strict factorizations show the zero is simple in both original rows.
- `K7Prefix.finite_original` covers upper sizes $8\le N\le95$. The first pair is $(7,8)$, using `Rows11.pair8` in namespace `LongCycleFinite.K7Prefix` (the declaration itself is `K7Prefix.pair8`). The last finite pair is $(94,95)$. `SevenCutoff.original` starts at upper size 96 and therefore begins at $(95,96)$. It lower-bounds its old size by 95 when invoking the sign theorem. Both factorizations in this branch are connected to the literal rows by `Band.actual_general_cycle_row`. There is neither a gap nor a repeated pair at the join. `SevenCutoff.all_sizes` covers $N\ge8$ and the separate `IndependentCutoffSeven.from_lower_size` sets $N=m+1$, where $m\ge7$ and $N-3=m-2$.
- In `CycleProfile.lean` the row sums over derangements with a product of $w(\ell)$ for their individual cycle lengths $\ell$. The weighted theorem `SevenCutoff.independent_weights` allows each of the five values $w(2),\ldots,w(6)$ to vary independently in $[0,1]$, including zero and one. It uses one common profile at both adjacent sizes, requires $w(1)=0$ and fixes $w(\ell)=1$ for $\ell\ge7$. The weighted conclusion starts at $(95,96)$. The hard-cutoff assertion is the all-zero choice at the five short lengths, with the separate finite package below upper size 96. The weighted conclusion makes no assertion about independent choices of profiles for the two rows.

To identify the exact input and reproduce the source comparison, run the following commands from this topic folder after preparing the source with the checker. The observed archive SHA-256 was `acbc05bf6119e341714756e5f42a1b37ef3ccc339be67c536dff6bb14632154b`, and the pinned sources specify Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
python3 -I check.py source-checked --source-only
cat source-checked/lean-toolchain
rg -n 'def (Allowed|excedances|enumerator|OriginalPair|StrictNegativeInterlacing|cycleWeight|row)|theorem (all_sizes|finite_original|pair8|independent_weights|original)' \
  source-checked/LongCycles/Statement.lean \
  source-checked/LongCycleFinite/Interlacing.lean \
  source-checked/LongCycleFinite/K7Prefix/{Base,All,Rows11}.lean \
  source-checked/LongCycleBounds/{CycleProfile,SevenCutoffAllSizes,SevenCutoffVerified}.lean
cat OriginalClaim.lean
```
