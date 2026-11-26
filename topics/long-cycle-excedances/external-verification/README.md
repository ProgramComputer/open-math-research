# External cutoff proofs reported by Bowen Zuo

**External proof reported, independent check pending.** Bowen Zuo supplies the following Lean proofs for strict excedances. The adjacent pair in each release has lower size $m$ and upper size $N=m+1$. All three all-size statements concern unweighted original rows. The separate weighted bounds start at different sizes. [Alexandersson's original claim](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

| Minimum cycle length | Supplying release and commit | All-size theorem | First pair |
| --- | --- | --- | --- |
| 4 | [v1.0.0](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.0.0), `f8fef864286a1bbc59f96484074f28d77b1a027f` | `LongCycleBounds.fixed_four_all_sizes` | 4 and 5 |
| 5 | [v1.1.0](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.1.0), `70cad373bce521d78d6de9bcff3d29d07fc7fe9f` | `LongCycleBounds.FiveCutoff.all_sizes` | 5 and 6 |
| 6 | [v1.2.0](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.2.0), `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554` | `LongCycleBounds.SixCutoff.all_sizes` | 6 and 7 |

The independent source comparison followed `LongCycles.Allowed` to the condition that no positive power smaller than the cutoff fixes any label. This is equivalent to the required minimum cycle length. The enumerator ranges over all permutations on the labeled finite set and counts indices strictly smaller than their images. The strict predicate factors both quotients completely into simple, negative, alternating lists. The separate weak predicate factors the original rows. The cutoff-four proof uses `Band.actual_general_cycle_row` to factor out the common variable. For cutoffs five and six, `OriginalPair` includes both original-row factorizations. Since the quotient roots are all strictly negative, the extracted zero has multiplicity one.

All three supplying projects pin Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The runner authenticates each dependency manifest, checks the inner and outer cutoff-six archives, and prints all nine dependency revisions. It adds a comparison theorem quantified by the old size, prints the supplied theorem and original definitions, and audits transitive axioms. The proof source and its dependency locks stay pinned to Zuo's releases. [Reproduction script](rebuild.py)

With the official pinned Linux toolchain on PATH and an empty directory for each run, execute:

~~~sh
python3 -Bu rebuild.py 4 /tmp/zuo-cutoff-4
python3 -Bu rebuild.py 5 /tmp/zuo-cutoff-5
python3 -Bu rebuild.py 6 /tmp/zuo-cutoff-6
~~~

The independent compiled declarations and axiom reports are pending. Zuo's own signed receipts and source-level matches are recorded separately from the outcome of these runs.
