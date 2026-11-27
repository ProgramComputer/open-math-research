# Bowen Zuo’s cutoff-seven proof

**External proof reported, independent check pending.** Bowen Zuo’s November 27, 2026 release states strict interlacing after division by the simple common zero for the literal unweighted strict-excedance rows at every lower size $m\ge7$, with upper size $m+1$. His separate theorem with five independently chosen short-cycle weights applies from upper size 96. The release credits ProgramComputer’s earlier hard-cutoff research. [Supplying release v1.3.0](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.3.0) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

The supplying commit is `84418bbac7f071f49394c9dc297501671e1a2052`. The verification script authenticates the tagged Lean archive, all files in its internal manifest and the dependency lock. Lean is pinned to 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`. The source-only check passed. The build includes a separately stated comparison in lower-size notation. The comparison requires the complete negative root lists of both quotients to be simple and strictly interlacing, with weak interlacing for the two original rows. Zuo’s theorem uses the upper size $N\ge8$ and gives the old quotient degree as $N-3=m-2$. [Comparison statement](OriginalClaim.lean) · [Checker](check.py)

Run the following in this folder with the pinned Lean and Lake on the path. The directory argument must be fresh. Add `--source-only` to check the source and lock without compiling.

~~~sh
python3 -Bu check.py /tmp/zuo-seven-audit
~~~

The upstream release reports 199 project modules replayed and 11 declaration audits. The independent run adds the separately stated lower-size theorem to the replay and axiom audit. The completion record will distinguish the supplying author’s receipts from the independent run. [Supplying theorem and sources](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/tree/84418bbac7f071f49394c9dc297501671e1a2052/cutoff-seven)
