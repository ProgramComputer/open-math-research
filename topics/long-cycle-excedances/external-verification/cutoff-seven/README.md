# Bowen Zuo’s cutoff-seven proof

**External proof reported, independent check pending.** Bowen Zuo’s November 27, 2026 release states strict interlacing after division by the simple common zero for the literal unweighted strict-excedance rows at every lower size $m\ge7$, with upper size $m+1$. His separate theorem with five independently chosen short-cycle weights applies from upper size 96. The release credits ProgramComputer’s earlier hard-cutoff research. [Supplying release v1.3.0](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.3.0) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

The supplying commit is `84418bbac7f071f49394c9dc297501671e1a2052`. The verification script authenticates the tagged Lean archive, all files in its internal manifest and the dependency lock. Lean is pinned to 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`. The source-only check passed. An independent reviewer matched the original combinatorial definitions, the two pair endpoints and the strict ordering. [Scope review](scope.md) The build includes a separately stated comparison in lower-size notation. The comparison requires the complete negative root lists of both quotients to be simple and strictly interlacing, with weak interlacing for the two original rows. Zuo’s theorem uses the upper size $N\ge8$ and gives the old quotient degree as $N-3=m-2$. [Comparison statement](OriginalClaim.lean) · [Checker](check.py)

Run the following in this folder with the pinned Lean and Lake on the path. The directory argument must be fresh. Add `--source-only` to check the source and lock without compiling.

~~~sh
python3 -Bu check.py /tmp/zuo-seven-audit
~~~

The upstream release reports 199 project modules replayed and 11 declaration audits. The independent run adds the separately stated lower-size theorem to the replay and axiom audit. The completion record will distinguish the supplying author’s receipts from the independent run. [Supplying theorem and sources](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/tree/84418bbac7f071f49394c9dc297501671e1a2052/cutoff-seven)

## Independent endpoint arithmetic

A second calculation checks $(7,8)$, $(94,95)$ and $(95,96)$ directly, including both sides of the finite-to-analytic transition. It constructs integer rows by singling out the cycle of label 1. Literal enumeration agrees at sizes 7 and 8. After removing the simple zero, every signed Euclidean remainder has positive leading coefficient and degree one less than the preceding divisor, ending in a positive constant. The signs at consecutive roots of the divisor therefore alternate. Induction from the final linear and constant pair, with the leading signs at infinity, proves strict interlacing of the full lists. Positive coefficients and positive constant term in each quotient place every root below zero. The three chains had 5, 92 and 93 nonzero remainders respectively. Run with Python-FLINT 0.9.0. [Independent checker](check-endpoints.py) · [Exact output](endpoints.txt)

~~~sh
python3 -IB check-endpoints.py
~~~

## First independent attempt

The first job cold-compiled the supplying finite-prefix modules through Rows95. Lake then rejected the independently added comparator because it was placed outside the registered libraries. The job stopped before the consolidated declaration audit and independent replay. This is partial build evidence. The retry keeps the supplier inputs intact, places the generated files under the registered LongCycleBounds library, and checks that layout with the pinned Lake before the full build. Its workflow retains the supplier's compiler outputs and source hashes at the comparator boundary if a later check fails. [First build log](https://github.com/ProgramComputer/open-math-research/actions/runs/45952201222/job/140350418998)

The corrected layout passed the pinned Lake preflight, including compilation of the three named modules and independent replay of the preflight comparator. The hosted runner later lost communication with GitHub during the full build. GitHub recorded no completed rebuild step, and the run produced neither a report nor a supplier checkpoint. Full replay remains pending. [Retry build and runner annotation](https://github.com/ProgramComputer/open-math-research/actions/runs/45964336070/job/140389300003)
