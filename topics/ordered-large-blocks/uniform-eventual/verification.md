# Verification record

**Scope.** The proof establishes one existential eventual cutoff over all thresholds and ranks for the ordered-block statistic. The complete argument and its supporting files underwent an independent agent-assisted mathematical review with authorship and earlier verdicts withheld. Formal verification of this theorem is ⬜ None. [Fresh-context review](review-assembly.md) · [Sparse review](review-sparse.md) · [Bounded-radius review](review-dense.md) · [Earlier formal scopes](../README.md)

The research assembly and its review landed at commit 3e3344cbfe6e2c8fa930217171de87487905ad75. The publication package includes the two growing outer-rank inputs, the compact start and its joint inner-edge input. [Reviewed research PR](https://github.com/ProgramComputer/open-math-research/pull/228) · [Growing-rank research PR](https://github.com/ProgramComputer/open-math-research/pull/227)

The existing exact angular assets support the fixed-threshold case of the assembly. Both checkers replayed all 27 angular comparisons. The independent minimum Bernstein lower bound was 29/150. The growing-rank fixture checks 15 consecutive pairs and 719 rational sign-changing intervals, including five degree increases. The interval signs are checked exactly after numerical centers propose separators. Its output matched the committed record. These checks support the analytic cases and illustrate the growing-rank orientations. [Angular certificate](../results/angular-modulus.json) · [Growing-rank output](../growing-outer-ranks/check-output.txt)

From the ordered-block topic directory, run the first two commands with Python 3 and the fixture with Python-FLINT 0.9.0.

~~~sh
python3 -I -B code/verify_angular_modulus.py
python3 -I -B code/check_angular_separation_independent.py
python3 -I -B growing-outer-ranks/check.py
~~~
