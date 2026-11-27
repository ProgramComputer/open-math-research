# Strict interlacing through the first quintic ordered-partition row

For every threshold $`j\ge2`$, the consecutive ordered large-block partition polynomials have simple negative roots in strict alternating order for $`3j\le n<5j`$. This includes the first quartic and first quintic rows. Together with the earlier linear and quadratic proof, it settles **every consecutive pair with old size $`n<5j`$**. Constant rows use the usual empty-root convention. The all-size conjecture remains open. [Written proof](proof.md) · [Earlier degrees](../quadratic-rows/README.md) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

**Formal verification**　⬜ None. An independent agent-assisted mathematical review checked the uniform analytic bounds, the old-to-new root order and the two changes of degree. A separate integer Sturm verifier reconstructed and checked every residual pair. [Review](independent-review.md) · [Independent verifier](independent-finite.py)

| Old degree | Analytic range | Rational rectangles | Finite equal-degree pairs | Finite degree increases |
|---:|---|---:|---:|---:|
| 3 | $`j\ge64`$ | 73 | 1,953 | 62 |
| 4 | $`j\ge128`$ | 1,615 | 8,001 | 126 |

The certificate retains both the scaled size $`n/j`$ and the reciprocal threshold $`1/j`$. Its boxes cover the whole continuum in these two parameters. This makes the large-threshold part effective and allows one check to cover infinitely many pairs. The same construction can be tried for larger degrees. The bounds and certified rectangles here cover the two degrees in the table.

## Reproduce

From this directory, use Python 3 with assertions enabled. The replay of the stored certificates and both residual tests use only the standard library.

~~~sh
python3 -B replay.py finite-3-64.json finite-4-128.json
python3 -B all-finite.py 3 64
python3 -B all-finite.py 4 128
python3 -B independent-finite.py 3 64
python3 -B independent-finite.py 4 128
~~~

The finite checker accepts `--ledger FILE` and writes each threshold, old size and pair of complete coefficient vectors as JSON lines. The two independent checks use the same deterministic encoding so their SHA-256 digests can be compared. The cubic and quartic outputs retain the pair counts and both digests. The compressed table stores each distinct row in each degree strip as a JSON array containing the strip degree, threshold, size and complete coefficient vector. Reassembling adjacent pairs from its 10,330 rows reproduces both coefficient-ledger digests. Its compressed SHA-256 is `d5600176aa24926fa23df8bd970ef9e13b48bfb6133b994845f2b5f99c108711`. [Finite coefficient rows](finite-rows.jsonl.gz) [Cubic output](residual-3.json) · [Quartic output](residual-4.json) · [Rectangle replay output](replay-output.txt)

The optional certificate generator uses python-flint 0.9.0 for initial bracket proposals. All acceptance tests use rational arithmetic. Run the following from a writable copy of this directory to regenerate the JSON certificates and replay them.

~~~sh
python3 -B finitej.py 64 3
python3 -B finitej.py 128 4
python3 -B replay.py finite-3-64.json finite-4-128.json
~~~
