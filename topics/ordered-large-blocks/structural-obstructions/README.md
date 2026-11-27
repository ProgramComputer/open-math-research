# Structural obstructions for ordered large-block interlacing

The canonical renewal determinant cannot be turned into a definite symmetric pencil by constant invertible coordinate changes. Its reduced matrix has an explicit indefinite form, and its shifted renewal kernel has a negative Toeplitz minor at every threshold at least three. [Determinant and resolvent identities](determinant.md)

The two- and three-box geometric prefixes can each be real-rooted while a partial addition of the third box has nonreal roots. At size $`2j`$ and interpolation weight $`2^{-j}`$ this happens exactly for $`j\ge16`$. The finite occupancy tests concern their specific auxiliary polynomials and weak order. [Supplementary-box obstruction and exact cases](occupancy.md)

Formal verification is ⬜ None. These are obstructions to sufficient closure methods for the unit-weight ordered-partition problem. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1)

## Reproduce

From this directory, with Python 3 and assertions enabled, run the exact formula checks.

~~~sh
python3 -B check-determinant.py
python3 -B verify-collision.py --ledger /tmp/ordered-collisions.jsonl.gz
gzip -dc collisions.jsonl.gz | shasum -a 256
gzip -dc /tmp/ordered-collisions.jsonl.gz | shasum -a 256
~~~

The finite auxiliary grid additionally uses `python-flint==0.9.0`.

~~~sh
python3 -B search.py 32 65 2 3 4 5 6 7 8 9 10 12 15 --output /tmp/ordered-occupancy
gzip -dc medium.jsonl.gz | shasum -a 256
gzip -dc /tmp/ordered-occupancy.jsonl.gz | shasum -a 256
cmp medium-summary.jsonl /tmp/ordered-occupancy-summary.jsonl
~~~
