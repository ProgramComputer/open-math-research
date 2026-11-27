# Executable coefficients of the original permutation rows

This adapter evaluates a requested quotient coefficient in rational arithmetic.
It uses convolution in the ordered support recurrence, skips cycle counts that
cannot contribute to the requested exponent, and divides by the appropriate
cycle-ordering factorial. It never enumerates permutations or constructs the
higher coefficients. The evaluator is recursive and has no memoization.

The correctness statement identifies this calculation, after coercion, with
the coefficient of the original permutation sum one exponent higher.
The upstream [cycle quotient identity][quotient] and verified executable
[Eulerian coefficients][eulerian] are from Bowen Zuo's frozen v1.2.0 source.
The archive uses Lean 4.33.1 and mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

Run this command in that toolchain on a host with space for the pinned Mathlib
cache. The destination must be new.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/pinned-quotient/check.py /tmp/quotient-audit
~~~

The checker loads just the adapter's upstream import closure and audits both
identity declarations. It also checks at runtime that all 27 explicit entries
in the cutoff-seven fixture match the executable output. The fixture check
runs the certified function and compares rational values. The computational
comparison itself is a runtime assertion. This is supporting verification for
the reviewed $k\ge7$ result. It supplies neither the root windows nor a replay of
the full finite certificates. The local research Lean 4.19 build cannot import
a Lean 4.33.1 object.

[quotient]: https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L98
[eulerian]: https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleFinite/CoefficientRows.lean
