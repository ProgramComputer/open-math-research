# Rational endpoint signs for original reduced rows

For a positive size, cutoff at least two and nonnegative rational endpoint,
the checked sign theorem reads the shifted coefficient prefix by the
[verified coefficient adapter](../pinned-quotient/README.md). A strict rational
margin over the geometric tail certifies the corresponding signed value of
the original quotient. The coefficient envelope follows from the run-color theorem.

The shape bridge equates the upstream quotient with the canonical coefficient
shift of the original permutation sum. At size at least the cutoff it gives
the degree, monicity and value at zero needed by the root-list certificate.
It uses [the supplying shape theorem][shape] in the same environment.

The hosted check uses Lean 4.33.1 compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. It verifies the frozen
v1.2.0 source and can reuse the [65-module import library][artifact], whose
exact archive digest matches the [strict coefficient audit][prior].
The [hosted check][hosted] compiled and replayed all three new local modules.
The five audited declarations use only `propext`, `Classical.choice` and
`Quot.sound`. [Audit excerpt](hosted-audit.txt) · [Independent scope review](independent-review.md)

With the pinned toolchain, run from the repository root

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/common-pin/check.py /tmp/long-cycle-common-pin
~~~

The checker accepts the hashed import archive as an optional second argument.
The next obligation is the exact numeric margin at each required dyadic
endpoint. Root-list assembly and the analytic joins remain separate.

[hosted]: https://github.com/ProgramComputer/open-math-research/actions/runs/45921839840
[artifact]: https://github.com/ProgramComputer/open-math-research/actions/runs/45917288503
[prior]: https://github.com/ProgramComputer/open-math-research/actions/runs/45918517895
[shape]: https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L131
