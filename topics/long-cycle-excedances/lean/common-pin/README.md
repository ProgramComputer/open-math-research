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
endpoint. The analytic joins must still provide a complete ordered witness family.

[RepositoryRootAssembly.lean](RepositoryRootAssembly.lean) checks the
original-row conclusion once that witness family and its signs are supplied.
The existing mixed-witness theorem gives complete root lists in increasing
positive modulus order. Negating and reversing the indices gives the ordered
negative root factorization predicate used by Zuo's frozen
[weak-interlacing assembly][assembly]. That theorem adjoins the common zero
to both lists and gives weak interlacing of the literal enumerators. The [hosted assembly check][root-audit] compiled and replayed both new modules.
The three new declarations use only `propext`, `Classical.choice` and
`Quot.sound`. [Assembly audit excerpt](assembly-audit.txt) · [Independent assembly review](assembly-review.md)

[RepositoryHalfAxisAssembly.lean](RepositoryHalfAxisAssembly.lean) checks
a reduced input for the same original result. It uses the frozen quotient
reciprocity theorem and extends the ordered windows below modulus one to
all negative root moduli. Reciprocal reflection swaps the endpoints and
transports the next-row signs with the degree parity. When the old degree
is odd, reciprocity gives its root at minus one, and only the next-row
sign at that point remains an input. The [hosted half-axis check][half-audit]
compiled and replayed the three new modules. Both additional declarations
use only `propext`, `Classical.choice` and `Quot.sound`. [Audit excerpt](half-axis-audit.txt) · [Independent half-axis review](half-axis-review.md)

[RepositoryCenterSign.lean](RepositoryCenterSign.lean) checks an algebraic
proof of the remaining odd-old-degree center sign. Distinct simple negative
roots of an even-degree Eulerian polynomial pair by inversion. Each pair
contributes a negative factor to its value at minus one. In the anchored
cycle expansion, odd cycle lengths contribute zero, while the even terms
have one common sign after normalization. The summand for a single
full-size cycle makes the sign strict whenever the cutoff fits. The
full weak-interlacing implication then needs only the left-hand windows.
The [hosted center check][center-audit] compiled and replayed both new modules.
The three additional declarations use only `propext`, `Classical.choice`
and `Quot.sound`. [Audit excerpt](center-audit.txt) · [Independent review](center-review.md) ·
[Eulerian roots][eulerian-roots] ·
[Eulerian reciprocity][eulerian-reciprocity] · [Anchored expansion][anchored]

[center-audit]: https://github.com/ProgramComputer/open-math-research/actions/runs/45924858448
[eulerian-roots]: https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/EulerianSturm.lean#L74
[eulerian-reciprocity]: https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/Reciprocity.lean#L43
[anchored]: https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/AnchoredRows.lean#L158
[half-audit]: https://github.com/ProgramComputer/open-math-research/actions/runs/45923553428
[root-audit]: https://github.com/ProgramComputer/open-math-research/actions/runs/45922634178
[assembly]: https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleFinite/Assembly.lean#L8
[hosted]: https://github.com/ProgramComputer/open-math-research/actions/runs/45921839840
[artifact]: https://github.com/ProgramComputer/open-math-research/actions/runs/45917288503
[prior]: https://github.com/ProgramComputer/open-math-research/actions/runs/45918517895
[shape]: https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L131


## The original-row pole expansion

[RepositoryPoleProfile.lean](RepositoryPoleProfile.lean) proposes an exact
expansion of the normalized original permutation row for every cutoff at
least two. The expansion sums over the allowed cycle counts, with each
cycle moment represented by the full signed odd-pole series. It uses the
frozen ordered cycle moment recurrence and Eulerian partial fraction identity.

The second theorem bounds the difference from keeping just the nearest
conjugate pole pair in each individual cycle. On the infinite region where
the cutoff is at least eight and its product with the squared pole-angle
sine is at least one, each cycle is controlled by the frozen decay estimate.
For each cycle count the bound increases its nonnegative factorial-weighted
scale by the accumulated relative error from the omitted poles. This
estimates the actual row, while the signed consecutive-row comparison in
the [uniform proof](../../effective-uniform.md) still needs its common
contour and correlated adjacent-row error estimates.

The hosted common-pin audit is pending.
