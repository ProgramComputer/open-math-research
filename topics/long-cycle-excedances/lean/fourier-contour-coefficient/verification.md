# Verification record

The production source at `2ecda1ee2d9d714998e3d4593c754b50b17fdf45` passed on Linux with Lean `4.33.1` at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The driver authenticated Bowen Zuo's frozen cutoff-six source at `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554` for the reused Eulerian and cycle-profile identities. Run `python3 -I -B check.py /path/to/new/project` from this directory. [Driver](check.py) · [Common supplying pin](../common-pin/README.md) · [Passing hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/46026059458)

The report archive has SHA-256 `9b22b95ec7f1660b1073152ecc10d081038fe94581ba3e54017bf8fad418d934`. All 19 repository compiler inputs matched the tested sources or their documented staged hash. All 11 frozen module readouts matched the previously authenticated common-pin receipt. The eight new modules compiled and replayed with bundled LeanChecker. All 12 named reports used only `propext`, `Classical.choice` and `Quot.sound`. The original endpoints are `RepositoryQuotientAudit.original_contour_coefficient` and `RepositoryQuotientAudit.original_contour_adjacent`. [Endpoint source](RepositoryContourCoefficient.lean) · [Independent statement comparison](review.md)

| Source | SHA-256 |
| --- | --- |
| [SimplePoleRemoval](SimplePoleRemoval.lean) | `79c3c0aaab8e6b066f05189b07695ce3490888237f362ed43b7bd0626a520b23` |
| [AnnularPrincipalParts](AnnularPrincipalParts.lean) | `801706a314189be0714475e3c8f7ea654ad99c0a59e5af4b7d3ae5ebb9f856a2` |
| [TaylorCircle](TaylorCircle.lean) | `12094c4573ed746c738bfb6e27dcec73be2fde1e7a69f2292c2726f77a3550cb` |
| [LogisticContour](LogisticContour.lean) | `70eb7342dce531fb898648e8a78bfa58a56669bb7c8dcdbf56601cdbbd94d1fe` |
| [AdjacentContour](AdjacentContour.lean) | `92d9f19ae0e5b266d680c9dfdd364b848e120aa1b08bdd07fd18e0999ea40dd0` |
| [AnchoredPoleTaylor](AnchoredPoleTaylor.lean) | `bb48b53287d6824e77af82af317de072b38565ef8be2ea8b0af802d81d40a937` |
| [ScalarLogisticTaylor](ScalarLogisticTaylor.lean) | `69f76ef8bca031376eade6ce35678911bca83575436b7aa72cc50eff9f144a20` |
| [RepositoryContourCoefficient](RepositoryContourCoefficient.lean) | `9bc71c9e24604608d7dd22abc88225e650c95a20ba504a1a796e4f639e1edd11` |

The checker stages the explicit integral-subtraction port from #318 when the checked-out Fourier shift source predates that change. It checks the raw SHA-256 and requires the resulting SHA-256 `5d8db3cd4b1c3f3e3ad92e512b33033387c4de01dfeb7c89b35428e694ff8c80` in either case. When an existing authenticated project already contains its Fourier shift, anchored logistic, real-axis and tilt modules, call `compile_contour_coefficients(project)` from the checker without repeating project setup. [Port](FourierCircleShift.common-pin.patch)

Earlier hosted attempts diagnosed pin differences in interval-integral rewriting, pointwise analytic sums, reciprocal cancellations and the formal-series antidiagonal name. The final run resolved those errors and completed with advisory tactic-linter warnings. The coefficient and contrast theorem statements match the independent review.
