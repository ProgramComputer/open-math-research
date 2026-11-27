# Verification of the original Fourier pole kernel bounds

The [hosted source check](https://github.com/ProgramComputer/open-math-research/actions/runs/46024689000) passed at [commit ef47c0d](https://github.com/ProgramComputer/open-math-research/tree/ef47c0d8ad45eee2b91ee5e8ad6714f3ca3a7be4). It used Lean 4.33.1 at compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The checker authenticated the retained common-pin import archive and checked the pinned package revisions. [Hosted job](https://github.com/ProgramComputer/open-math-research/actions/runs/46024689000/job/140592918840) · [Reproduction command](README.md).

The three axiom reports for `row_pole_coefficient_bound`, `squared_gap_inverse_factors`, and `literal_fourier_kernel_budgets` contain only `propext`, `Classical.choice`, and `Quot.sound`. LeanChecker replayed both new modules with exit code zero. The compiled hashes match both new Lean sources and 17 checked dependency sources. These dependencies include the original pole and row modules, the signed odd-pole moments, and the nine direct Fourier sources whose SHA-256 digests are recorded in the checker. [Standalone checker](check.py) · [Exact direct dependency revision](https://github.com/ProgramComputer/open-math-research/tree/ade4acc68e05cf882f3733308e18b61477a381d4/topics/long-cycle-excedances/lean/fourier-circle) · [Dependency source check](https://github.com/ProgramComputer/open-math-research/actions/runs/46022783206).

The final theorem proves summability for the four pole kernels and absolute summability for the endpoint numerator. It gives both scaled nonnegativity facts and all five numerical bounds. Its hypotheses are cutoff at least 100, aspect at least 48, the stated size-sine lower bound, the annular radius constraints, and a same-radius squared pole gap for every signed pole. These estimates are inputs to the subsequent normalized coefficient and residue argument. [Literal theorem](FourierLiteralKernelBudgets.lean).

[Report artifact 15212196927](https://github.com/ProgramComputer/open-math-research/actions/runs/46024689000/artifacts/15212196927) has ZIP SHA-256 `28e94b1df1cf7799d20acdb65e815bac2c81bddb60c3144b5ee39d372fd90676` and log SHA-256 `5e87ed7f88e906beb20e0864fd84fcbafa6110da69af65fe94bfd55b7cff2954`.

| Module | Compiled input SHA-256 |
| --- | --- |
| FourierPolePointwiseBudget | `30bdc2b4cfc5a435c681c30853134312f91cd5dd764bd4ab2906977253732a3d` |
| FourierLiteralKernelBudgets | `94a7d04ea8203c540c42bb81f413bc9adcade91cc9fcc5963ad36db1f7797016` |
