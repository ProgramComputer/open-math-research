# Original boundary errors for cutoffs eight through ninety-nine

Lean 4.33.1 verified `OpenMathResearch.LongCycleExcedances.original_small_normalized_fourier_errors` on source commit `46643c3971c6274b170815e54920f7715bbaa6b3`. For $8\le k\le99$, $n\ge10000$, $s\ge0$ and $nS^2\ge1$, the same separated contour gives both the $1/25$ old-row error bound and the $S/25$ signed successor bound. The proof uses the actual numerator in each of the three cutoff ranges. [Exact statement](RepositorySmallBoundary.lean) · [Hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/46035353188) · [Independent scope review](review.md)

The pinned Linux compiler commit was `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, mathlib was `0df444a360eaa60ab8c11dca51a86af692955474`, and Bowen Zuo’s frozen supplying release was `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. The audit matched all 90 repository compiler inputs across 89 distinct modules, including eight authenticated port patches. All eleven upstream source hash entries matched the previously verified release inputs. The bundled checker replayed 67 modules. The 168 named transitive axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. The downloaded report archive matched its GitHub SHA-256 digest `f3ce53ff2c600e1faad99b57a2dea8d26071806cc5593f9ad93a6e7bc9c25827`.

From the repository root with the pinned Linux compiler, give the driver a fresh output directory.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-small-boundary/check.py /tmp/finite-cutoff-cauchy
~~~

Earlier runs stopped at two porting issues. The first used a superseded numerator helper. In the second, the parser read an order relation next to the height variable as a different token. The final replay checked the original statement after resolving both.
