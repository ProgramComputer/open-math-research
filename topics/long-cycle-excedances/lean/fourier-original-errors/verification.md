# Verification of the two boundary errors

Lean 4.33.1 checked `OpenMathResearch.LongCycleExcedances.original_normalized_fourier_errors` at `bb124c3ec0ccbc89b2d01a9c5064c8fc59c4cefe`. The theorem supplies one circle for the original row and its signed successor contrast. Its hypotheses include $k\ge100$, $n/k\ge48$, $s\ge0$ and $n(\pi/r)^2\ge1$. Combining these boundary errors with the nonprincipal residue estimates is a separate proof step. [Theorem](FourierOriginalErrorPair.lean) · [Hosted build](https://github.com/ProgramComputer/open-math-research/actions/runs/46030278719) · [Scope review](review.md)

The Linux compiler commit was `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, mathlib was `0df444a360eaa60ab8c11dca51a86af692955474`, and the supplying release by Bowen Zuo was `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. The source audit matched all 83 repository compiler inputs covering 81 distinct modules, including eight zero-fuzz port patches. Eleven upstream source-hash entries matched the previously audited release inputs. The bundled Lean checker replayed 59 modules. All 156 named transitive axiom reports, including the final theorem, used only `propext`, `Classical.choice` and `Quot.sound`. The downloaded report archive matched its GitHub SHA-256 digest `b8318500f3f3d6ff452be25ccfcb9e4ec74fd33d099c7233fe4613d62fe14534`.

To reproduce from the source commit with the pinned Linux compiler, run from the repository root using a fresh output directory.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-original-errors/check.py /tmp/original-fourier-errors
~~~

The first replay stopped at a definitional equality for the original trace inside two conditional branches. The checked revision unfolds that definition explicitly in both branches.
