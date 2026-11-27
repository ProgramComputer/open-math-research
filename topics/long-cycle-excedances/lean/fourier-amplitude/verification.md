# Selected-circle amplitude verification

The original all-height logarithmic contraction and normalized selected-circle estimate passed on source commit `c53d8c30dec8cc0cd816f7eedf5d591f5d7c1e19`. The final theorem uses the power-series numerator of the original permutation generating function. Its height split uses nonnegative height throughout, cutoff at least 100 and a common error budget $2997/100$. The circle and numerical amplitude conclusions hold for aspect $x\ge44$ under the stated angular-entrance condition. [Build log](https://github.com/ProgramComputer/open-math-research/actions/runs/46017308607) · [Theorems and argument](README.md)

The run used Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`, and Bowen Zuo’s supplying release commit `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. All 50 repository compiler inputs matched the corresponding Git sources or the result of applying the authenticated port patch. They comprise 49 distinct modules. All eight port patches matched their logged source hashes and were applied with zero fuzz. The bundled Lean checker replayed 45 modules. All 94 named transitive axiom reports contained only `propext`, `Classical.choice` and `Quot.sound`. These runs use the research dependency pins.

From a checkout of the verified revision, put the pinned Linux compiler on the path and run the command with a fresh output directory.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-amplitude/check.py /tmp/fourier-amplitude
~~~

The workflow can reuse the authenticated supplying import archive. The command above rebuilds those supplying targets from source. The enhanced statement exposing the squared gap of the same selected circle is pending a separate production replay. The full all-size interlacing theorem has additional Fourier coefficient and residue obligations.
