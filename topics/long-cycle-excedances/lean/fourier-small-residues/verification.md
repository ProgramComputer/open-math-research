# Enclosed-residue verification for cutoffs eight through ninety-nine

The pinned build checked `RepositoryQuotientAudit.original_small_cutoff_minor_sums` on commit `79ad045c8e981d9e0a3eb913a2118a3fb84cb5c7`. It bounds both sums on any finite set of positive nonprincipal poles enclosed by the selected radius. It uses the original permutation generating numerator, $8\le k\le99$, $n\ge10000$, $s\ge0$ and the angular entrance inequality. The associated pointwise estimate and the weighted and unweighted budgets were also replayed. [Exact statement](RepositorySmallMinorSums.lean) · [Pointwise estimate](RepositorySmallCutoffResidues.lean) · [Hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/46032358588)

The run used Linux Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` and Bowen Zuo’s supplying release at `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. The audit compared all 39 repository compiler inputs with the tested Git sources and matched eleven upstream hash entries to the previously audited supplying sources. The bundled checker replayed 23 modules. All 73 named transitive axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. The downloaded report archive matched its GitHub SHA-256 digest `31c348fd7e48c4b5cfc29f89cf1cedfb33ac69be9a8ce923f520b378b09f44c6`. [Independent mathematical review](review.md)

From the repository root, run the driver with the pinned Linux compiler and a fresh build directory.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-small-residues/check.py /tmp/original-small-residues
~~~

Intermediate replays identified simplification differences in the geometry, exact radius identity and the equality between the two definitions of the principal pole. The final run checked the original bounds with these steps explicit. Transfer to ordered roots uses separate boundary and phase estimates.
