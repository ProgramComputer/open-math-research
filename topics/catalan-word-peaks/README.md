# Strict peaks in Catalan words

**Theorem.** For a Catalan word of length $n$ with $w_1=0$ and $0\le w_{i+1}\le w_i+1$, count strict peaks $w_{i-1}<w_i>w_{i+1}$. The polynomial $C_n(t)$ that counts words by this statistic has only simple negative zeros, and consecutive nonconstant rows strictly interlace. In each pair the rightmost zero of the longer row lies farther right. The empty word gives $C_0=1$. This answers both assertions in Alexandersson’s conjecture. A fresh agent assessed an anonymized copy of the full argument, checked it against the original conjecture, and recorded a blind referee report. [Blind review and formal-scope supplement](review/README.md) [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjCatalanWordPeaks) · [Proof](proof.md) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/3)

The analytic proof applies at every length from $150$. It bounds the error in a four-cut coefficient integral, then compares the integrals for adjacent rows at every interior zero. Separate arguments determine the signs at both extreme roots. Exact computation covers rows $0$ through $150$ and all $150$ successive pairs in this range, including vacuous comparisons for constant rows. [Rightmost zero](effective-right-edge.md) · [Farthest zero](far-left.md) · [Coefficient vectors](results/family-rows.jsonl)

Baril, Harris, Harry, McClinton and Ramírez derived the generating function for short peaks. The earlier public argument established eventual real-rootedness and interlacing with an unspecified cutoff. The effective bounds here connect the infinite argument to a reproducible finite range. [Enumeration paper](https://doi.org/10.26493/2590-9770.1794.fc5) · [Earlier eventual theorem](https://github.com/1337isnot1337/solved-conjectures/issues/59#issuecomment-7134751818) · [Sources and priority search](LITERATURE.md)

**🟩 Full · Lean 4.** Lean defines the polynomial from Catalan words and checks the coefficient recurrence, the formal generating function and its scaled discriminant. It verifies the branch-point geometry, local integrand majorants, and the exact moments and integrated tail bounds for the radial density. It identifies each positive-index coefficient of the scaled Catalan series with the sum of the four improper ray integrals. Lean verifies that every row has only simple negative zeros, using the exact finite prefix and the explicit phase and alternating signs from length $150$. It checks all $150$ consecutive pairs in the finite prefix. Lean also proves the error bound for the normalized near-ray mean and the quantitative successive-size bounds $|J_{n+1}-J_n|<1/n$ and $|J_{n+1}-J_n|<4/n$ under their respective interior angle conditions. Lean bounds the normalized far-ray contribution in both angular ranges and proves $\Re J_n>17/20$ in the small-angle sector. The strict next-row signs at the old middle and extreme roots give the analytic interlacing step from length $150$. The combined Lean theorem verifies both assertions for every length using this step and the finite prefix. [Formal statements and build instructions](lean/README.md)

Archived Lean proof sources · [![Zenodo DOI 10.5281/zenodo.24552076](https://zenodo.org/badge/DOI/10.5281/zenodo.24552076.svg)](https://doi.org/10.5281/zenodo.24552076)

[Stable Lean recheck](verification.json) · [Per-declaration axiom reports](lean/publication/axioms-4.36.json) · [Reproduce the audit](../../shared/lean/publication/README.md)

Lean also derives the strict next-row sign at the farthest old zero for $n\ge150$ from the top three shifted coefficients and complete root lists for both word polynomials. [Formal endpoint theorem and reproduction](lean/README.md#sign-at-the-farthest-old-root)

The written proof includes exact finite certificates. The independent review checked the orientations of the radial cuts, the phase, both ranges of integral estimates, the covariance comparison between consecutive sizes and the degree count. The finite verifier compares the algebraic generating function with a binomial coefficient formula, then checks signed polynomial remainder chains over the rationals. [Finite verifier](code/verify_all_rows.py) · [Far-left verifier](code/far_left.py)

From the repository root run

~~~sh
python -m pip install python-flint==0.9.0
python -I -O topics/catalan-word-peaks/code/verify_all_rows.py topics/catalan-word-peaks/results/family-rows.jsonl
python -I -O topics/catalan-word-peaks/code/effective_right_edge.py
python -I -O topics/catalan-word-peaks/code/far_left.py
~~~

[Append-state recurrence obstructions](append-states/README.md) records why two local interlacing invariants fail in a combinatorial approach to the known theorem.
