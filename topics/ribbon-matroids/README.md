# Ribbon matroids have the Narayana polynomial

For every connected lattice path matroid with a nonempty ribbon diagram and rank $r$, the $Z$-polynomial is the Narayana polynomial $N_{r+1}$ and has exactly $r$ simple negative roots. Alexandersson’s original conjecture states the coefficient identity and real-rootedness. [Dated original conjecture](https://github.com/PerAlexandersson/symmetricfunctions.com/blob/b4a005205cfd78dd987facedf2e1916ef1e308fd/tex-source/realRootedOpenProblems.tex#L496-L506) · [Author’s issue, item 4](https://github.com/PerAlexandersson/RealRooted/issues/2650)

[Proof](proof.md) · [Manuscript](paper.pdf) · [TeX source](paper.tex) · [Blind mathematical review](review.md) · [Blind formal coverage review](formal-coverage-review.md) · [Independent flat computations](results/ribbons.jsonl)

**🟩 Full · Lean 4.** Lean proves the Narayana coefficient identity and all $r$ simple negative roots from the boundary paths of the original ribbon matroid. The official Lean kernel and Rust Nanoda replayed the same export, including the comparisons with the separate source and publication statements. [Lean theorem](lean/publication/RibbonNarayana.lean) · [Reproduce the check](lean/README.md) · [Verification record](verification.json)

The theorem uses the standard nonempty ribbon convention. Lean also checks $Z=1$ under the optional rank-zero convention. The singleton coloop with an empty-area diagram belongs to the written rank-one argument. The extension to arbitrary noncrossing polygon diagonals has a written proof and a conditional Lean reduction. [Formal scope](lean/README.md) · [Proof](proof.md)

The repository proof was public on 25 November 2026. On 26 November, SymCat credited the same ribbon theorem to Steve Raj’s working draft *Outerplanarity from the Z-polynomial of a graphic matroid*, dated 25 November. The relationship between the arguments is unknown. This verification concerns the repository proof. [Repository proof commit](https://github.com/ProgramComputer/open-math-research/commit/d27bf1897bff2f426d57bea5efdbc9fca6f17d4f) · [SymCat theorem](https://www.symmetricfunctions.com/schubertMatroidZ.htm#ribbonMatroidZNarayana) · [SymCat source history](https://github.com/PerAlexandersson/symmetricfunctions.com/commit/c697a84b47c36a53e3b63b3dcb4cd6305905a19d)

## Reproduce the finite checks

The flat-lattice computation covers every inner word through ground-set size 12 and four larger examples, for 2,051 ribbons. Run from this topic folder with Python 3.10 or later.

~~~sh
python3 -I -O code/ribbon.py --verify
~~~
