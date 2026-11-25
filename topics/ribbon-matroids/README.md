# Ribbon matroids have the Narayana polynomial

For every connected ribbon lattice path matroid of rank $r$, the $Z$-polynomial equals the Narayana polynomial of order $r+1$. Simplifying the multi-fan gives a polygon with noncrossing diagonals. Deleting each diagonal preserves the polynomial, leaving a boundary cycle with the known Narayana formula.

[Proof](proof.md) · [Manuscript](paper.pdf) · [TeX source](paper.tex) · [Independent flat computations](results/ribbons.jsonl)

**🟨 Partial · Lean 4.** Lean verifies the polygon reduction with the general matroid identities as hypotheses, together with concrete rank-three flat recurrences. [Formal scope](lean/README.md) · [Kernel record](verification.json)

## Reproduce the finite checks

The flat-lattice computation covers every inner word through ground-set size 12 and four larger examples, for 2,051 ribbons. Run from this topic folder with Python 3.10 or later.

~~~sh
python3 -I -O code/ribbon.py --verify
~~~
