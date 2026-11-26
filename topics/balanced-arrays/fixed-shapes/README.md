# A decision procedure for fixed balanced-array minors

Let $`a_k(n,r,d)`$ count labeled binary arrays with $`n`$ rows, $`d`$ columns, column sum $`k`$, and row sum at most $`r`$. Specialize the complete homogeneous symmetric function $`h_k`$ to $`a_k(n,r,d)`$ in the Jacobi–Trudi determinant of a fixed skew shape.

An exact algorithm decides whether that determinant is nonnegative for all row counts, caps and dimensions. A separate finite algorithm decides coefficientwise nonnegativity in independent cell weights. The accompanying exact certificate proves binomial-basis nonnegativity in the row count for every skew shape with at most 18 cells. The fixed-shape cutoff is coefficientwise in cell weights, and the finite-dimensional decision procedure and weight-18 conclusion concern unweighted arrays with uniform cap. This is a partial result on [Alexandersson's balanced-array conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm).

- [Proof and certificate coverage](proof.md)
- [Manuscript source](paper.tex)
- [Earlier work and the uncapped case](literature.md)
- [Independent cutoff checks](fixed-minor-review/README.md) and [independent weight-18 review](fixed-minor-review/review-w18.md)

**Formal verification**　⬜ None. The proof was reviewed with agent assistance. The certificate replay uses exact integer arithmetic.

## Reproduction

Run from this directory with Python and `python-flint==0.9.0` installed. The first two invocations show a straight and a skew shape. The replay checks the cutoff ledger and all residual cases of the weight-18 certificate.

```sh
python decide_shape.py 2,2,2
python decide_shape.py 3,2 --inner 1
python fixed-minor-review/check.py
python fixed-minor-review/replay_w18.py
```

The replay expects the [cutoff ledger](universal-w18/cutoffs.jsonl) and [compressed residual ledger](universal-w18/residuals.jsonl.gz) in their checked-in locations. Its expected counts and checksums are in the [recorded output](fixed-minor-review/replay_w18.log).
