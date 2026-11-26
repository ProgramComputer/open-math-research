# Eventual negative zeros for balanced arrays

**Partial theorem.** There is an absolute row threshold $N$ such that, for every $n\ge N$, every $d\ge2$ and every $1\le r\le d$, the balanced-array polynomial has exactly $\lfloor nr/d\rfloor$ simple, strictly negative zeros. The coefficient of $q^k$ counts labeled binary $n\times d$ arrays with common column sum $k$ and every row sum at most $r$. At $d=1$, the polynomial is $(1+q)^n$.

Per Alexandersson’s original conjecture asks for real-rootedness at every row count. The eventual theorem leaves a finite range of possible exceptions, since $d\ge n$ is covered by coefficient separation. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**Status.** An independent, agent-assisted blind referee accepted the written uniform eventual theorem, taking the cited fixed-quadratic and large-dimension theorems as inputs. The row threshold is ineffective, and the verdict leaves the original all-row conjecture open. [Uniform theorem referee report](review.md)

**Fixed-profile review.** An anonymous, agent-assisted independent referee checked the fixed-profile enumeration formula. [Fixed-profile referee report](fixed-profile-review.md) [Editorial follow-up to both reports](editorial.md)

**Formal verification**　🟨 Partial · Lean 4. The research build verifies the exact coefficient support and degree directly from labeled arrays, and the one-column identity. The eventual negative-root assertion and its uniform estimates remain open in Lean. [Checked components, pins and axiom reports](lean/README.md)

## Proof and supporting estimates

- [Main proof](proof.md)

- [Angular signs from the analytic transverse expansion](analytic-angular-signs.md)
- [Fixed-profile global localization](sparse-fixed-profile-global-localization.md)
- [Fixed-profile local integral and constant correction](sparse-fixed-profile-edgeworth.md)
- [Edgeworth transfer for bounded cap ratio](edgeworth-bounded-rank-ratio.md)
- [Finite lower-quota overlap](edgeworth-finite-lower-overlap.md)
- [Sparse-profile transfer in the upper quota band](sublinear-b-generic-upper-transfer.md)
- [Prior results and source screen](literature.md)
- [Manuscript PDF](paper.pdf) and [LaTeX source](paper.tex)

Build from this directory with `tectonic paper.tex`.
