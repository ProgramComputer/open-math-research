# Balanced arrays at fixed row cap and arbitrary dimension

For integers $n,d,r$, let $P_n^{(r,d)}(q)$ count labeled binary $n\times d$ arrays with all row sums at most $r$, where the exponent of $q$ is the common column sum. Per Alexandersson's balanced-array conjecture asks for real-rootedness throughout the parameter range. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**Partial theorem.** For each fixed integer $r\ge1$ there is an $N_r$ such that for every $n\ge N_r$ and every $d\ge\max(2,r)$, $P_n^{(r,d)}$ has exactly $\lfloor nr/d\rfloor$ simple, strictly negative zeros. This leaves at most finitely many nonconstant cases for each fixed cap. The argument gives an existential threshold. The original conjecture remains open.

**Independent review.** An agent-assisted blind review accepted the written proof. [Referee report and editorial follow-up](review.md)

**Formal verification.** ⬜ None.

## Proof and supporting estimates

- [Proof](proof.md)
- [Manuscript PDF](paper.pdf) and [LaTeX source](paper.tex)
- [Fixed-profile local limit for column balance](fixed-profile-balance-llclt.md)
- [Coefficient and adjacent-ratio limits near quota zero](balanced-fixed-rank-lower-edge.md)
- [Coefficient and adjacent-ratio limits near the last quota](fixed-cap-upper-quota.md)
- [Transverse Gaussian approximation at a moving tilt](tall-sparse-transverse-saddle.md)
- [Global localization of the torus integral](fixed-cap-moving-u-localization.md)
- [Prior results and literature screen](literature.md)

Build the manuscript from this directory with `tectonic paper.tex`.
