# Column balance and outer roots near quota saturation

For a labeled binary array with $n$ rows, $d$ columns and row cap $r$, let $a_k$ count arrays with common column sum $k$ and put $D=\lfloor nr/d\rfloor$. This package proves an explicit near-saturation bound for the original counts. It also confines a potential failure of [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) to a narrower band.

For $n\ge\lceil e^{50}\rceil$ and $n/4\le d\le n$, every internal quota $k$ with $nr/d-k\le\tfrac12\sqrt{n/\log n}$ satisfies $a_k^2>4a_{k-1}a_{k+1}$. Consequently the polynomial has at least $D-k$ distinct negative roots to the left of $-\sqrt{a_{k-1}/a_{k+1}}$. The proof combines a known stable-polynomial lower bound with an explicit uniform Fourier–Bessel upper bound and a scalar profile average. [Lower bound and sources](lower.md) · [Profile upper bound](upper.md) · [Proof and constants](consequences.md)

For the same row cutoff and $59n/200\le d<n$, a nonreal zero would require a quota with raw curvature at most four and a drop in normalized curvature from the previous quota. Its deficit distance must be strictly between $\tfrac12\sqrt{n/\log n}$ and $1+n\sqrt{8\log n/d}$. The transition between these scales remains open. [Necessary band](consequences.md#necessary-band-for-a-failure-of-real-rootedness)

The exact examples at $d=3n/10$ and $r=d/2$ certify the following lower bounds on the number of simple outer negative roots. Each example certifies all the roots outside its specified geometric radius by Rouché’s theorem.

| Rows | Certified outer roots |
| ---: | ---: |
| 4,000 | 2 |
| 10,000 | 5 |
| 100,000 | 22 |
| 1,000,000 | 76 |
| 10,000,000 | 244 |

Replay the exact rational certificates with the Python standard library from the repository root.

~~~sh
python3 -B topics/balanced-arrays/bessel-margins/certificates.py | diff - topics/balanced-arrays/bessel-margins/certificates.jsonl
~~~

For regular row profiles, the variance of the third column after conditioning the first two to balance strictly exceeds the Gaussian conditional variance. The excess has an explicit bound independent of the number of rows. This rules out an exact variance contraction at that step. [Variance calculation and exact replay](conditional-variance.md)

**⬜ None** for Lean or Rocq. The [lower source comparison](lower-review.md), [upper-bound audit](upper-review.md) and [consequences review](consequences-review.md) are agent-assisted. [Research issue #2](https://github.com/ProgramComputer/open-math-research/issues/2)
