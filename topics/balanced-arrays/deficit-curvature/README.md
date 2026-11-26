# Screen of a proposed upper-quota curvature estimate

Let $a_k$ count labeled binary matrices with $n$ rows, $d$ columns, common column sum $k$, and each row sum at most $r$. For internal quotas $1\le k<D=\lfloor nr/d\rfloor$, let $\Gamma_k=a_k^2/(a_{k-1}a_{k+1})$ and $e=nr-dk$. We screened the proposed estimate

$$
\log\Gamma_k\ge \frac{nd}{n+e+d}\log\left(1+\frac d{e+d}\right).
\tag{1}
$$

This proposed estimate remains unproved for general balanced arrays. Even with this estimate, a separate argument would be needed to locate the roots left by the below-cap comparison. The [scalar convolution argument](scalar.md) concerns row deficits without equal-column conditioning. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Below-cap comparison](../dense-regime/below-cap/README.md) · [Existing normalized log-concavity bound](../orientation-normalization.md)

## Exact archive screen

The [deduplicated output](screen.jsonl.gz) is keyed by $(n,r,d)$. Inputs are the following files from `topics/balanced-arrays/results/` at the pinned Git commit `5bcefb9ba2439f8248fed98c75d1c6b52d21023d`. The script loads them with `git show`. It requires every repeated coefficient vector to agree exactly and retains all input archive names for each output record.

- Column extensions. `column-extension-cap-two.jsonl.gz`, `column-extension-corank-two.jsonl.gz`, `column-extension-screen.jsonl.gz`, and `column-extension-seven.jsonl.gz`. Left and right vectors have keys $(n,r,d)$ and $(n,r,d+1)$.
- Canonical coefficient tables. `corank-one.jsonl.gz`, `degree_reduction.jsonl`, `linear_tail_ranges.jsonl`, and `source_range.jsonl`. Records without explicit coefficients are omitted.

| Input selection | Distinct vectors | Internal nodes | Strict passes | Equalities | Violations |
|---|---:|---:|---:|---:|---:|
| Four column-extension archives, 529 transitions | 676 | 6,061 | 6,061 | 0 | 0 |
| Four canonical coefficient archives | 1,023 | 8,309 | 8,309 | 0 | 0 |
| Deduplicated union | 1,492 | 13,346 | 13,346 | 0 | 0 |

The checker uses Arb enclosures of the logarithmic gap, starting at 96 bits. A gap ball excluding zero certifies its sign. For a ball still containing zero after three precision steps, the checker reduces the integer ratios and compares exact cross-multiplied powers. Every archive comparison was certified by Arb. Synthetic examples exercised strict pass, strict failure, and the exact equality fallback.

Each node array records the quota, deficit, outcome, and certification method in that order. From the repository root with Python 3 and `python-flint==0.9.0`, run

~~~sh
python3 topics/balanced-arrays/deficit-curvature/check.py
~~~

The command recomputes all signs and compares every record with the checked gzip archive. It also reports the two input subsets and their union. Use `--repo` or `--revision` to select another checkout or input revision and `--output` to regenerate the archive.

## Analytic checks for counterexamples

**Rank one.** The count is $a_k=n!/[e!\thinspace (k!)^d]$. Hence

$$
\Gamma_k=\left(\frac{k+1}{k}\right)^d
\frac{(e+d)!(e-d)!}{e!^2},
\qquad
\frac{(e+d)!(e-d)!}{e!^2}
=\prod_{i=1}^d\left(1+\frac d{e-d+i}\right)
\ge (1+d/e)^d .
$$

This is strictly stronger than (1). All internal quotas satisfy $e\ge d$.

**Full rank.** Here $a_k=\binom nk^d$ and $e=d(n-k)$. Thus $\log\Gamma_k=d\log[(1+1/k)(1+1/(n-k))]$, whereas the right side of (1) is at most $d\log(1+1/(n-k+1))$. The inequality is strict.

**Fixed dimension, compact interior quotas.** Write $x=k/n$ and $\mu=r-dx=e/n$, and give the single row size $S$ tilted mass proportional to $\binom ds w^s$ for $0\le s\le r$, at mean $dx$. For fixed $d,r$ and $x$ tending to a strictly interior limit, the [local coefficient saddle](../geometric-centers/bulk-center-coefficients.md) gives $n\log\Gamma_k\to d^2/\mathrm{Var}(S)$ at the limiting tilt. The right side of (1), multiplied by $n$, tends to $d^2/[\mu(1+\mu)]$. The deficiency $r-S$ has mean $\mu$ and log-concave mass on its support. The ratio of its mass to that of a geometric distribution of mean $\mu$ is log-concave. Its excess over one is supported on an interval. Subtracting a chord from any convex test function across the two crossing points gives convex-order domination by the geometric law, since the two distributions have equal mass and mean. For the square the comparison is strict because the deficiency has finite support and the geometric tail is positive. Consequently $\mathrm{Var}(S)<\mu(1+\mu)$, giving a strict asymptotic margin. [Yu, Theorem 12 and Lemma 1](https://arxiv.org/pdf/1010.2043#page=9)

**Fixed distance from either endpoint.** At fixed lower quota $k$ with fixed $d,r$, $a_k/n^{dk}\to1/(k!)^d$ and the two adjacent limits give $\Gamma_k\to(1+1/k)^d>1$, while the right side of (1) tends to zero. At a fixed positive number of steps from the upper quota for fixed $1\le r<d$, pass to a residue class with $e$ fixed. The [fixed-rank reversed endpoint coefficient ratios](../fixed-rank-eventual.tex) tend, after geometric scaling, to a constant times $1/e!$ at each of the three successive deficiencies. Hence $\Gamma_k\to(e+d)!(e-d)!/e!^2$, and the proposed lower bound on $\Gamma_k$ tends to $(1+d/(e+d))^d$. The rank-one factorial comparison proves a strict margin for these limits as well.

These checks locate no counterexample. They leave the finite proper-rank cases and regimes in which dimension and quota vary jointly outside these limits unresolved.

**⬜ None.** The screen has exact arithmetic checks. The accompanying scalar argument and analytic special cases have written proofs without Lean or Rocq formalization.
