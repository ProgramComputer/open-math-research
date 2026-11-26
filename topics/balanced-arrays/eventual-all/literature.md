# Prior work on eventual balanced-array roots and fixed-profile enumeration

Checked 2026-11-26. The two claims have separate hypotheses.

## A single eventual row threshold

The candidate gives an absolute $`N`$ such that for all $`n\ge N`$, every $`d\ge2`$ and $`1\le r\le d`$, the polynomial counting labeled binary $`n\times d`$ arrays by their common column sum with row sums at most $`r`$ has $`\lfloor nr/d\rfloor`$ simple negative roots. For $`d=1`$ the polynomial is $`(1+q)^n`$. Per Alexandersson's exact conjecture on SymCat is real-rootedness for **all** $`n\ge0`$, $`1\le r\le d`$, without a simplicity requirement. His open issue gives the same diagonal elementary-symmetric coefficient and describes finite rank-two computations and an unpublished eventual argument for $`U(2,4)`$. The independent bounded investigation #165 also remained open. [Primary SymCat statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Author issue #2005](https://github.com/PerAlexandersson/RealRooted/issues/2005) · [Independent issue #165](https://github.com/1337isnot1337/solved-conjectures/issues/165)

- The project's fixed-pair theorem gives simple negative zeros with strict consecutive-row interlacing eventually at each proper fixed pair. Its threshold depends on both $`r`$ and $`d`$. Publication #91 makes the threshold uniform in dimension at each fixed cap. Neither gives a threshold uniform in both parameters. [Fixed-pair manuscript](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/fixed-rank-eventual.tex) · [Fixed-cap theorem](https://github.com/ProgramComputer/open-math-research/tree/f7e10f84dd21fec44ca58c60bae0879d12ebd89b/topics/balanced-arrays/fixed-cap)
- Publications #93 and #95 give absolute quartic-log and quadratic bounds, #97 gives eventual simplicity at every fixed positive quadratic aspect, and #99 gives all caps for $`n\ge Cd^{5/3}`$ and all dimensions for $`\min(r,d-r)\le c n^{1/5}`$ at large $`n`$. The separate logarithmic dimension bound gives all caps for $`d\ge Bn/\log n`$ at large $`n`$. These conditions leave, for instance, $`d=\lfloor n^{2/3}\rfloor`$, $`r=\lfloor d/2\rfloor`$. [#99 published package](https://github.com/ProgramComputer/open-math-research/tree/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/fifth-thirds) · [#97 published package](https://github.com/ProgramComputer/open-math-research/tree/605cc467a5be93a8408519da331e46f1008df96e/topics/balanced-arrays/critical-aspect) · [Growing-dimension results](https://github.com/ProgramComputer/open-math-research/tree/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/dense-regime)
- The prior exact results at $`r=d-1`$, $`r=d`$, $`U(2,4)`$ and through degree fourteen have separate proofs. Coefficient separation deals with $`d\ge n`$. Combined with an eventual theorem, this would leave a finite range of possible exceptions, since for bounded $`n`$ only $`2\le d<n`$ would remain. An existential $`N`$ does not verify that range. [Reviewed balanced-array results](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/README.md) · [Coefficient separation](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/orientation-normalization.md)

## Balance probability for a fixed profile

Let $`k/d\to\beta\in(0,\infty)`$, and let $`s_1,\ldots,s_m`$ sum to $`dk`$ with $`\Delta=\max_i s_i=o(d)`$. The proposed probability of equal column sums for independent uniform subsets of the respective sizes is

$$
\sqrt d\thinspace (2\pi\Lambda)^{-(d-1)/2}\exp(-1/(12\beta))(1+o(1)),
\qquad \Lambda=\sum_i\frac{s_i(d-s_i)}{d(d-1)}.
$$

This is the prescribed-margin count divided by $`\prod_i\binom d{s_i}`$. Deleting zero rows leaves between $`dk/\Delta`$ and $`dk`$ rows, potentially with highly unequal positive sizes.

### A subrange implied by Greenhill, McKay and Wang

Their Theorem 1.3 and Corollary 5.2 cover $`\Delta=o(d^{1/3})`$. The product of maximal margins is $`\Delta k=o((dk)^{2/3})`$, the standardized column variance is zero, and the standardized row variance is $`O(\Delta)`$. With $`Q=\sum_i s_i^2/(dk)`$, $`p=k/m`$ and $`\nu=(d-1)/2`$, dividing their count by the product of row binomials gives

$$
K\exp\negthinspace \left(\frac{Q-dp-1+p}{2(1-p)}+o(1)\right),
\qquad K=\frac{\binom m k^d}{\binom{md}{dk}}.
$$

Since $`p\le\Delta/d=o(1)`$ and $`m\gg d`$, Stirling’s expansion gives $`K=\sqrt d(2\pi k(1-p))^{-\nu}\exp(-d/(12k)+o(1))`$. Retain the $`1/(12j)`$ factorial terms: $`-d/(12k)`$ survives, while $`d/m=o(1)`$ and $`d/k^3=o(1)`$. Finally

$$
\frac{\Lambda}{k(1-p)}
=1-\frac{Q-dp-1+p}{(d-1)(1-p)}.
$$

The negative $`\nu`$th power contributes exactly the exponent from Corollary 5.2 up to $`O(\Delta^2/d)=o(1)`$. This proves the proposed formula in the overlapping range, including every bounded profile. At singleton row sizes the independent exact computation is $`(dk)!/[d^{dk}(k!)^d]`$, with the same correction by Stirling. [GMW version of record](https://doi.org/10.1016/j.jcta.2005.03.005) · [Authors’ text, Corollary 5.2](https://web.maths.unsw.edu.au/~csg/papers/irregular-final.pdf#page=33)

### Restrictions of other enumeration results

- Canfield and McKay, Electron. J. Combin. 12 (2005), R29, Theorem 1(c), allow extreme aspect and arbitrary density when **both** margins are regular. In their notation the smaller row count $`m`$ satisfies $`m=O((t(m-t)n)^{1/4-\varepsilon})`$, up to transpose. Their Theorem 1(a), attributed to McKay and Wang, and their Conjecture 1 also concern biregular sequences. [Canfield–McKay, Theorem 1 and Conjecture 1](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v12i1r29) · [McKay–Wang](https://www.sciencedirect.com/science/article/pii/S0024379503005068)
- Canfield, Greenhill and McKay, J. Combin. Theory Ser. A 115 (2008), Theorem 1, require row and column deviations $`O(d^{1/2+\varepsilon})`$ and $`O(m^{1/2+\varepsilon})`$, mutual size constraints $`d=o(A^2m^{1+\varepsilon})`$ and $`m=o(A^2d^{1+\varepsilon})`$, and their density/aspect inequality, where $`A=p(1-p)/2`$. These conditions need not hold here. [Version of record](https://doi.org/10.1016/j.jcta.2007.03.009) · [Authors’ text, Theorem 1](https://web.maths.unsw.edu.au/~csg/papers/CGM.pdf)
- Liebenau and Wormald, Random Structures Algorithms, Theorem 1.1 and Remark 1.2, require controlled degree deviations and aspect. For fixed $`0<\kappa<1/10`$, the published bipartite hypotheses include $`m/d^{3/2-5\kappa}+d/m^{3/2-5\kappa}=o(p^{1/2-5\kappa})`$, average degrees dominating each fixed logarithmic power, and deviations at most the respective mean to power $`1/2+\kappa`$. Column regularity does not remove the row deviation or aspect requirements. [Version of record](https://doi.org/10.1002/rsa.21105) · [Preprint](https://arxiv.org/abs/2006.15797)
- Barvinok and Hartigan’s binary Gaussian correction, §2.5 equation (2.5.4), assumes fixed $`\delta`$-tameness, including comparable dimensions and entropy-maximizing probabilities bounded away from 0 and 1. Symmetry forces those probabilities to be $`s_i/d=o(1)`$ in the present profile. Their cited broader logarithmic estimates do not give a relative $`1+o(1)`$ or the constant correction. [Version of record](https://doi.org/10.1002/rsa.20409) · [Authors’ text, §2.5](https://dept.math.lsa.umich.edu/~barvinok/degree.pdf)
- Greenhill, Hasheminezhad, Iliffe and McKay, Discrete Appl. Math. (2026), Theorem 2.2, estimate the constrained count as a ratio to the unconstrained fixed-margin count, which remains on the right-hand side. Removing all forbidden positions gives an identity. Their Theorem 2.1 for the unconstrained count cites GMW with the same sparse maximum-product hypothesis. [Version of record](https://www.sciencedirect.com/science/article/pii/S0166218X26005147) · [First arXiv version, §2](https://arxiv.org/html/2601.04822v1)
- Isaev and McKay's cumulant expansion for graph factors accepts large degree variation but requires the host graph's least signless-Laplacian eigenvalue to be a positive constant times its order, Assumption 1.1(d). It is zero for the complete bipartite host here. Their Fourier and cumulant techniques are pertinent without supplying the desired binary-margin formula directly. [2025 arXiv preprint, §1.1](https://arxiv.org/pdf/2508.18731#page=4)

For a concrete admissible profile outside the cited ranges, take $`d=t^2`$, $`k=d`$, $`m=t^3`$ for even $`t`$, with half of the rows of size $`t/2`$ and half of size $`3t/2`$. Now $`dk=t^4`$, $`\Delta=3t/2`$, $`p=1/t`$ and the row deviations have order $`t`$. It misses GMW, biregularity, CGM’s mutual size requirements, LW’s aspect and deviation hypotheses, and fixed $`\delta`$-tameness. The sources examined do not supply the unrestricted-profile estimate, while the correction is already known in the overlapping regime. This does not establish priority.

## Searches and limits

Searches included ‘Alexandersson "balanced arrays" eventual real rooted all ranks dimensions negative zeros GitHub’, ‘binary matrices prescribed margins one margin regular max row degree sparse asymptotic enumeration McKay Greenhill Barvinok Hartigan Liebenau Wormald’, ‘enumeration binary matrices prescribed unequal row sums equal column sums large number of rows sparse asymptotic irregular tall matrices non identical subset local limit’, and ‘site:arxiv.org binary matrices fixed margins sparse enumeration arbitrary number rows max degree semiregular switching’. A Scholar-index query ‘site:scholar.google.com asymptotic enumeration "binary" "equal column sums" irregular sparse row margin’ surfaced no relevant primary result. [Earlier arXiv and Scholar screen](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/fifth-thirds/literature.md)

GitHub CLI issue searches for ‘"balanced arrays"’ and ‘"binary matrices" "prescribed margins" asymptotic’ returned the three known open balanced-array threads and no relevant margin-enumeration issue. Exact-title code search for ‘"balanced arrays of uniform matroids"’ found repository literature notes. Indexed X searches ‘site:x.com Alexandersson balanced arrays real rootedness’ and ‘site:x.com "balanced array" real-rooted Alexandersson conjecture solved’ surfaced no relevant announcement with a proof. X coverage is limited to indexed public results. No independent universal eventual theorem, full resolution of the original conjecture, or enumeration theorem for the entire proposed profile range surfaced.
