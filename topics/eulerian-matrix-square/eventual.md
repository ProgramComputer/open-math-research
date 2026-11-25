# Every sufficiently large Eulerian-square row has only real zeros

Let $A(n,k)$ count permutations of $[n]$ with $k-1$ descents for $1\le k\le n$. Set $A(0,0)=1$ and all other boundary entries equal to zero. Write
$$
 P_n(x)=\sum_{k=1}^n (A^2)(n,k)x^k=x H_n(x)
$$
for the row polynomial of the ordinary matrix square. **There exists an integer $n_0$ such that for every $n\ge n_0$, the polynomial $P_n$ has one simple zero at zero and $n-1$ distinct negative zeros.** Mao and Wang ask for all rows. The threshold in this proof is existential. [Original preprint, §4](https://arxiv.org/abs/2607.01572)

## Proof

For $n\ge1$ the coefficient of $x$ in $P_n$ is $\sum_k A(n,k)A(k,1)=n!$, and its leading coefficient is one. Thus $H_n$ has degree $n-1$ and a nonzero constant term. Put $N=n+1$ and let $y=\log |x|$ for a complex zero of $H_n$.

1. For any fixed $R>0$ the closed-disk theorem proves that every zero of $H_n$ with $|x|\le R$ is simple and negative for all sufficiently large $n$. This includes roots whose moduli approach zero. [Closed disk](right-half.md) · [Fixed annulus](compact-annuli.md)
2. There is an absolute $Y_0>0$ such that for all sufficiently large $n$, every zero with $Y_0+1\le y\le3N^{1/4}$ is simple and negative. The proof counts the winding number on circles whose principal phase is an integral multiple of $\pi$. The count increases by exactly one from one circle to the next. A single root in such an annulus has multiplicity one, is real by conjugation and is negative by positivity of the coefficients. [First family of moving circles](lower-cross-sections.md)
3. There is an absolute $a>0$ such that the same conclusion holds on $\tfrac32N^{1/4}\le y\le (a/2)\sqrt{N/\log N}$. In this range two terms from each of two Eulerian pole expansions can compete. Their mixed logarithmic difference is positive to leading order and bounds their cancellation at the counting circles. [Four-pole winding argument](left-cross-sections.md)
4. For **each fixed** $d>0$, the conclusion holds on $y\ge d\sqrt{n/\log n}$ for all sufficiently large $n$. In the reciprocal polynomial the two principal one-variable factors have real zeros, which can approach each other. At a near collision a mixed derivative term gives the local quadratic $\xi^2-\Delta^2-1$. Its two simple real roots remain separated uniformly for real $\Delta$. The coefficient estimates control the entire transition and meet the count of the extreme pairs. [Lower logarithmic range](theta-lower-bridge.md) · [Square-root and upper logarithmic ranges](theta-transition.md) · [Extreme pairs](growing-large-roots.md)

Fix $R=e^{Y_0+2}$ and $d=a/4$. The first two ranges overlap on $Y_0+1\le y\le Y_0+2$, and the next two overlap on $\tfrac32 N^{1/4}\le y\le3N^{1/4}$ for all sufficiently large $n$. Finally, $\sqrt{(n+1)/\log(n+1)}\,/\sqrt{n/\log n}\to1$, so the fourth interval starts strictly below the upper endpoint of the third. Take the maximum of the finitely many thresholds for these fixed parameters. Every zero now belongs to one of the four ranges. This proves the theorem.

## Verification and the all-row gap

Two separate implementations give exact real-rootedness checks for every $n$ from 0 through 256, as well as $384,512,768,1024$. The argument above supplies no upper bound on $n_0$. A counterexample to the all-row Eulerian clause, if one exists, therefore belongs to a finite set whose largest possible index is currently unknown. Global interlacing of consecutive Eulerian-square rows is a stronger question. [Computations and Lean scope](README.md)
