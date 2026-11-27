# Nine signed lattice maxima suffice for the determinant budget

In the bounded-aspect proof, the determinant sign requires the sum of four errors to lie below a positive main term. For $n\ge10000$, the aspect range $4\le n/k\le48$ is divided into nine intervals. The angle satisfies $S=\sin\theta>0$, $\cos\theta\ge0$ and $nS^2\ge6/5$. An exact rational calculation retains a margin exceeding $93/1000$ on every interval, even after rounding each of the four costs up to a millionth. The calculation uses nine signed lattice maxima and eight shared vectors of pole weights. [Previous uniform bound](uniform-carrier.md) · [Four-error determinant argument](https://github.com/ProgramComputer/open-math-research/pull/299)

## The product coefficients

For an interval $[\ell,X]$, put $K=\lfloor10000/X\rfloor$ and $c_0=(1-1/K)/(160X)$. The weight at odd index $p$ is $(1+c(p^2-1))^{-96}$. It decreases weakly in $c$. So does the explicit tail bound. Every linear coefficient in this interval uses $c\ge c_0$. Evaluating the maximum at $c_0$ therefore suffices for all 241 bins. The checker sums over odd $p$ from $-63$ through $63$, divides each weight by its gap from the center, omits the center itself, and maximizes over all 66 odd centers from $-65$ through $65$. It adds the certified tail and rounds the result upward to a multiple of $1/256$. [Signed lattice and tail bounds](nonprincipal-value.md) · [Linear tables](../lean/sine-comparison/LinearSlabs.lean)

Write $s$ for this upper bound, $m_i$ for the original degree mass and $A$ for the interval's lower radius. At scale $G=2^{32}$ put $L_i=\lceil Gm_i s/A\rceil$. The checker takes $Q_0=G$ and uses the recurrence

$$
Q_b=\left\lceil\frac{\sum_{i=1}^b i L_i Q_{b-i}}{bG}\right\rceil,\qquad 1\le b\le240.
$$

The original linear coefficients at scale $2^{56}$ are bounded by $2^{24}L_i$. Multiplying each $Q_b$ by $2^{24}$ therefore supplies upper bounds satisfying the recurrence inequality at the original scale. The isolated cutoff error uses a difference that subtracts the single occupied factor. In the first interval we need a lower bound for that subtraction. At center $3$, the poles $1$ and $-1$ each have unit weight and gaps $2$ and $4$. Their contribution is $3/4$ at every shape. This gives the lower integer bound $\lfloor Gm_i(3/4)/A\rfloor$ at the smaller scale. The other eight intervals can use zero. [Original product recurrence](../lean/sine-comparison/BinProductMajorant.lean)

## The two signed moments

For bin $b$ put $y=\max(1/X,1-b/(4\ell))$. Round $y$ down to the largest member below or equal to it in the set

$$
\lbrace 1/48,1/24,1/12,1/6,1/3,1/2,3/4,1\rbrace.
$$

Using the smaller argument in the decreasing pole weights and tail bounds gives upper bounds for both signed moments. The zeroth moment includes both principal poles. The first absolute moment for the nonprincipal term omits them. The checker rounds each retained weight upward at scale $2^{56}$ before summing. The one-factor cutoff error uses the same zeroth moment at the outer shape and the interval's signed lattice maximum.

The main term contributes at least $54/55$ on the first two intervals and $6000/12243$ on the other seven. Subtracting the four separately rounded costs gives the following lower bounds. Each entry in the last column has been rounded down.

| Aspect interval | Numerator of the lattice bound at scale 256 | Margin in millionths |
| --- | ---: | ---: |
| $[4,6]$ | 228 | 106587 |
| $[6,10]$ | 278 | 93581 |
| $[10,16]$ | 331 | 310306 |
| $[16,22]$ | 368 | 367466 |
| $[22,28]$ | 397 | 331751 |
| $[28,34]$ | 421 | 270956 |
| $[34,40]$ | 441 | 186752 |
| $[40,44]$ | 453 | 115288 |
| $[44,48]$ | 463 | 102060 |

## Reproduction and verification scope

Run the following from this directory with standard-library Python 3.9 or later.

~~~sh
python3 -I -B check-coarse-cost.py > /tmp/long-cycle-coarse-cost.txt
diff -u coarse-cost-output.txt /tmp/long-cycle-coarse-cost.txt
~~~

The checker uses integer and rational arithmetic throughout. A separate calculation using the earlier lattice and degree-mass implementations reproduced all nine margins before rounding the four costs. The standalone output records both variants. The end-to-end Lean check connecting all four coarse costs to the original permutation determinant is pending. [Standalone checker](check-coarse-cost.py) · [Complete arithmetic output](coarse-cost-output.txt) · [Verification tracking](https://github.com/ProgramComputer/open-math-research/issues/4)

On Lean 4.19.0 the kernel checked the lifted product recurrence, both signed moments, the subtraction at the cutoff, and the four-cost comparison on the same coefficient vector for each interval. The resulting budget theorem gives a uniform margin of $93581/10^6$. Its named axiom report lists `propext`, `Classical.choice` and `Quot.sound`. The specialization to the original two normalized permutation polynomials is awaiting the Lean 4.33.1 build. [Nine finite inequalities](../lean/paired-profile/CoarseNineMargins.lean) · [Uniform four-cost budget](../lean/paired-profile/CoarseCertifiedBudget.lean) · [Original permutation statement](../lean/paired-profile/RepositoryCoarseDeterminant.lean)
