# Binomial normalization of balanced-array coefficients

Supporting research on [Per Alexandersson’s balanced-array conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays). The conjecture concerns the original quota polynomial.

Let $`a_k`$ count the original labeled arrays with $`n`$ rows, $`d\ge2`$ columns, uniform cap $`r`$ and quota $`k`$. Write $`D=\lfloor nr/d\rfloor`$. The proposed auxiliary polynomial is

$$
B(q)=\sum_{k=0}^{D}\frac{a_k}{\binom nk}q^k.
$$

Its real-rootedness is sufficient for real-rootedness of the original count. This transfer is valid at the actual degree $`D`$. A universal proof of real-rootedness of $`B`$ remains open in this investigation. A [three-column proof](../three-column-all-rows.md) establishes the normalized case $`d=3,r=2`$.

## Recovery by a finite multiplier

For $`0\le m\le N`$, the multiplier $`c_k\mapsto\binom Nk c_k`$ acts on degree at most $`m`$ and has symbol

$$
J_{N,m}(q)=\sum_{k=0}^m\binom mk\binom Nkq^k.
$$

Let $`L_N`$ be the Legendre polynomial. Its binomial expansion gives $`F_N(q)=(1-q)^N L_N((1+q)/(1-q))=\sum_k\binom Nk^2q^k`$, with all zeros negative by the location of Legendre zeros. Apply reversal in degree $`N`$, differentiate $`N-m`$ times, then reverse in degree $`m`$ and multiply by $`m!/N!`$. The result is $`J_{N,m}`$. These operations preserve real negative zeros by Rolle's theorem and reciprocation. The finite multiplier criterion now applies. With $`N=n,m=D`$ it sends $`B`$ to the original polynomial. [Kostov–Shapiro, Schur–Szegő composition criterion](https://staff.math.su.se/shapiro/Articles/FinalNote.pdf)

The correction that divides only by $`\binom nk/\binom Dk`$ would instead need recovery multiplier $`\binom nk/\binom Dk`$, whose symbol is the plain degree-$`D`$ truncation of $`(1+q)^n`$. This fails already at $`n=4,D=2`$, giving $`1+4q+6q^2`$ with discriminant $`-8`$.

## Rank one and a uniform separation regime

At rank one,

$$
\frac{a_k}{\binom nk}=\prod_{j=1}^{d-1}\binom{n-jk}{k}.
$$

For each $`1\le j\le d-1`$, the polynomial with coefficients $`\binom{n-jk}{k}`$ is the independence polynomial of the $`j`$th power of a path on $`n-j`$ vertices. A $`k`$-subset has adjacent selected indices at least $`j+1`$ apart, and subtracting $`j`$ times each selected index's zero-based order gives the stated binomial count. The neighbors of any vertex on each side form a clique, so the graph is claw-free and the polynomial has real negative zeros. If $`D=0`$ the rank-one statement holds directly and there is no issue with the path length. [Chudnovsky–Seymour](https://doi.org/10.1016/j.jctb.2006.06.001)

To multiply the coefficient factors, suppose $`H=\sum h_k q^k`$ has real negative zeros and degree $`M\ge D`$. The same binomial multiplier applies with the two symbol indices interchanged, since $`J_{D,M}=J_{M,D}`$, with missing coefficients taken as zero. Applying $`c_k\mapsto\binom Dk c_k`$ in degree $`M`$ gives the real-rooted polynomial $`\sum_{k\le D}\binom Dk h_k q^k`$. Its real negative zeros make $`c_k\mapsto h_kc_k`$ an admissible multiplier in degree $`D`$. Begin with the shortest path-power factor ($`j=d-1`$, degree $`D`$) and apply the other factors in this way. This proves once-normalized real-rootedness for every rank-one shape. For full cap, the same binomial multiplier immediately proves it, since $`a_k/\binom nk=\binom nk^{d-1}`$.

For general cap, the existing log-concavity of $`p_k=a_k/\binom nk^d`$ implies that the internal curvature ratio of $`B`$ is at least

$$
\left((1+1/k)(1+1/(n-k))\right)^{d-1}.
$$

At each internal quota the ratio strictly exceeds four whenever either $`d-1\ge(n+1)\log4/4`$ or $`d(d-1)\ge nr\log4`$. For the first condition use $`\log(1+1/x)>2/(2x+1)`$ and convexity. For the second use $`\log(1+1/k)>1/(k+1)`$ and $`k+1\le D\le nr/d`$. The usual strict coefficient-separation criterion gives simple negative zeros. [Orientation inequality](../orientation-normalization.md)

## Exact obstructions to stronger normalizations

- Dividing by the native binomial $`\binom Dk`$ fails at $`(n,r,d)=(5,1,2)`$. The actual coefficients $`(1,20,30)`$ give $`(1,10,30)`$ and discriminant $`-20`$.
- Dividing twice by $`\binom nk`$ fails at $`(4,1,2)`$. The actual coefficients $`(1,12,6)`$ give a positive multiple of $`(12,9,2)`$ and discriminant $`-15`$.
- The validity probabilities $`p_k`$ themselves fail at $`(5,2,4)`$. The actual coefficients $`(1,540,2490)`$ give a positive multiple of $`(1000,864,249)`$ and discriminant $`-249504`$.

A different question is how many source factors must remain. The [retained-exponent threshold](threshold.md) gives lower and upper asymptotic bounds on the smallest universally sufficient exponent $`S(n)`$. At $`(n,r,d)=(4,5,7)`$ retaining only one factor gives a quadratic with discriminant $`-48335287/21233664`$. The [independent edge review](edge-review.md) includes an inclusion–exclusion derivation. Removing one factor keeps $`d-1`$ factors and remains a viable sufficient route.

## Exact replay

From this folder run the standard-library checks.

```sh
python3 -B check.py
python3 -B check-retained-one.py
python3 -B check-archives.py
python3 -B section_certificate.py --verify section-cutoffs.jsonl
```

The witness replays count labeled capped rows or labeled column subsets. The archive replay computes exact Sturm sequences after dividing each quota coefficient by one source binomial. All 275 corank-one polynomials, 74 distinct cap-two dimension endpoints and 369 cap-two source-range polynomials pass, with 688 distinct parameter triples in the union. See the [corank-one archive](../results/corank-one.jsonl.gz), the [cap-two extension archive](../results/column-extension-cap-two.jsonl.gz) and the [cap-two source-range archive](../results/source_range.jsonl). The script reads the pinned Git blobs, so the archive files need not be materialized in the checkout. In a shallow checkout, run `git fetch origin 1740556cba01ba9d32731d31cc9789e657c19126` first.

The [dimension certificate archive](section-cutoffs.jsonl) covers nine fixed row-count and retained-exponent choices. For example, at $`n=4,s=2`$ it proves real-rootedness for every cap once $`d\ge48`$. With SymPy installed, use `python3 -B section_certificate.py 4 2` to generate a certificate for that pair. The bounds and witnesses have agent-assisted mathematical checks. No Lean or Rocq proof is claimed.
