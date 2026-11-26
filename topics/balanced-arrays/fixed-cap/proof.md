# A uniform row threshold in every dimension at fixed cap

**Theorem.** For every fixed integer $`r\ge1`$ there is an integer $`N_r`$ such that, simultaneously for all $`n\ge N_r`$ and all dimensions $`d\ge\max(r,2)`$, the balanced-array polynomial $`P(q)=\sum_{k=0}^{D}a_kq^k`$ has $`D=\lfloor nr/d\rfloor`$ simple negative zeros. Here $`a_k`$ counts the labeled binary matrices of size $`n`$ by $`d`$ with row sums at most $`r`$ and column sums all equal to $`k`$. At $`r=d=1`$, $`P(q)=(1+q)^n`$.

In particular the original real-rootedness conjecture has only finitely many possible counterexamples for each cap. Indeed for $`n<N_r`$ it suffices to consider $`d<n`$, since $`d\ge n`$ is covered by coefficient separation (and the zero-row polynomial is constant). Thus the caps of any sequence of distinct counterexamples must tend to infinity. The proof supplies no explicit $`N_r`$ and no consecutive interlacing theorem. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Orientation inequality and separation](https://github.com/ProgramComputer/open-math-research/blob/ba7ddfd7efb37cac33769f4fdfed749e1b5bf58a/topics/balanced-arrays/orientation-normalization.md)

At every integer quota $`0\le k\le D`$, choose any row-size profile $`(s_1,\dots,s_n)`$ with $`0\le s_j\le r`$ and total $`dk`$, which is possible since $`dk\le nr`$. Assign successive blocks of lengths $`s_j`$ in the cyclic list of the $`d`$ column labels to the corresponding rows. No block repeats a label since $`s_j\le d`$, and each label occurs exactly $`k`$ times in the whole list of $`dk`$ positions. This realizes every such profile and gives $`a_k>0`$ throughout the degree range.

## The dimension range that remains

A failure of the theorem would give a sequence with $`n\to\infty`$ at one fixed $`r`$. A bounded-dimensional subsequence is excluded by the fixed-pair eventual theorem when $`r<d`$ and by the unrestricted binomial multiplier theorem when $`r=d\ge2`$. We can therefore take $`d\to\infty`$. The rank-dependent dimension bound excludes $`d\ge C_r\sqrt{n/\log n}`$. On the remaining sequence $`b=d^2/n\to0`$. Write $`T=nr/d`$, $`D=\lfloor T\rfloor`$, so that $`D/d\to\infty`$. We prove the required signs for every sequence $`d\to\infty`$, $`b\to0`$ at fixed $`r`$. [Fixed-pair theorem](https://github.com/ProgramComputer/open-math-research/blob/ba7ddfd7efb37cac33769f4fdfed749e1b5bf58a/topics/balanced-arrays/fixed-rank-eventual.pdf) · [Unrestricted case](https://github.com/ProgramComputer/open-math-research/blob/ba7ddfd7efb37cac33769f4fdfed749e1b5bf58a/topics/balanced-arrays/finite-linear-reduction.md) · [Rank-dependent theorem](https://github.com/ProgramComputer/open-math-research/tree/ba7ddfd7efb37cac33769f4fdfed749e1b5bf58a/topics/balanced-arrays/dense-regime/rank-dependent)

## Where the phases are attained

For $`w>0`$ write $`H(w)=\sum_{s=0}^r\binom ds w^s`$ and let $`S`$ have these size weights, normalized by $`H(w)`$. Put $`\mu=\mathbb E S`$, $`V=\mathrm{Var}(S)`$, $`y=n\mu/d`$, $`\phi=\pi/d`$ and $`\nu=(d-1)/2`$. The tilt with mean quota $`x`$ is written $`w_x`$, so $`y(w_x)=x`$. Write $`H_\phi=H(we^{i\phi})`$. If $`G(S)=S(d-S)/(d(d-1))`$, put

$$
\lambda_\phi=\frac{\mathbb E[G(S)e^{i\phi S}]}{\mathbb E e^{i\phi S}},
\qquad \Psi(w)=n\arg H_\phi-\nu\arg\lambda_\phi.
$$

All arguments use the branches obtained continuously from angle zero. For $`d`$ large, $`r\phi<\pi/4`$, and both positive-weight characteristic sums are in that angular sector. As $`w`$ increases from zero to infinity, $`\Psi`$ is continuous with limits $`-\nu\phi`$ and $`nr\phi=T\pi`$. The lower limit follows from the dominance of $`S=1`$ in the numerator defining $`\lambda_\phi`$, and the upper limit from $`G(r)>0`$ for $`d>r`$. Thus each internal level $`k\pi`$ has a first positive hitting point $`v_k`$, and $`v_1<\cdots<v_{D-1}`$ by continuity.

For the centered characteristic function, the imaginary part differs from zero by $`O_r(V\phi^3)`$ because the first moment vanishes and $`\mathbb E|S-\mu|^3\le r V`$. Its real part is $`1+O(V\phi^2)`$. This gives $`\arg H_\phi=\mu\phi+O_r(V\phi^3)`$. Moreover $`|\arg\lambda_\phi|\le r\phi`$. Bounded support gives $`V\le C_r\min(\mu,r-\mu)`$. Consequently, throughout the positive radius,

$$
|\Psi(w)/\pi-y|\le C_r\big(1+\min(y,T-y)/d^2\big).
\tag{1}
$$

At a crossing, (1) implies $`y=k+O(1)`$ if $`k=O(d)`$ or $`T-k=O(d)`$: in the lower case bound the minimum by $`y`$, solve for $`y`$ and substitute, and at the upper end apply the same argument to $`T-y`$. If both $`k/d`$ and $`(D-k)/d`$ tend to infinity, so do $`y/d`$ and $`(T-y)/d`$, since a bounded subsequence on either side would contradict (1).

At $`k/d\to c\in(0,\infty)`$, we have $`\mu=O(b)`$ at $`v_k`$. The law of $`S`$ concentrates at zero, and the law with weights multiplied by $`G(S)`$ concentrates at one. Indeed their respective exceptional probabilities are $`O(\mu)`$ from the expansion in $`dw=O(\mu)`$ and $`G(s)/G(1)\le r`$. For a bounded integer-valued law with probability $`1-O(\mu)`$ at $`s_0`$, its characteristic argument at $`\phi`$ is $`s_0\phi+O_r(\mu\phi)`$ by centering at $`s_0`$. Hence $`\arg\lambda_\phi=\phi+O_r(\mu\phi)`$. Also $`nV\phi^3=O(k/d^2)=o(1)`$ at the crossing. Therefore $`y(v_k)=k+1/2+o(1)`$. At $`(D-k)/d\to c\in(0,\infty)`$ we have $`r-\mu=O(b)`$, and both laws concentrate at $`r`$ with exceptional probability $`O_r(r-\mu)`$, since $`G(s)/G(r)`$ is bounded. This gives $`\arg\lambda_\phi=O_r((r-\mu)\phi)`$ and $`nV\phi^3=O((T-k)/d^2)=o(1)`$. Thus $`y(v_k)=k+o(1)`$ there. The tilt satisfies

$$
\frac{\mathrm d}{\mathrm dx}\big(d\log w_x\big)=\frac{b}{V_x},
$$

and the endpoint expansions $`V_x\sim dx/n`$ at the lower end and $`V_x\sim d(T-x)/n`$ at the upper end give

$$
d\log v_k=d\log w_k+\frac{d}{2k}+o(1)\quad(k/d\to c),
\qquad d\log v_k=d\log w_k+o(1)\quad((D-k)/d\to c).
\tag{2}
$$

These expansions of $`V_x`$ hold on bounded translates of $`k`$ by expanding the finite size weights in $`dw_x`$ or its reciprocal. In particular $`b/V_x\to1/c`$ on either window.

## Alternation near each end

Write $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$ and $`\Gamma_k=a_k^2/(a_{k-1}a_{k+1})`$. The normalized orientation inequality implies strict log-concavity at every internal quota and $`\Gamma_k\ge(1+1/k)^d`$. On $`k/d\to0`$ this tends to infinity, including bounded $`k`$. On $`(D-k)/d\to0`$ the scalar deficit curvature and the uniform column-balance local limit prove $`\Gamma_k\to\infty`$. In either event $`(-1)^kP(-t_k)>0`$ eventually. To see this, divide by $`a_kt_k^k`$ and multiply by $`(-1)^k`$. The two immediate neighbors have magnitude $`1/\sqrt{\Gamma_k}`$, and each of the two remaining alternating tails begins with a positive term and has decreasing magnitudes by log-concavity. The resulting lower bound is $`1-2/\sqrt{\Gamma_k}`$. [Upper endpoint](fixed-cap-upper-quota.md) · [Fixed-profile estimate](fixed-profile-balance-llclt.md)

At $`k/d\to c\in(0,\infty)`$ or $`(D-k)/d\to c\in(0,\infty)`$, the endpoint coefficient estimates give $`\log\Gamma_{k+j}\to1/c`$ for every fixed integer $`j`$. They also give $`\log t_k=d\log v_k+o(1)`$ by (2). At any radius $`x`$ with $`\log(x/t_k)=o(1)`$, the ratios $`a_{k+j}x^j/a_k`$ tend to $`\exp(-j^2/(2c))`$. This follows by multiplying consecutive term ratios starting from the two neighbors at $`t_k`$. For any fixed large $`L`$, the outward consecutive ratios beyond distance $`L`$ are bounded by a constant $`<1`$ uniformly along the sequence, by log-concavity and the limit at $`L`$. The two sums beyond $`L`$ are therefore bounded by a constant times the boundary terms, which converge to $`e^{-L^2/(2c)}`$. Extending missing terms by zero and sending $`L`$ to infinity yields

$$
\frac{(-1)^kP(-x)}{a_kx^k}
\longrightarrow \sum_{j\in\mathbb Z}(-1)^j e^{-j^2/(2c)}
=\sqrt{2\pi c}\sum_{m\in\mathbb Z}e^{-2\pi^2c(m+1/2)^2}>0 .
$$

The equality is Gaussian Poisson summation. This proves the sign at both $`x=t_k`$ and $`x=v_k^d`$. [Lower-end coefficients](balanced-fixed-rank-lower-edge.md) · [Upper-end coefficients](fixed-cap-upper-quota.md)

## Alternation between the two ends

Give the torus $`|z_j|=1`$, $`\prod_j z_j=-1`$ its normalized Haar measure. For $`R_w(z)=\sum_{|A|\le r} w^{|A|}\prod_{j\in A} z_j`$,

$$
P(-w^d)=\int R_w(z)^n\thinspace d\mathrm{Haar}(z).
$$

Indeed all exponents must agree to survive averaging the first $`d-1`$ independent circle variables. The product constraint then gives $`(-1)^k`$ at quota $`k`$. At $`w=v_k`$ with $`k/d,(D-k)/d\to\infty`$, (1) implies $`n\mu/d^2,n(r-\mu)/d^2\to\infty`$. Global localization gives an absolute error $`o(|H_\phi|^nI_0)`$ away from the two constant-phase neighborhoods. There $`I_0=(2\pi)^{-(d-1)}d^{-1/2}(2\pi/(n\lambda_0))^{\nu}`$ with $`\lambda_0=\mathbb E G(S)`$. For the common-arc tolerance $`\eta`$ in the localization estimate, choose the fixed centered hyperplane cube with coordinate deviations at most $`\eta/2`$, reducing its radius further if needed for the local expansion. Every pair of coordinates then differs by at most $`\eta`$, placing the entire cube in the corresponding principal chart. Its complement inside the short-arc cluster has negligible mass by the coordinate tail bound. The local transverse Gaussian evaluation on that cube gives the two conjugate terms, whose sum is

$$
2 |H_\phi|^n I_0 (\lambda_0/|\lambda_\phi|)^\nu
\big(\cos\Psi(w)+o(1)\big).
$$

Here $`|\lambda_\phi|/\lambda_0=1+O_r(\phi^2)`$ since $`\lambda_\phi/\lambda_0`$ is the ratio of characteristic functions of two bounded-support laws at $`\phi`$. The determinant multiplier tends to one. The local term uses Euclidean hyperplane measure, whose Haar density is $`(2\pi)^{-(d-1)}/\sqrt d`$. Since $`\Psi(v_k)=k\pi`$, this yields $`(-1)^kP(-v_k^d)>0`$ eventually. [Global localization](fixed-cap-moving-u-localization.md) · [Local Gaussian proof](tall-sparse-transverse-saddle.md)

## One ordered set of test points

Use the radius $`t_k`$ when $`k\le d`$ or $`D-k\le d`$, and $`v_k^d`$ otherwise. The two edge ranges are disjoint for large $`d`$ since $`D/d\to\infty`$. The geometric radii increase strictly by log-concavity, and the phase radii increase by their first-hitting definition. At either interface the neighboring geometric radii satisfy $`\log(t_{k+1}/t_k)=(\log\Gamma_k+\log\Gamma_{k+1})/2\to1`$ because the relevant distance divided by $`d`$ tends to one. Replacing one by its phase radius changes the logarithm by $`o(1)`$ by (2) and the coefficient estimates. Thus all test radii are strictly ordered. Put zero at the left and take the right endpoint to positive infinity, with sign $`(-1)^D`$ there because the leading coefficient is positive.

If an interior sign fails along a subsequence, pass to a further subsequence on which $`k/d`$ and $`(D-k)/d`$ have limits in $`[0,\infty]`$. Their sum tends to infinity. A zero limit is in the geometric range, a positive finite limit is covered for either radius by the endpoint argument, and two infinite limits are in the phase range covered by localization. This excludes every failure. Alternating signs therefore give $`D`$ distinct negative real roots by the intermediate value theorem, exhausting the degree and proving simplicity.
