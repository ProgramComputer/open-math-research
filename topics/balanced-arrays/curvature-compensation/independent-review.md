# Independent review of geometric-node compensation

At an internal quota $`k`$, write $`\gamma_j=a_j^2/(a_{j-1}a_{j+1})`$, $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$, and $`\tau=1/\sqrt{\gamma_k}`$. Normalize the signed value at $`-t_k`$ by the central term. Both immediate neighbors have relative magnitude $`\tau`$. Going in direction $`e\in\{-1,1\}`$, the magnitude ratio from index $`k+e`$ to $`k+2e`$ is $`\tau/\gamma_{k+e}`$, and from there to $`k+3e`$ it is $`\tau/(\gamma_{k+e}\gamma_{k+2e})`$. This follows by dividing consecutive coefficient ratios and holds in both directions. Ordinary log-concavity makes the subsequent successive magnitude ratios nonincreasing and less than one. Thus the second and third terms on each side contribute at least

$$
\frac{\tau^2}{\gamma_{k+e}}
\left(1-\frac{\tau}{\gamma_{k+e}\gamma_{k+2e}}\right)
$$

if both exist, with the loss omitted if the third does not exist. All farther terms can be paired from distances four and five onward; the pairs have nonnegative total. If the second term is missing or only its nonnegativity is known, zero is a lower bound for that side's contribution beyond the immediate neighbor.

For rigorous lower and upper curvature bounds $`L_j,U_j`$ and an upper bound $`T`$ on $`\tau`$, the displayed contribution is at least

$$
\tau^2 C_e, \qquad
C_e=\frac{1-T/(L_{k+e}L_{k+2e})}{U_{k+e}}.
$$

The loss term is omitted when the third term is absent. Here $`L_j>1`$ follows from normalized log-concavity and the binomial curvature, so the factors being bounded are positive. When $`U_{k+e}`$ is unavailable use zero. The checker uses the dyadic upper bound obtained by rounding up the integer square root of the scaled reciprocal lower curvature. In these cases $`T<1`$. For $`C=C_{-1}+C_1`$ the lower bound for the signed value is $`1-2\tau+C\tau^2`$. Its minimum on $`[0,T]`$ is the value at $`T`$ if $`CT\le1`$, and $`1-1/C`$ otherwise. This gives the exact branch in the code. If $`L_k>4`$, the immediate neighbors alone cost less than one.

Finally $`t_{k+1}/t_k=\sqrt{\gamma_k\gamma_{k+1}}>1`$. Thus alternating signed values at all internal geometric nodes, together with the endpoint signs at zero and negative infinity, yield the full degree in distinct simple negative roots. Both coefficient probability estimates used by the script are justified. The lower estimate is the union bound, and the upper estimate follows from negative association of the independently concatenated uniform column subset indicators, applied to the decreasing cap tests on disjoint row supports.

## Independent coefficient and sign certificate for the corank-two cases

An exact inclusion–exclusion computes the coefficients without summing all arrays. If $`\ell`$ specified rows exceed cap $`d-2`$, each is missing from at most one column. Suppose $`h`$ rows are actually missing from some column. Choose the $`h`$ labels, then partition those labels into buckets for the $`d`$ columns. A bucket of $`b`$ omitted labels contributes
$`\binom{n-\ell}{k-\ell+b}`$ choices for the unrestricted rows of that column. If $`V_j(h)`$ counts assignments of $`h`$ named missing rows to the first $`j`$ columns with these column weights, then

$$
V_{j+1}(h)=\sum_{b=0}^h\binom hb\binom{n-\ell}{k-\ell+b}V_j(h-b),
\qquad V_0(h)=\mathbf1_{h=0}.
$$

The joint bad-row count is $`\sum_h\binom\ell h V_d(h)`$, and the alternating inclusion–exclusion weight is $`(-1)^\ell\binom n\ell`$. Values $`\ell>d k/(d-1)`$ are impossible. This requires only univariate integer convolutions.

The independent standard-library checker rounds every geometric node down to a rational point with denominator $`2^{256}`$, checks the ordering afresh, and uses exact rational Horner evaluation to check its sign. Thus no estimate of the rounding error or geometric compensation lemma is needed for the finite certificates. It proves 30 simple negative roots for $`(n,r,d)=(36,10,12)`$ and 29 for $`(36,9,11)`$. The two runs took about 0.15 seconds total. The first case also has a completely coefficient-free certificate from the compensation checker and one-row probability bounds.

For completeness, testing direct center signs with only the union and singleton negative-association bounds gives positive interval lower bounds at $`k=13`$ through $`20`$ in the first case. Using all the three-row bounds extends this through $`22`$ but does not certify $`23`$ by direct interval summation at the midpoint-coefficient probe. The compensation lemma avoids the loss from assigning independently adversarial signs to distant unknown coefficients.

## Direct finite certificate from four joint failure moments

The additional `independent-probes.py` avoids whole-array counts and the compensation lemma. It computes just the first four bad-row intersection probabilities from the corank-two convolution, with $`\ell\le4`$. Alternating inclusion–exclusion partial sums bound every cap-valid probability by Bonferroni. At each central index $`14\le k\le22`$ it uses a dyadic approximation to the geometric node formed from interval midpoint coefficients, then checks the signed value strictly by using coefficient lower bounds at positive terms and upper bounds at negative terms. Outside the central window the binomial curvature alone exceeds four. Exact rational comparisons place the first central probe after the geometric node at $`k=13`$ and the last central probe before the geometric node at $`k=23`$. These comparisons use the upper and lower possible squared geometric node bounds. The two joins and all nine direct signs pass, proving the full negative root count for $`(36,10,12)`$. Neither the negative-association upper bound nor the exact cap-valid coefficients enter this certificate.

## Adjacent corank-three cases

An excluded row for cap $`d-3`$ can omit up to two columns. For fixed $`\ell`$ excluded labels, count assignments column by column and keep the histogram of zero, one and two omissions so far. A column can omit $`a`$ previously unused labels and $`b`$ labels with one prior omission. Multiply by the two binomial choices within those classes and by the unrestricted-column weight $`\binom{n-\ell}{k-\ell+a+b}`$. This two-coordinate state distribution implements exact labeled counting. The same inclusion–exclusion and dyadic Horner checks give 26 simple negative roots for $`(36,8,11)`$ and 27 for $`(36,9,12)`$ in a few seconds each. Both counters also agreed with direct labeled-row enumeration on all 15 nonzero-cap cases with $`2 \le n \le4`$, $`3 \le d \le5`$ and corank two or three. The histogram becomes larger for lower caps, beyond this check.

Run from this directory:

```sh
python3 -B independent-probes.py
python3 -B independent-count.py
python3 -B independent-near-full.py
```

## Coverage of the partial replay

The published finite reduction leaves 28 row-36 candidates beyond the analytic, degree and subfamily criteria. The earlier partial local replay supplied 19 coefficient vectors, each rechecked for positive coefficients and a full distinct real-root count. The separate corank-two checker supplies the case $`(36,9,11)`$. Exactly eight cases then remain in this checkpoint, five recorded in this package and three at 12 columns and caps five through seven. The earlier published universal range is still through 35 rows.

**Signed** · four_central, independent agent-assisted review.
