# Extreme excedance zeros with a variable cycle-length restriction

Let $E_{n,k}(t)=\sum_h a_h(n,k)t^h$ count permutations of $[n]$ whose cycles have length at least $k$, by their number of excedances. Throughout $3\le k\le n$. An excedance is an index $i$ with $\pi(i)>i$. Write $r_{n,k,h}$ for the modulus of the $h$th nonzero zero in increasing modulus whenever this rank consists of a single simple negative root. The full conjecture asks for all zeros and consecutive interlacing at each fixed $k$. [Alexandersson’s original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsPermutations) · [Research issue](https://github.com/ProgramComputer/open-math-research/issues/4)

**Proposed theorem.** In every admissible row, the closest nonzero root is simple and negative. Its modulus strictly decreases in the next row and is smaller than the modulus of every other nonzero root of the next row. The reciprocal statement holds for the largest modulus. More generally, for each fixed $H$, all sufficiently large $n$ satisfy these conclusions about reality and simplicity for the first and last $H$ nonzero roots, uniformly over $3\le k\le n$. The first $H$ ranks obey
$$
 r_{n+1,k,h}<r_{n,k,h}<r_{n+1,k,h+1}\qquad(1\le h\le H).
$$
Uniformly in $k$, for each fixed $h$ we have $r_{n,k,h}\sim a_h(n,k)/a_{h+1}(n,k)$ and $r_{n+1,k,h}/r_{n,k,h}\to h/(h+1)$.

In fact the number of ranks can grow with $n$: the final section proves these conclusions simultaneously up to $\lfloor\tfrac14\sqrt{n/\log n}\rfloor$ at each end, uniformly in $k$.

## Encoding the coefficients by decreasing runs

Cut every cycle immediately after the source of each ascent in its cyclic list of labels. An ascent is exactly an excedance. Since cycles have distinct labels and length at least two, each has at least one ascent. The cuts give $h$ nonempty strictly decreasing runs. Temporarily label them by $[h]$. The data are then a word $w$ indexed by the original labels, with $w(i)$ the run containing $i$, and a permutation $\sigma$ of the runs describing their cyclic succession. Conversely sort each color class in decreasing order. The word and permutation specify precisely one admissible permutation with the prescribed cuts when all classes are nonempty, each boundary goes upwards from the minimum of its departing class to the maximum of its successor, and the sum of the class sizes on every cycle of $\sigma$ is at least $k$. There are $h!$ labellings for each original permutation. Thus
$$
 a_h/h^n=\Pr(\text{all three conditions}),
$$
for independent uniform $\sigma\in S_h$ and $w\in[h]^n$. In particular $a_h\le h^n$ and $a_1=1$. Inversion preserves the cycle lengths and exchanges excedances and deficiencies, so $a_h=a_{n-h}$ and $E_{n,k}(t)/t$ has degree $n-2$, constant and leading coefficients one, and reciprocal nonzero zeros.

## A certificate in every row

A permutation with two excedances has one or two cycles. For one cycle the two run labels must be exchanged. Of the $2^n$ colorings, two omit a color, and $2(n-1)$ have a nonempty initial segment in one color and the complementary final segment in the other; these are precisely the nonempty colorings with a failed upward boundary. Divide by two for the labelling. For two cycles the run permutation is the identity, and both color classes must have size at least $k$. Consequently
$$
 A_n:=a_2(n,k)=2^{n-1}-n+\frac12\sum_{\ell=k}^{n-k}\binom n\ell .
$$
At fixed $k$, every accepted coloring in the sum permits the additional label to take either color. Therefore $A_{n+1}\ge2A_n$ for $n\ge3$. Also $A_n\le 2^n$ and $A_n\ge(7/16)2^n$ for $n\ge32$, since $n/2^n$ decreases there.

Set $z=A_nt$ and divide $E_{n,k}(t)$ by $t$. On $|z|\le6$ this polynomial differs from $1+z$ in modulus by at most
$$
 \sum_{p\ge3}18^{p-1}(p/2^{p-1})^n
 \le\frac{18^2(3/4)^n}{1-18(2/3)^n}<\frac18
 \qquad(n\ge32).
$$
Here $1/A_n\le3/2^n$ and the ratio of adjacent bounds uses $(p+1)/(2p)\le2/3$. The final rational inequality follows at $n=32$ by clearing denominators, and the bound decreases. By Rouché on $|z+1|=1/8$ and on $|z|=6$ there is exactly one root in the former disk and no additional root in the latter. It is simple and negative by conjugation. Its modulus in $t$ is between $7/(8A_n)$ and $9/(8A_n)$, and every other modulus exceeds $6/A_n$. For consecutive rows $2\le A_{n+1}/A_n\le32/7$. These bounds put the old first root strictly between the new first root and every other new nonzero-root modulus.

For $3\le k\le n\le32$, the [exact archive](prefix.jsonl.gz) supplies all 465 coefficient vectors. The [standard-library verifier](verify.py) constructs them by choosing the cycle containing label one, of length $s$ and weight $t A_{s-1}(t)$, where $A_m(t)$ is the ordinary Eulerian descent polynomial. To see this weight, begin a cycle with its largest label; the last element contributes one ascent back to that label, and the remaining interior ascents have the Eulerian distribution. An independent check deletes the maximum from its cycle, using the author's recurrence
$$
 E_{n+1,k}=nt E_{n,k}+t(1-t)E'_{n,k}+\binom n{k-1}tA_{k-1}(t)E_{n+1-k,k}.
$$
For $n>0$ the rows below $k$ are zero; the empty row is one. The term with binomial coefficient counts when the maximum was in a cycle of length exactly $k$. In the remaining case, inserting it after any label replaces one edge by an ascent and a descent, leaving the old number of ascents unchanged on the old ascending edges and increasing it by one on the others. [Author’s recurrence and prior checks](https://github.com/PerAlexandersson/RealRooted/issues/2590#issuecomment-7059794955)

The verifier divides out $t$. For each row and its derivative, and for each of the 435 consecutive pairs from the same threshold, the signed Euclidean remainder chain has positive leading coefficients and drops exactly one degree per step down to degree zero. These conditions certify strict interlacing: starting at the last constant and linear polynomial, the relation $P=S Q-cR$ with $c>0$ fixes the signs of $P$ at the roots of $Q$, and the signs at the two infinities supply the outer roots. Induction exhausts the degree and gives simplicity. Positive coefficients exclude nonnegative roots. Thus the finite and analytic arguments overlap.

## Uniform control at an arbitrary fixed rank

Fix $h$. With probability $1-O_h((1-1/h)^{\lfloor n/2\rfloor})$ every color occurs both in the lower and upper halves of $[n]$ (for $h=1$ the condition holds at $n\ge2$). Then all upward boundary conditions hold regardless of $\sigma$. Write $p_{n,h,k}$ for the probability of the cycle-size constraints alone. As a proportion $1/h$ of the permutations of runs are single cycles and $k\le n$,
$$
 a_h(n,k)/h^n=p_{n,h,k}+O_h((1-1/h)^{\lfloor n/2\rfloor}),\qquad p_{n,h,k}\ge1/h.
$$
Couple row $n+1$ to row $n$ by appending one independent uniform color. For a fixed $\sigma$, a proper cycle with $s$ colors can change the truth of the length constraint only if its previous size was $k-1$. This size is binomial with parameters $n,s/h$, and its largest point probability is $O_h(n^{-1/2})$ by Stirling's formula at a mode. A single cycle containing all colors meets the constraint in both rows. The union bound gives $|p_{n+1,h,k}-p_{n,h,k}|=O_h(n^{-1/2})$ for every $k\le n$. Thus $a_h(n+1,k)/a_h(n,k)=h(1+O_h(n^{-1/2}))$.

For a fixed $h$ let $u=a_h/a_{h+1}$ and $b=h/(h+1)$. The probability estimates imply $c_h b^n\le u\le C_h b^n$ with positive constants independent of $k$. On compact complex annuli the scaled Laurent polynomial
$$
 \frac{E_{n,k}(u z)}{a_h(uz)^h}=1+z+o_h(1)
$$
converges uniformly, also over $k$. For $p<h$, each term is bounded on the annulus by a constant times $[(p/h)b^{p-h}]^n$, with bracket strictly below one because the sequence $p b^p$ increases strictly up to $h$ and has its two equal maxima at $h,h+1$. For $p\ge h+2$, the first term has exponential base $(h+2)h/(h+1)^2<1$. Successive terms in the upper bound formed with $a_p\le p^n$ have ratio at most a fixed constant times $[(h+3)h/((h+2)(h+1))]^n$ there. This geometric tail vanishes uniformly.

For $0<\epsilon<1/2$, use the circles $|z|=1-\epsilon$, $|z|=1+\epsilon$ and $|z+1|=\epsilon/2$. After multiplication by $z^{h-1}$ the expression is a polynomial proportional to $E_{n,k}(uz)/z$. Rouché's theorem gives $h-1$ zeros on the inside of the first circle, $h$ on the inside of the second, and exactly one in the disk about $-1$. The latter is simple negative. This identifies the rank by modulus and proves $r_{n,k,h}/u\to1$. The formula for consecutive coefficients shows that $u(n+1,k)/u(n,k)\to h/(h+1)$. The $(h+1)$st root of the next row is exponentially farther than the $h$th of the old, since $(h+1)/(h+2)>h/(h+1)$. Inversion supplies the outer ranks. Taking the maximum of the finitely many cutoffs for $h\le H+1$ completes the proof.

The encoding also gives the leading coefficient constant off its transition values. If $h$ is fixed, $k/n\to\lambda$ in $(0,1)$ and $\lambda h$ is not integral, the weak law of large numbers on each of the finitely many run cycles gives
$$
 \lim a_h(n,k)/h^n=\Pr_{\sigma\in S_h}\{\text{every cycle of }\sigma\text{ has length }>\lambda h\}.
$$
For example, the same exponential scale can have different leading constants as the minimum allowed cycle length varies with $n$.

## A growing number of extreme ranks

**Quantitative strengthening.** For all sufficiently large $n$, uniformly in $3\le k\le n$, all the preceding strict root and order conclusions hold simultaneously for
$$
 1\le h\le H_n=\left\lfloor\frac14\sqrt{\frac{n}{\log n}}\right\rfloor .
$$
We track the coefficients at $h\le H_n+2$, also at row $n+1$. Write $p=p_{n,h,k}$ as above. The case $h=1$ satisfies all probability estimates directly. The constants below are absolute.

We first bound $p$ below. If $k\le n/2$, put $L=\lceil2hk/n\rceil$. A uniform permutation of $u$ elements has all cycles of length at least $L$ with probability $d(u,L)\ge1/(2L)$ for every $u\ge L$. Indeed the cycle of the first element has uniform length, so $u d(u,L)=\sum_{s=L}^u d(u-s,L)$. The term $d(0,L)=1$ suffices for $L\le u<2L$. For $u\ge2L$, induction adds at least $(u-2L+1)/(2L)$. Condition on this event at $u=h$. Each cycle then has a binomial number of assigned labels of mean at least $2k$ and at least $n/h$. The probability this number is less than $k$ is at most $e^{-n/(8h)}$ by the binomial half-mean bound. A union bound over the cycles costs at most $h e^{-n/(8h)}=o(1)$. For $k>n/2$, a single cycle of the run permutation always meets the constraint. These cases prove
$$
 p_{n,h,k}\ge c/(1+hk/n)
$$
for an absolute constant $c>0$.

In the consecutive-row coupling the new letter must land in a cycle that had size exactly $k-1$. The expected number of $s$-cycles in a uniform permutation of $h$ elements is $1/s$, by choosing their labels, cyclic order and the remaining permutation. Such a cycle receives the new letter with probability $s/h$. The all-color cycle always satisfies the lower bound for $k\le n$. Thus
$$
 0\le p_{n+1,h,k}-p_{n,h,k}
 \le\frac1h\sum_{s=1}^{h-1} b(s/h),\qquad
 b(x)=\binom n{k-1}x^{k-1}(1-x)^{n-k+1}.
$$
This kernel increases up to $(k-1)/n$ and decreases thereafter. Its sum on the interior grid, divided by $h$, is bounded by its integral plus $h^{-1}\max_{1\le s<h} b(s/h)$. To see this, omit the largest sample and charge every other sample to its adjacent interval toward that maximum; by unimodality the kernel there is at least the smaller endpoint value. The intervals have disjoint interiors. The beta integral is $1/(n+1)$.

There are two useful bounds on the sampled maximum. For a binomial variable with parameter $x=s/h$, its largest point probability is at most $C/\sqrt{n x(1-x)}\le C'\sqrt{h/n}$. This follows by Stirling's bounds at a binomial mode; here $n/h\to\infty$ uniformly. When $k\le(n+1)/2$ the continuous maximum at $x=(k-1)/n$ is at most $C''/\sqrt{k}$ by the same bounds. Using the first estimate for the constant term in $1+hk/n$ and the second for $hk/n$ gives
$$
 \frac{p_{n+1,h,k}-p_{n,h,k}}{p_{n,h,k}}
 =O\left(\frac{1+h}{n}+\frac1{\sqrt{nh}}+\frac{\sqrt{k}}n\right)
 =O(h/n+n^{-1/2}).
$$
If $k>(n+1)/2$, the size constraints force a single cycle of $\sigma$ in both rows, so both probabilities are $1/h$. The discarded empty-color and failed-boundary probabilities are at most $2h\exp(-\lfloor n/2\rfloor/h)$. Even after division by $p\ge c/(1+h)$ these are smaller than $1/n$ uniformly in our range. In particular, with $u_{n,h}=a_h/a_{h+1}$ and $b_h=h/(h+1)$,
$$
 \frac{u_{n+1,h}}{u_{n,h}}=b_h\bigl(1+O(h/n+n^{-1/2})\bigr).
$$

It remains to bound the two-term approximation on the scale of the gap $1/h$. Let $H=H_n+2$. For $h\le H$ the single-cycle lower bound gives $h^n/(2h)\le a_h\le h^n$ for all sufficiently large $n$. For $h<H$ this gives $b_h^n/(2h)\le u_{n,h}\le 2(h+1)b_h^n$. In the annulus $1/2\le|z|\le2$, bound terms left of $h$ in the normalized Laurent polynomial starting at $h$ and moving down. Their upper bounds have successive ratios at most
$$
 4h\bigl[(h-1)(h+1)/h^2\bigr]^n\le4h e^{-n/h^2},
$$
starting with an envelope of $2h$ at index $h$. For terms right of $h+1$ start instead at $h+1$ with envelope $2(h+1)|z|$ and move up, using $a_p\le p^n$ also far outside the range of the lower bound. The ratios are at most
$$
 4(h+1)\bigl[(h+2)h/(h+1)^2\bigr]^n
 \le4(h+1)e^{-n/(h+1)^2}.
$$
Consequently the annular error is $O((H+1)^2 e^{-n/(H+1)^2})=o(1/H)$; for example $n/(H+1)^2\ge8\log n$ for all sufficiently large $n$. The same estimates apply at $n+1$ with the old cutoff. Apply the three-circle count above with $\epsilon=H^{-2}$, which dominates the error. It gives $r_{n,k,h}/u_{n,h}=1+o(1/H)$ uniformly. Since $H(h/n+n^{-1/2})\to0$ uniformly, the consecutive ratio is $b_h(1+o(1/H))<1$.

Finally, the lower bound on $u_{n+1,h+1}$ and upper bound on $u_{n,h}$ give
$$
 \frac{u_{n+1,h+1}}{u_{n,h}}\ge
 \frac{b_{h+1}}{4(h+1)^2}
 \left(1-\frac1{(h+1)^2}\right)^{-n}.
$$
This tends to infinity uniformly for $h\le H_n$. It supplies the other consecutive inequality and completes the growing-rank proof. The estimates control a sublinear number of roots; the central ranks remain open.
