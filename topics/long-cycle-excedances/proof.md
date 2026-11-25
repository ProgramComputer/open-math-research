# Extreme excedance zeros with a variable cycle-length restriction

Let $E_{n,k}(t)=\sum_h a_h(n,k)t^h$ count permutations of $[n]$ whose cycles have length at least $k$, by their number of excedances. Throughout $3\le k\le n$. An excedance is an index $i$ with $\pi(i)>i$. Write $r_{n,k,h}$ for the modulus of the $h$th nonzero zero in increasing modulus whenever this rank consists of a single simple negative root. The full conjecture asks for all zeros and consecutive interlacing at each fixed $k$. [Alexandersson’s original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsPermutations) · [Research issue](https://github.com/ProgramComputer/open-math-research/issues/4)

**Proposed theorem.** In every admissible row, the closest nonzero root is simple and negative. Its modulus strictly decreases in the next row and is smaller than the modulus of every other nonzero root of the next row. The reciprocal statement holds for the largest modulus. More generally, for each fixed $H$, all sufficiently large $n$ satisfy these conclusions about reality and simplicity for the first and last $H$ nonzero roots, uniformly over $3\le k\le n$. The first $H$ ranks obey
$$
 r_{n+1,k,h}<r_{n,k,h}<r_{n+1,k,h+1}\qquad(1\le h\le H).
$$
Uniformly in $k$, for each fixed $h$ we have $r_{n,k,h}\sim a_h(n,k)/a_{h+1}(n,k)$ and $r_{n+1,k,h}/r_{n,k,h}\to h/(h+1)$.

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
