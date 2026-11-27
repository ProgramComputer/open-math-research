# Normalized long states in the finite-alphabet renewal

The proposed Wronskian lemma gives a sufficient condition for the long-state ordering step. Exact examples rule out several simpler closures, including one on actual states. The remaining one-step problem is to compare the combined new row with the updated normalized differences and the short states. Formal verification is ⬜ None. [Alexandersson’s ordered-partition conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1)

## Exact update for the first differences

Let $`A_n(t)`$ be the weight of all sequences of increasing nonempty blocks on an alphabet of size $`M`$, counted at total length $`n`$ and marking each block of length at least $`j`$. We have $`A_0=1`$ and $`A_n=0`$ for $`n<0`$. Choosing the first block gives $`A_n=\sum_{\ell=1}^M\binom{M}{\ell}t^{[\ell\ge j]} A_{n-\ell}`$ for $`n>0`$. For every fixed $`n,j`$, $`M^{-n}A_n`$ tends coefficientwise to the original ordered-partition polynomial divided by $`n!`$. An all-size real-rootedness and oriented-interlacing theorem for these rows would pass to weak interlacing of the limits.

At a state for total size $`n`$, use $`p_i=A_{n-i}`$, $`L_b=\sum_{\ell\ge j}\binom{b-1}{\ell-1}A_{n-\ell}`$, $`C_b=\binom{b-1}{j-1}`$ and $`G_b=L_b/C_b`$. Thus $`G_j=A_{n-j}`$. The binomial ratio identity gives

$$
G_b=\sum_{k\ge0}\frac{\binom{b-j}{k}}{\binom{j+k-1}{k}} A_{n-j-k},\qquad
D_b:=G_{b+1}-G_b=\sum_{k\ge1}\frac{\binom{b-j}{k-1}}{\binom{j+k-1}{k}} A_{n-j-k}.
$$

In particular each $`D_b`$ has nonnegative coefficients. Writing $`H_b=G'_b`$ for the next state, $`p=p_{j-1}`$ and $`\alpha=C_b/C_{b+1}`$, Pascal's identity and the hockey-stick sum give

$$
H_b=p+\sum_{a=j}^{b-1}w_aG_a,\qquad
w_a=C_a/C_b,\qquad
\sum_{a=j}^{b-1}w_a=(b-j)/j,\qquad
H_{b+1}=\alpha H_b+(1-\alpha)p+\alpha G_b.
$$

Unfolding $`G_a=G_j+\sum_{c<a}D_c`$ in this formula yields

$$
D'_b=\frac1jG_j+\sum_{c=j}^{b-1}\left[\frac1j+\binom{c}{j}\left(\frac1{C_b}-\frac1{C_{b+1}}\right)\right]D_c.
$$

Thus the first differences stay in the positive span of $`G_j`$ and the old differences. Chudnovsky–Seymour's positive-leading-coefficient lemma makes pairwise compatibility of these old states sufficient for compatibility of all their positive combinations. This part of the difference recurrence requires no ordering of its matrix minors. [Savage–Visontai, Lemma 2.2 and Theorem 2.3](https://arxiv.org/pdf/1208.3831#page=4)

## Conditional repair of the long-state order

Write $`f\preceq g`$ for proper interlacing position with the earlier roots at the larger moduli when degrees are equal. Use $`W(f,g)=f'g-fg'`$, which is nonpositive for this orientation. Suppose the old chain $`G_M,\ldots,G_j,p`$ is strictly in this order, its roots are simple and real, all polynomials have positive leading and nonnegative other coefficients, and $`W(D_c,p)\le0`$ on the real line for every $`c`$. Then the next long states $`H_M,\ldots,H_j`$ are pairwise ordered, strictly when $`p`$ has positive degree.

For $`a<b`$, the additional hypothesis gives $`W(G_b,p)\le W(G_a,p)\le0`$ by summing the first differences. Also $`W(G_b,G_a)\le0`$ by the old order. Consequently

$$
\begin{aligned}
W(H_{b+1},H_b)
&=\alpha\left(W(G_b,p)+\sum_{a<b}w_aW(G_b,G_a)\right)
 -(1-\alpha)\sum_{a<b}w_a W(G_a,p)\\
&\le \left(\alpha-(1-\alpha)\sum_{a<b}w_a\right)W(G_b,p)
 =\frac1j W(G_b,p).
\end{aligned}
$$

Indeed $`\alpha=(b-j+1)/b`$. At every root of $`p`$ all participating $`G_a`$ have the nonzero sign of $`p'`$. Thus each $`H_b`$ is simple by the $`\deg p`$ separate sign brackets, or is $`p`$ itself when the sum is empty. The strict old pair $`G_b,p`$ has $`W(G_b,p)<0`$ everywhere when $`p`$ has positive degree, from the positive simple residues of $`G_b/p`$. At each root of $`H_b`$ the displayed strict Wronskian sign gives the nonzero sign of $`H_b'`$ for $`H_{b+1}`$. Both have degree $`\deg p`$, so the signs and left tail prove strict oriented alternation. If $`p`$ is constant the claim is vacuous. In the non-strict difference hypothesis, since $`\deg D_c\le\deg p`$ and $`p`$ is simple, it is sufficient to verify $`D_c(\xi)/p'(\xi)\ge0`$ at each zero $`\xi`$ of $`p`$ by partial fractions. [Brändén, interlacing-preserving matrices](https://arxiv.org/abs/1410.6601)

The same calculation handles all $`c>b`$ directly. Put $`\alpha=C_b/C_c`$ and $`v_a=C_a/C_c`$ for $`b\le a<c`$. Then $`H_c=\alpha H_b+(1-\alpha)p+\sum_{a=b}^{c-1}v_aG_a`$. Using the old order and $`W(G_a,p)\le W(G_b,p)`$ for $`a\ge b`$ gives

$$
 W(H_c,H_b)\le\left(\sum_{a=b}^{c-1}v_a-(1-\alpha)\sum_{a<b}w_a\right)W(G_b,p)
 =\frac{c-b}{j}W(G_b,p).
$$

This proves pairwise order without an assumption of transitivity. The new long states also precede every shifted short state $`p_i'=p_{i-1}`$ for $`i\ge2`$, since each input to $`H_b`$ precedes that fixed endpoint, and the comparison is preserved by positive summation of the Wronskians or the signs at its roots.

Coefficientwise monotonicity of $`G_b`$ and even the proper order of the first differences amongst themselves do not imply the new order. Already at $`j=2,M=4`$, take

$$
G_2=(t+2)(t+5),\quad G_3=(t+39/10)(t+6),\quad
G_4=(t+79/20)(t+601/100),\quad p=100(t+1)(t+4).
$$

Their root moduli verify the strict old chain. The $`G_b`$ are coefficientwise increasing and their two nonnegative linear differences have moduli $`134/29<679/120`$, in the expected direction. Yet at $`t=-4003/1000`$, one has $`H_3=-195191/2000000<0<98109/1000000=H_4`$. Since $`H_4(-3)<0<H_4(0)`$, both roots of $`H_4`$ are to the right of this cutoff. The leftmost $`H_3`$ root is to its left, reversing the desired order. The case $`M=j+2`$ is the smallest alphabet enlargement permitting failure of a long–long comparison. For $`M=j+1`$ the only comparison is between $`p`$ and a positive combination of $`p`$ with $`G_j`$.

## Obstruction at the newest short state

The new last row has the form $`A_n=P+tQ`$, where $`P=\sum_{1\le i<j}\binom Mi p_i`$ and $`Q=\sum_b L_b`$. A termwise compatibility proof would try to put $`tQ`$ and every $`D'_b`$ in one compatible cone. It already fails on actual states at $`(j,M,n,b)=(2,5,4,4)`$. The original recurrence gives

$$
A_1=5,\quad A_2=25+10t,\quad A_3=125+110t,\quad A_4=625+855t+100t^2.
$$

Hence $`Q=305+100t`$, and the two adjacent long states at size 5 give $`12D'_4=3L_5-4L_4=193+60t`$. The positive combination

$$
tQ+60D'_4=965+605t+100t^2
$$

has discriminant $`-19975`$. This is minimal in old size and then alphabet size for this incompatibility. Below size 4 both $`Q`$ and every $`D'_b`$ are constant whenever the latter is defined, and at size 4 only $`j=2`$ can give a nonconstant $`Q`$. There is no difference when $`M=2`$. For $`M=3,4`$ the exact linear root moduli of each $`D'_b`$ are strictly smaller than the modulus of the root of $`Q`$, so they lie between the two roots of $`tQ`$.

Requiring every order of normalized differences in one cone with the short states also fails on actual input. At $`(j,M,n)=(2,4,5)`$ the second normalized difference starting at $`G_j`$ is $`A_{n-j-2}/\binom{j+1}{2}=4/3`$, whereas $`p_1=A_4=256+321t+36t^2`$. Adding 400 times this second difference to $`p_1`$ gives discriminant $`-10623`$. More generally, at $`n\equiv1\pmod j`$ the second difference at $`G_j`$ and $`p_1`$ have degree gap two as soon as both are nonzero.

Even if the long-state comparison is settled, the new-row comparison cannot follow from an arbitrary strictly interlacing state vector. For $`j=M=3`$ the input $`G_3=t+3`$, $`p_2=t+2`$, $`p_1=t+1`$ satisfies the entire old chain. The prescribed output is $`A_n=t^2+9t+9`$, positive at the old root $`-1`$, with both roots strictly to its left. No normalized differences exist at this alphabet size. The witness separates the newly produced row from the repaired long-state argument.

This localizes a possible induction. Require the old ordered chain, compatibility of the basis $`G_j,D_b,p_i`$, and proper position of each $`D_b`$ before every short state. All new basis elements other than $`p'_1`$ are positive combinations of the old basis, so their compatibility persists. The new differences precede the shifted short states by the same signed linearity. The first differences need no mutual direction for the next long-state lemma. The old order also puts $`Q`$ before $`P`$ by bilinearity and the signs at the simple roots of $`P`$, so $`P`$ and $`tQ`$ interlace and give reality of $`A_n`$. What remains is to put $`p'_1=A_n`$ after the updated basis in the desired proper position. Once that is done the comparison with every long state follows by positive summation, since $`G'_b=G'_j+\sum_{c<b}D'_c`$.

For an actual simple negative root $`\xi=-x`$ of an updated difference $`E=D'_b`$, the exact missing comparison is

$$
E'(\xi)A_n(\xi)=E'(\xi)P(\xi)-xE'(\xi)Q(\xi)\le0
$$

in the stated orientation. When $`E\preceq P`$, the only problematic roots have $`E'(\xi)Q(\xi)<0`$. At those roots the strict bound $`|P(\xi)|>x|Q(\xi)|`$ would supply the needed sign without splitting the two summands. The explicit actual obstruction above shows that one must retain the short summand in at least some comparisons. This bound and a comparable new-row versus short-state comparison remain open here.

## Reproduction

Run `python3 -B check-witnesses.py` beside this note. The standard-library checker reconstructs the exact actual rows and reports both negative discriminants, the exact rational separator signs, and the last-row counterexample. No novelty is claimed for the underlying Wronskian or compatibility criteria.
