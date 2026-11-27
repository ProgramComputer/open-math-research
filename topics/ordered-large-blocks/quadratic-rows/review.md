# Independent review of ordered large-block interlacing through the first cubic row

**Verdict.** I accept the all-threshold linear-old and quadratic-old interlacing theorems as partial results. For every integer $j\ge2$, the consecutive pairs with $j\le n\le3j-1$ have simple negative roots and strictly interleave in the direction prescribed by the source. The result includes the boundary pairs $2j-1\to2j$ and $3j-1\to3j$. The unrestricted all-size factorial-moment result used in the linear argument is also correct. This agent-assisted review found no mathematical gap in those results. Formal verification remains ⬜ None. The original conjecture includes further consecutive pairs beginning with a cubic old row. [Alexandersson's original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Linear-old proof](https://github.com/ProgramComputer/open-math-research/pull/239) · [Quadratic-old proof](https://github.com/ProgramComputer/open-math-research/pull/241)

Reviewed by Codex, acting as the independent mathematical reviewer.

## Definition and orientation

The source counts all ordered partitions of the labelled set $[n]$, weighting each by $t$ to the number of blocks of size at least $j$. Thus singleton blocks give a positive constant term and partitions with $k$ large blocks exist exactly for $0\le k\le \lfloor n/j\rfloor$. Normalization by $n!$ preserves all root statements. The source orders roots from left to right on the real line, requiring the old root first at equal degrees and the new root first at a degree increase. In increasing modulus for negative roots this means new first in both cases, and the final root at a degree increase also belongs to the new row. In increasing $y=\lambda^{j-1}(1-t)/(2j!)$, the same order applies. [SymCat interleaving definition](https://www.symmetricfunctions.com/realRootedInterlacing.htm)

## Linear argument

- I independently expanded $A=1/(2-e^z)$ at $\lambda=\log2$ using the Taylor expansion of $1-e^x$. The principal parts of $A$ and $A^2$ are $-1/(2x)$ and $1/(4x^2)-1/(4x)$. On $|z|=2$ the stated cosine and mean-value estimates give $|A|<9$, and adding the absolute principal-part bounds gives analytic remainder bounds $10$ and $100$. All other poles have modulus greater than $2$. Cauchy's bounds after scaling give $14\mu^n$ and $196\mu^r$ with $\mu=7/20$.
- In the normalized ratio comparison the pole polynomial contributes the difference $1$. Each of the four error majorants decreases with $r\ge8$ and the sum at $8$ is less than $1/10$. Independently computed Stirling-gap counts confirm the low-index ratios. The convolution with $A^{k-1}$ preserves strict growth against the fixed ratio $a_{n+1}/a_n$, since each old significant summand grows strictly and the new boundary term is nonnegative. The subsequent convolution with the marked series has lag at least $kd$, where $d$ is the smallest marked size. The transition from size $kd-1$ is strict because the first moment numerator is then born with positive coefficient.
- In the linear band, increasing $b_n/a_n$ makes the value of the new row negative at the old root. At $N=2j-1$, the first quadratic contribution is $X^2/(j!)^2$ after evaluating at $1-X$. Retaining the term of size $j$ gives the normalized difference with denominator $4A_N^\ast\lambda^{j+2}$ as stated. For $j\ge9$ this beats $a_N/(j!b_N)\le a_N/c_{j-1}$ by the claimed inequality involving $\lambda^3$. The finite first-quadratic checks cover precisely $2\le j\le8$. Positivity at zero and the leading sign at negative infinity bracket two simple roots.

## Quadratic argument

- From the marked expansion, each occurrence of $t-1$ contributes $-2j!y/\lambda^{j-1}$. In the quadratic band this gives $a-by+dy^2$ with the proposed $B_m^\ast$ and $D_s^\ast$. At $n+1=3j$ the three distinguished blocks fill the labels and all have size $j$, giving exactly $-16\lambda^4y^3$ in the normalized new row.
- Cubing the Laurent series gives the principal part $-1/(8x^3)+3/(16x^2)-1/(8x)$. The coefficient of $x^{-1}$ is $3(-1/2)(1/4)^2+3(-1/2)^2(-1/24)=-3/32-1/32=-1/8$. The principal part and $|A|<9$ give the stated analytic remainder bound $800$. Since $8(7/10)^3(800)<2200$, the normalized Cauchy error is valid. The first difference of the pole polynomial is $r+2+3\lambda/2$. Independent gap counts verify the eight low-index cases and rational bounds verify the tail margins. Summing the lower difference bound also yields $E_s^\ast\ge s^2/2$.
- The estimate $b/U\ge m$ uses the lower witness $m+1+\lambda-1/20$ for $b$, multiplied by $1-\lambda/(j+1)$. The lost amount in the witness is at most $\lambda(m+2)/(j+1)<7/5$. The crude upper bound $m+198$ follows directly from the error estimate for $C^\ast$. In the difference for $b$, the summand errors are dominated by a geometric series with ratio $\gamma/\mu$, while $u_{m+1}C_0^\ast$ and the omitted tail contribute at most $3\gamma^{m+1}/(1-\gamma)$. The extra normalization by $v$ is bounded by the $30\mu^{2j}$ estimate. In the difference for $d$, dropping the $\ell>s$ tail loses at most twice the total first moment of the $w_\ell$, and the $-\ell$ inside the retained terms costs at most one more copy. Since $\sum \ell w_\ell=2U\sum \ell u_\ell$, the claimed first-moment bound follows by summing $\ell\gamma^\ell$. The upper bound includes the boundary term since $E_0^\ast<3$. The polynomial-times-geometric bounds used here decrease beyond the claimed cutoffs.
- The difference at old roots is $y(\Delta d\,y-\Delta b)$ for a quadratic new row. The separator $y_*=\Delta b/\Delta d$ lies between the two distinct old roots exactly when $b>a/y_*+dy_*$. The bound for this last sum divided by $U$ follows since $(s+4)^2/(s+3/2)\le s+11$ for $s\ge0$. It leaves a margin strictly greater than zero at $j=32$ and greater than $j/6$ at $j\ge64$. The signs at the smaller and larger old moduli are negative and positive, respectively. The first sign is unchanged by the negative cubic perturbation. At the larger old modulus the quantitative separator margin gives $d(y_2-y_*)>jU/6$, since the margin equals $-P(y_*)/y_*=d(1-y_1/y_*)(y_2-y_*)$. The positive contribution after taking out $y_2$ is therefore greater than $U/4$. The negative perturbation is smaller than $U/4$ since $y_2<b/d<11U/j$. The last bound uses the decreasing function $2j(2j+198)/(j-1)^2$ at $j=64$. The signs at zero, both old roots, and infinity then locate three distinct negative new roots at the cubic transition.
- In the submitted finite cubic check, evaluation at either old root agrees with evaluation of the affine remainder after reduction modulo the old quadratic. Its positive slope in $x=1-t$ and a negative old value at its zero yield exactly the two required opposite signs. The stated same-degree finite range has $\sum_{j=2}^{31}(j-1)=465$ cases and the first cubic range $2\le j\le63$ has 62 cases. The analytic bounds start at $32$ and $64$, respectively.

## Reproduction

I extracted the patches in a scratch Git repository, reviewed #239 at head and merge commit 975ab362633ca90238f52af96382692af8e127c5 and #241 at head 298ffd905a1c8260ee2256786511f6e6ca899453, and ran the following with Python 3.13.5.

~~~sh
gh pr diff 239 --repo ProgramComputer/open-math-research > 239.diff
gh pr diff 241 --repo ProgramComputer/open-math-research > 241.diff
git init -q
git apply --include='topics/ordered-large-blocks/*/*' 239.diff
git apply --include='topics/ordered-large-blocks/*/*' 241.diff
for name in first-degree-increase quadratic-rows; do
  directory=topics/ordered-large-blocks/$name
  python3 -B "$directory/check.py" > "$name.out"
  diff -u "$directory/check-output.txt" "$name.out"
done
python3 -B independent.py
python3 -B constants.py
~~~

Both submitted outputs matched byte for byte. From this directory, run the [independent sign checker](independent.py) and [analytic constant checks](constants.py) with the last two commands. The companion scripts here reconstruct the coefficients using Stirling numbers for unmarked labels distributed among ordered gaps, then apply binomial inversion for the exact number of large blocks. With $p$ gaps and $h$ unordered blocks on the remaining labels, $h!\binom{h+p-1}{p-1}$ arrangements place the blocks into the gaps in order. This supplies the counts used for choosing distinguished blocks, independently of the submitted first-block recurrence. The checks agree with every sample row in SymCat for $j=3$. The script then evaluates the new polynomial in the original $t$ coordinate directly at the old rational or quadratic roots. It compares integral powers or signed rational squares and uses no numerical root estimates or affine remainders.

This independent replay covers all finite checks and includes the first threshold of each analytic range. It passed 36 linear-to-linear pairs, 8 linear-to-quadratic transitions, 496 quadratic-to-quadratic pairs, and 63 quadratic-to-cubic transitions. The independent exact analytic-constant checks also passed. This review did not formalize the argument in Lean or Rocq.
