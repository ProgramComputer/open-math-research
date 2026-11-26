# Adding a column can fail to preserve real-rootedness by a diagonal multiplier

Let $a_{n,k}^{(r,d)}$ count labeled $n\times d$ binary arrays with every column sum equal to $k$ and every row sum at most $r$. Fix $n,r,d$ with $1\le r\le d$ and put $m=\lfloor nr/d\rfloor$. The coefficientwise map taking the balanced-array polynomial for $d$ columns to the polynomial for $d+1$ columns multiplies coefficient $k$ by $a_{n,k}^{(r,d+1)}/a_{n,k}^{(r,d)}$. Its degree-$m$ symbol is
$$
S_{n,r,d}(x)=\sum_{k=0}^{\lfloor nr/(d+1)\rfloor}
\binom{m}{k}\frac{a_{n,k}^{(r,d+1)}}{a_{n,k}^{(r,d)}}x^k.
$$
This is the image of $(1+x)^m$. A nonreal zero of the symbol therefore rules out preservation of real-rootedness even on inputs with only negative zeros.

**Theorem.** For $(n,r,d)=(7,6t,7t)$ the symbol is real-rooted for $1\le t\le14$ and has a nonreal conjugate pair for every integer $t\ge15$. This obstructs the column-addition multiplier method. The individual array polynomials in this comparison have degrees six and five and lie within the repository's [verified degree range](low-degree.md).

## Proof of the infinite family

The degree bounds are $6$ and $5$. For the first, quota six is attained by using each six-element column support exactly $t$ times. For the second, use the complements of the seven adjacent pairs of a seven-cycle as column supports, repeat the block $t$ times, and add any column of quota five. Each row then has at most $5t+1\le6t$ ones. Removing entries in each column gives feasible arrays at each lower quota.

For quota $0\le k\le5$, choose each column independently and uniformly from the $k$-subsets of the seven rows. Let $p_-$ and $p_+$ denote the probabilities of satisfying the cap for $7t$ and $7t+1$ columns, respectively. Under deletion of the last column, $p_+\le p_-$. For the new array each row count $X$ is binomial with $7t+1$ trials and success probability $k/7\le5/7$. Applying Markov's inequality to $2^X$ and taking a union bound over seven rows gives
$$
p_-\ge p_+\ge 1-\varepsilon_t,\qquad
\varepsilon_t=7\frac{(12/7)^{7t+1}}{2^{6t+1}}
=6\left(\frac{559872}{823543}\right)^t.
$$

An old feasible array can lose feasibility only if the new column hits a row whose old count is exactly $6t$. The saturation probability for a given row is $\binom{7t}{t}(k/7)^{6t}((7-k)/7)^t$. Its new-column hit probability is independently $k/7$. The union bound over the seven rows gives
$$
p_--p_+\le q_{k,t}
=k\binom{7t}{t}(k/7)^{6t}((7-k)/7)^t.
$$
For $1\le k\le5$, the ratio of successive terms $q_{k,t+1}/q_{k,t}$ is bounded by $(k/6)^6(7-k)\le2(5/6)^6<1$. Indeed,
$$
\frac{\binom{7t+7}{t+1}}{\binom{7t}{t}}
=7\prod_{i=1}^6\frac{7t+i}{6t+i}\le7(7/6)^6,
$$
and $k^6(7-k)$ increases on $[0,5]$. For $k=0$ the loss is zero. Since $\varepsilon_t$ decreases, the bound $q_{k,t}/(1-\varepsilon_t)$ on $1-p_+/p_-$ is at most its value at $t=15$ for every $t\ge15$.

The number of unconstrained arrays increases by $\binom7k$ on adding one column. Hence the coefficient of $x^{5-k}$ in $F_t(x)=x^5 S_{7,6t,7t}(1/x)$ equals $\binom6k\binom7k p_+/p_-$. Set
$$
F(x)=126+525x+700x^2+315x^3+42x^4+x^5,
\qquad
E(x)=\sum_{k=0}^5\binom6k\binom7k\frac{q_{k,15}}{1-\varepsilon_{15}}x^{5-k}.
$$
At $z=57/100$, the triangle inequality gives $|F_t^{(i)}(-z)-F^{(i)}(-z)|\le E^{(i)}(z)$ for $0\le i\le2$. Exact rational substitution gives
$$
\begin{aligned}
F(-z)&>E(z),\
F''(-z)&>E''(z),\
(|F'(-z)|+E'(z))^2&<(F(-z)-E(z))(F''(-z)-E''(z)).
\end{aligned}
$$
These three inequalities are checked directly by [the verifier](code/verify_column_extension.py). They imply $(F_t'(-z))^2-F_t(-z)F_t''(-z)<0$. A real-rooted polynomial satisfies the opposite inequality at every real point, as follows by differentiating its logarithmic derivative off its roots and then using continuity. Taking reciprocals preserves nonreal zeros, so the original symbol has a nonreal conjugate pair.

## A failure in the corank-two transition

At $(n,r,d)=(36,5,6)$ the coefficient multiplier sends $(1+x)^{30}$ to a degree-$25$ polynomial $S$ with exactly $23$ distinct real roots and one nonreal conjugate pair. Each of the two actual balanced-array polynomials has its full degree of simple negative roots. This example falls outside the published through-degree-$14$ and through-row-$24$ reductions. The known uniform coefficient-separation estimate for the seven-column row at its middle index is $(19/18)^{14}<4$.

Here is an independent way to count the seven-column row and reproduce the certificate. More generally, let $D$ denote the new dimension and impose cap $D-2$. Mark $j$ rows violating the cap, so each has at most one zero. For column $i$, let $h_i$ count its zeros among the marked rows. The sets of these zeros are disjoint. If $H=\sum_i h_i\le j$, there are $(j)_H/\prod_i h_i!$ ways to place them, where $(j)_H$ is the falling factorial. Column $i$ then requires $k-j+h_i$ ones in the remaining $n-j$ rows. With binomial coefficients outside their support interpreted as zero, put
$$
B_j(z)=\sum_{h=0}^j \binom{n-j}{k-j+h}\frac{z^h}{h!}.
$$
Inclusion–exclusion gives the labeled-array count
$$
a_{n,k}^{(D-2,D)}=
\sum_{j=0}^{\min(n,\lfloor Dk/(D-1)\rfloor)}
(-1)^j\binom nj\sum_{H=0}^j (j)_H [z^H] B_j(z)^D .
$$
The bound on $j$ follows because the marked rows use at least $j(D-1)$ ones. The checker evaluates the inner sum by clearing the factor $(j!)^D$. In a second count, append one column of $n-k$ zeros at a time and track the numbers of rows still needing one or two zeros. A transition chooses the next column's zeros among these two sets and the already satisfied rows, with the three corresponding binomial multiplicities.

Form $T(x)=x^{25}S(1/x)$ from the two integer coefficient vectors. The exact check gives
$$
T'(-13/4)^2 - T(-13/4)T''(-13/4)<0 .
$$
This single rational inequality certifies the failure of the multiplier. The checker also counts the real roots of the actual array polynomials and the symbol by Sturm's theorem. The archive stores complete input coefficients and exact Sturm reports for the 46 transitions with $n\in\{16,24,30,36,48,60,72\}$, $d\in\{4,5,6,8,10,14,18,24\}$ and $2d\le n$. Exactly 29 of those 46 symbols have a nonreal zero. [Archive](results/column-extension-corank-two.jsonl.gz) · [Verifier](code/verify_corank_two_symbol.py)

~~~sh
python topics/balanced-arrays/code/verify_corank_two_symbol.py --recount
~~~

For the same fixed column increment $6\to7$ at cap five, a moment determinant proves that the symbol has a nonreal zero for every sufficiently large row count. The proof gives an existential cutoff. Two independent interval calculations verify the determinant. [Proof and verifier](column-extension-asymptotic.md) · [Independent review](review-column-extension-asymptotic.md)

## A test using the spacing of the input roots

For $b>1$, let $G_{m,b}(x)=\prod_{j=0}^{m-1}(1+b^jx)$. Replace $(1+x)^m$ by $G_{m,b}$ as the test input to the same coefficient multiplier. Lamprecht's convolution theorem applies when both this modified symbol and the actual input have negative roots, and successive root moduli in each are separated by a factor of at least $b$. In that case the output also has this property. After reflecting the positive-root convention by $x\mapsto -x$, the convolution on polynomials of degree at most $m$ divides the coefficient product by the corresponding coefficient of $G_{m,b}$, which gives exactly the original coefficient multiplier. [Lamprecht, Theorem 3](https://arxiv.org/abs/1210.1102) · [Leake and Ryder, Theorem 1.2](https://arxiv.org/pdf/1712.02499#page=2)

For $(36,5,6)$ the modified symbol and the actual input meet both hypotheses at $b=6/5,5/4,4/3,3/2,5/3,7/4$. At $b=2$ the modified symbol passes and the input fails the spacing test. The checker tests spacing by exact interlacing of $p(x)$ and $p(bx)$. Finding a factor that propagates across dimensions in general remains open.

## Exact checks and independent review

The [seven-row archive](results/column-extension-seven.jsonl.gz) stores both complete coefficient vectors at each $1\le t\le15$. The exact symbols have five distinct real zeros at $1\le t\le14$ and three at $t=15$. At $t=15$ the reversed symbol also gives a strict Laguerre violation at $-57/100$. The [earlier screen](results/column-extension-screen.jsonl.gz) stores the complete coefficient vectors for all 405 triples with $1\le n\le15$, $1\le r\le5$, and $r\le d\le\min(r+5,8)$. The [additional cap-two screen](results/column-extension-cap-two.jsonl.gz) covers 63 triples: $d=3,\ldots,6$ at $n=16$, $d=3,\ldots,7$ at $n=20$, and $d=3,\ldots,8$ at $n=24,30,\ldots,72$. Every symbol in these two screens was real-rooted.

An independent agent reviewer checked the coupling, the geometric decay bound, and the three rational inequalities. The reviewer also reconstructed the finite prefix by enumerating column complements. That recurrence tracks the sorted seven row counts of zeros, clipped at $d-r$ because only the lower quota matters. Each next complement contributes its multiplicity to the next sorted state. The terminal state with all seven coordinates clipped counts precisely the allowed arrays, and rational Sturm counts agree with the sharp cutoff. The proof and checks have no Lean or Rocq formalization.

From the repository root, use Python 3.10 or later and `python-flint==0.9.0`.

~~~sh
python topics/balanced-arrays/code/verify_column_extension.py
python topics/balanced-arrays/code/verify_column_extension.py --recount
~~~

The first command reconstructs the symbols and checks the root counts from the archived integers. The second also recomputes both original coefficient vectors for every archived case. Each JSONL record gives `n`, `r`, `d`, and the ascending coefficient vectors `left` and `right` for $d$ and $d+1$ columns.
