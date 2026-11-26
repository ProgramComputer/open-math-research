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

## Exact checks and independent review

The [seven-row archive](results/column-extension-seven.jsonl.gz) stores both complete coefficient vectors at each $1\le t\le15$. The exact symbols have five distinct real zeros at $1\le t\le14$ and three at $t=15$. At $t=15$ the reversed symbol also gives a strict Laguerre violation at $-57/100$. The [earlier screen](results/column-extension-screen.jsonl.gz) stores the complete coefficient vectors for all 405 triples with $1\le n\le15$, $1\le r\le5$, and $r\le d\le\min(r+5,8)$. The [additional cap-two screen](results/column-extension-cap-two.jsonl.gz) covers 63 triples: $d=3,\ldots,6$ at $n=16$, $d=3,\ldots,7$ at $n=20$, and $d=3,\ldots,8$ at $n=24,30,\ldots,72$. Every symbol in these two screens was real-rooted.

An independent agent reviewer checked the coupling, the geometric decay bound, and the three rational inequalities. The reviewer also reconstructed the finite prefix by enumerating column complements. That recurrence tracks the sorted seven row counts of zeros, clipped at $d-r$ because only the lower quota matters. Each next complement contributes its multiplicity to the next sorted state. The terminal state with all seven coordinates clipped counts precisely the allowed arrays, and rational Sturm counts agree with the sharp cutoff. The proof and checks have no Lean or Rocq formalization.

From the repository root, use Python 3.10 or later and `python-flint==0.9.0`.

~~~sh
python topics/balanced-arrays/code/verify_column_extension.py
python topics/balanced-arrays/code/verify_column_extension.py --recount
~~~

The first command reconstructs the symbols and checks the root counts from the archived integers. The second also recomputes both original coefficient vectors for every archived case. Each JSONL record gives `n`, `r`, `d`, and the ascending coefficient vectors `left` and `right` for $d$ and $d+1$ columns.
