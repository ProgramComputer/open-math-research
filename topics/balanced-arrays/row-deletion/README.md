# Two obstructions to transferring real-rootedness by deleting rows

Let $P_n(q)=\sum_k a_{n,k}q^k$ count labeled binary arrays with $n$ rows, $d$ columns, common column sum $k$ and row cap $r$. The original conjecture asks for real-rootedness of these unweighted polynomials. The examples below limit two proposed backward transfer methods. The deterministic implication from real-rootedness of $P_{n+1}$ to that of $P_n$ remains open. **⬜ None** for Lean or Rocq. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Research issue #2](https://github.com/ProgramComputer/open-math-research/issues/2)

## The direct coefficient map

Fix $(r,d)=(2,4)$. The diagonal coefficient map that sends $P_8$ to $P_7$ multiplies coefficient $k$ by $a_{7,k}/a_{8,k}$, using zero above the degree of $P_7$. A universal real-rootedness preserver in degree at most four would send the negative-rooted test polynomial $(1+q)^4$ to a real-rooted polynomial.

The coefficient vectors of $P_7,P_8$, in ascending order, are

$$
(1,2226,102690,106260),\qquad
(1,3864,380100,1543920,44730).
$$

Scaling the image of $(1+q)^4$ by a positive constant gives the primitive integer polynomial

$$
S(q)=19128985+44079835q+31007979q^2+5266195q^3.
$$

At $q=-1$, $S,S',S''$ are $790934,-2137538,30418788$, respectively, so

$$
(S'(-1))^2-S(-1)S''(-1)=-19490184966548.
$$

For a real-rooted polynomial $S$, this expression equals $S(q)^2\sum_\alpha(q-\alpha)^{-2}$ away from its roots $\alpha$, counted with multiplicity, so it is nonnegative. The violation proves a nonreal pair in the symbol. Both actual array polynomials have simple negative roots. [Four-column result](../four-columns/README.md) · [Independent witness reconstruction](review-multiplier.md)

For the [rank-two coefficient archive](../results/source_range.jsonl), the same construction gives 360 consecutive pairs. Exactly 225 symbols have a nonreal zero and the other 135 have only real zeros, by exact Sturm arithmetic. The [full symbol archive](inverse-row-symbols.jsonl.gz) retains both input vectors, the primitive symbol and the exact root report for each pair. Its gzip header has zero timestamp and no stored filename.

## Independent optional rows

For fixed $d,r$, let $P_N(q)$ be the ordinary balanced-array polynomial on $N$ labeled rows. Starting with $N$ mandatory rows, introduce $M$ optional rows and retain each independently with probability $p$. The expected polynomial is

$$
B_{N,M,p}(q)=\sum_{u=0}^{M}\binom Mu p^u(1-p)^{M-u}P_{N+u}(q).
$$

Equivalently, take the coefficient of each equal-exponent monomial in the product of $N$ ordinary row factors and $M$ factors $1+p(e_1+\cdots+e_r)$. This is also the deletion homotopy from $P_{N+M}$ to $P_N$ obtained by decreasing the optional rows' activity together. Every realized set of retained rows uses the ordinary unweighted count.

**Obstruction.** At $d=3,r=2$, for any $N$ divisible by three, three optional rows suffice to produce a nonreal zero for sufficiently small positive $p$. This holds for arbitrarily large $N$. All four deterministic polynomials in the mixture have simple negative zeros in positive degree by the [corank-one theorem](https://github.com/ProgramComputer/open-math-research/blob/ad3691053ff52215f980358f3c3a2f970702e185/topics/balanced-arrays/no-full-row.md). More generally, if $r$ does not divide $d$, a bounded number of optional rows suffices for every base $N$, with the bound depending only on the fixed shape $(r,d)$.

### Capacity and the obstruction

Write $m=\lfloor Nr/d\rfloor$ and $s=Nr-dm$. For $j\ge1$, the fewest extra rows that allow quota $m+j$ is

$$
u_j=\left\lceil\frac{dj-s}{r}\right\rceil .
$$

The capacity bound forces this number. It is attained by allocating the $d(m+j)$ occupied cells consecutively in groups of size at most $r$ along cyclic column order, then padding with empty rows. Each group has distinct column indices since $r\le d$. Thus for $u_j\le M$, the coefficient of $q^{m+j}$ in $B_{N,M,p}$ is a strictly positive constant times $p^{u_j}(1+O(p))$ as $p\downarrow0$. At quota $m$ its leading power is zero.

If $r$ does not divide $d$, let $g=\gcd(d,r)$ and $P=r/g$. The increments $u_j-u_{j-1}$ for $j\ge2$ are periodic of period $P$, with each increment either $\lfloor d/r\rfloor$ or $\lceil d/r\rceil$. Both values occur, since their period average is the noninteger $d/r$, by $u_{j+P}=u_j+d/g$. There is consequently a strict drop between two consecutive increments with middle index $j\in[2,P+1]$. Choose $M=u_{j+1}\le\lceil d(P+2)/r\rceil$. At quota $m+j$, the ratio of the squared coefficient to the product of its neighbors is a positive constant times

$$
p^{\,2u_j-u_{j-1}-u_{j+1}}(1+O(p)),
$$

which tends to zero at the strict drop. This violates the ordinary log-concavity required of positive coefficients of a polynomial with all roots real and negative.

For $d=3,r=2$ and $3\mid N$, the first three quotas $m,m+1,m+2$ already have minimal extra-row counts $0,2,3$. Taking $M=3$, their coefficient ratio is $O(p)$ and gives the stated obstruction. In particular, this example can be placed entirely inside an eventual region in which every deterministic row polynomial is real-rooted.

### Exact example and quantitative family

For $N=3$, $M=3$ and $p=1/500$, the three coefficients at quotas $2,3,4$ are

$$
\frac{415851453}{62500000},\qquad \frac{681}{312500},\qquad
\frac{9}{12500000}.
$$

The product of the first and third exceeds the square of the middle by $32575077/781250000000000>0$. These values can be checked with [the exact script](check_witnesses.py). In corank one the underlying coefficients are obtained by inclusion–exclusion on full rows, giving
$a_{n,k}=\sum_{t=0}^k(-1)^t\binom nt\binom{n-t}{k-t}^3$ for $d=3,r=2$.

In fact any positive schedule $p=o(N^{-2})$ gives failure along $3\mid N$, $N\to\infty$. To see this, put $N=3u$, $m=2u$, and define

$$
A=a_{N,m},\quad B=a_{N+2,m+1},\quad C=a_{N+3,m+1},\quad D=a_{N+3,m+2}.
$$

All rows are full at the two extreme coefficients, so $A=N!/(u!)^3$ and $D=(N+3)!/((u+1)!)^3$. The count $B$ has exactly one singleton row; choosing its location and column and then the missing columns of the full rows gives $B=3(N+2)!/[(u+1)!(u!)^2]$. Hence $B/A=O(N)$ and $D/A\to27$. For $C$, the total capacity slack is three. After choosing at most three deficient rows and their supports in $O(N^3)$ ways, the number of assignments of missing columns to the full rows is at most the largest trinomial coefficient on $N+3$ labels, which is $D=O(A)$. Thus $C/A=O(N^3)$. The ordinary coefficient ratio of $B_{N,3,p}$ at quota $m+1$ is at most

$$
\frac{p\,[3B/A+pC/A]^2}{(1-p)^3(D/A)}
=O(pN^2)\longrightarrow0.
$$

The inequality follows because the central coefficient is at most $p^2(3B+pC)$, its lower neighbor is at least $(1-p)^3 A$, and its upper neighbor is exactly $p^3D$.

Independent optional-row retention therefore cannot supply a transfer through real-rootedness along this homotopy. [Independent review](review-thinning.md)

## Remote and doubled sources

At $(r,d)=(2,4)$, the backward coefficient map from $2n$ fails its binomial test for every target $n\ge11$. For each fixed target $n\ge16$, the map from a sufficiently late source also fails on inputs with the source polynomial's root mesh. [Proof and exact replay](remote-transfer.md)

## Exact replay

From the repository root, reconstruct both witnesses. The archive command regenerates the exact symbols and Sturm reports and requires python-flint.

~~~sh
python -B topics/balanced-arrays/row-deletion/check_witnesses.py
python -B topics/balanced-arrays/row-deletion/verify_archive.py
~~~
