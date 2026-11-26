# Independent review of the four-column finite prefix

For a labeled binary array with $n$ rows and four columns, let $a_{n,k}$ count arrays with column sums all equal to $k$ and row sums at most two. The polynomial $P_n(q)=\sum_k a_{n,k}q^k$ has exactly $\lfloor n/2\rfloor$ distinct negative zeros for every integer $0\le n\le532$. In particular, $P_0=P_1=1$. This agent-assisted review checks the finite range of the four-column specialization of Per Alexandersson’s conjecture. The source separately raises consecutive-row interlacing, which requires a separate argument. [SymCat statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs) · [Author's specification and counting formula](https://github.com/PerAlexandersson/RealRooted/issues/2005)

## Cardinalities from the original arrays

Label the $k$ occupied positions within each column using $k$ distinct labels. A row with two ones pairs two labels from different columns. The resulting pairs are a matching of size $p$ in the complete four-partite graph with $k$ vertices of each color. The $p$ pairs and $4k-2p$ unmatched vertices give $4k-p$ identifiable blocks. Inject these blocks into the $n$ labeled rows, with all remaining rows zero. This construction is invertible for labeled occurrences, and each original array has $(k!)^4$ occurrence labelings. With $M_{k,p}$ the matching count, this gives the coefficient identity
$$
a_{n,k}=\frac{1}{(k!)^4}\sum_{p=0}^{2k}M_{k,p}(n)_{4k-p},
$$
where $(n)_s=n!/(n-s)!$ for $0\le s\le n$ and $(n)_s=0$ for $s>n$. Every nonzero count requires $4k\le2n$. Conversely, $k$ rows of type $\{1,2\}$ and $k$ rows of type $\{3,4\}$, padded with zero rows, realize every $0\le k\le\lfloor n/2\rfloor$. The constant coefficient is one.

The producing script computes $M_{k,p}$ by inclusion–exclusion. If $F_{k,a}$ counts matchings of size $a$ using only edges within the four color classes, the count after excluding all such edges is
$$
M_{k,p}=\sum_{a=0}^p(-1)^a F_{k,a}
\frac{(4k-2a)!}{(4k-2p)!\,2^{p-a}(p-a)!}.
$$
A chosen set of forbidden edges contributes only when it is a matching. Removing its endpoints leaves a complete graph on $4k-2a$ vertices, which gives the remaining factorial expression. For the finite sum over $p$ the producer uses another scaled exponential convolution, starting at $n=2k$. Dividing its resulting integer by the factorial scale gives the displayed array coefficient identity.

The independent checker computes all $M_{k,p}$ by appending one color class at a time. An old $p$-edge matching on $c$ colors leaves $f=ck-2p$ unmatched vertices. A choice of $j$ edges to the new color has $\binom{f}{j}\binom{k}{j}j!$ possibilities. Each new matching has a unique restriction to the old colors. Then the checker evaluates the falling-factorial sum directly using integer operations, factoring out $(n)_{2k}$. The producing script also uses the color-class recurrence as a cross-check for $k\le24$, while its primary inclusion–exclusion algorithm and the independent calculation agree for all $0\le k\le266$.

A direct row-by-row column-margin dynamic program agrees with every coefficient through $n=12$. An additional calculation groups columns as $\{1,2\}$ and $\{3,4\}$, chooses the rows taking both entries of either pair, then independently places the remaining entries of each pair in disjoint subsets of the remaining rows. This checks $k\in\{0,\lfloor n/4\rfloor,\lfloor n/2\rfloor\}$ at $n\in\{266,531,532\}$.

## Exact signs and root count

For a row of degree $m\ge1$, the recorded positive dyadics $t_j$ increase strictly and give $\mathrm{sgn}\,P_n(-t_j^4)=(-1)^j$ for $1\le j<m$. The value at $t=0$ is positive and the sign for sufficiently large $t$ is $(-1)^m$, by the positive leading coefficient. Continuity supplies one root per consecutive open interval, starting at zero and ending with the interval to infinity. The map $t\mapsto-t^4$ is injective on $t>0$, so there are $m$ distinct negative roots. Degree $m$ then forces all to be simple. The same argument works without interior nodes when $m=1$. Degree zero gives no roots.

The producer's floating-point phase is only a way to propose dyadic nodes. Its replay uses Arb enclosures to establish the strict signs. The independent checker evaluates every sign by exact integer Horner evaluation, with no floating-point phase or interval arithmetic. For a node $q=A/B$ in reduced form with $B>0$, the evaluated integer is $B^mP_n(A/B)$, which has the same sign.

## Replay

The topic package contains the nine archives, the producing checker and the independent checker. From the [topic folder](../README.md), use Python 3.13 with python-flint 0.9.0.

~~~sh
shasum -a 256 -c SHA256SUMS
python code/prefix.py --directory certificates/rows --verify --last 532
python code/independent_prefix.py certificates/rows --last 532
~~~

On an Apple M1 with Python 3.13.5, python-flint 0.9.0 and FLINT 3.6.0, the producing checker took 2.82 seconds and verified all 533 rows and 70,225 interior signs, with zero integer fallbacks. The independent run took 34.46 seconds, reconstructed and compared 71,289 coefficients and checked the same 70,225 signs using integers. This finite range has computational verification (⬜ None for Lean or Rocq). The review found no mathematical objection to the finite root claim.
