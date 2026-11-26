# Nonreal zeros under a common weight on two-entry rows

Let $P_n(q;t)$ count labeled balanced binary arrays with four columns and row cap two. An array of quota $k$ and $p$ two-entry rows contributes $q^kt^p$. Every allowed row type of a given size has the same weight, so the model retains all column permutations. Alexandersson asks about the specialization $t=1$. [Original question and matching count](https://github.com/PerAlexandersson/RealRooted/issues/2005)

**Theorem.** If $t_n/n\to\infty$ and $t_n/n^{5/2}\to0$, then for each positive integer $J$, $P_n(q;t_n)$ has at least $J$ conjugate pairs of nonreal zeros for all sufficiently large $n$. In particular $t_n=n^2$ suffices. At the scale $t_n\asymp n^{5/2}$ individual triples of zeros change behavior according to an explicit cubic.

**Exact example.** At $n=32$ and $t=216$ the degree is 16 and the polynomial is square-free. The variations of the Sturm sequence at $-\infty$, $0$ and $+\infty$ are $15,1,1$. There are fourteen negative roots and one nonreal conjugate pair. For $t=1$ at the same $n$, all sixteen roots are simple and negative. The data do not establish a least row count or weight. **⬜ None** for formal coverage. The independent checks use integer arithmetic in Python. [All 17 coefficients and signs](results/common-pair/weight-216-row-32.json) · [Independent mathematical review](review-symmetric-pair-weights.md)

## Counting by occupied row types

Write $a_i$ for the number of singleton rows of color $i$ and $b_{ij}$ for the number of pair rows of colors $i,j$. If there are $2s$ singleton rows, there are $2k-s$ pair rows and $L=2k+s$ occupied rows. Let $c_{k,s}$ be the sum of $1/(\prod a_i!\prod b_{ij}!)$ over these types with all margins $k$. Assigning the types to distinct labeled rows multiplies this by the falling factorial $(n)_L$, taken to be zero when $L>n$. Equivalently $c_{k,s}=m_{2k-s}(K_{k,k,k,k})/(k!)^4$ by labeling the occurrences in each column and matching those that share a row. This uses the author's matching count. Set $\epsilon=n/t$ and define
$$
H_n(z,\epsilon)=P_n\!\left(\frac{z}{n^2t^2};t\right)
=\sum_{k,s} c_{k,s}z^k\epsilon^s\frac{(n)_{2k+s}}{n^{2k+s}}.
$$
The positive rescaling preserves the number of nonreal zeros.

The series without the row factor, and with any fixed extra polynomial in $L$, converges absolutely on compact sets. Indeed for $|z|\le R$ and $|\epsilon|\le E$ put $u=R^{1/4}$. Dropping the equal-margin condition bounds the unmodified sum of absolute values by $\exp(4u\sqrt E+6u^2)$ by independent summation over all ten type multiplicities. For polynomial factors multiply every type variable by 2 before summing and use $L^p=O_p(2^L)$.

Let $F(z)=\sum_{j\ge0}z^j/(j!)^2$ and $G=F'$. With no singletons the opposite edges of the tetrahedron have equal multiplicities. Their three independent multiplicities contribute $f=F^3$. With two singletons of distinct colors one opposite edge has an extra occurrence. The six choices give $6zGF^2$. With two singletons of the same color there is a forced triangle on the other three colors. The four choices each have singleton factor $1/2!$, giving $2z^2G^3$. Here an unbalanced complementary edge pair contributes $G=\sum_{j\ge0}z^j/(j!(j+1)!)$. Thus the coefficient of $\epsilon$ in the infinite series is
$$
h=6zGF^2+2z^2G^3.
$$

## Finite row correction

For $L$ independent uniform draws from $n$ row labels, $(n)_L/n^L$ is the probability of no collision. Every two distinct pair-collision events have joint probability $1/n^2$, including events sharing one draw. The first two Bonferroni inequalities give
$$
0\le\frac{(n)_L}{n^L}-1+\frac{\binom L2}{n}
\le\frac{\binom{\binom L2}{2}}{n^2}
$$
also for $L>n$. For $s=0$ the first correction multiplies the $k$th coefficient by $-\binom{2k}2/n$. For $s=1$ its contribution is $O_K(\epsilon/n)$, and all $s\ge2$ give $O_K(\epsilon^2)$ by the compact majorant. We obtain, uniformly for $z$ in a compact set $K$ and $0\le\epsilon\le1$,
$$
H_n=f+\epsilon h-\frac{2z^2 f''+zf'}{n}
 + O_K(n^{-2}+\epsilon/n+\epsilon^2).
$$

## The local cubic and the number of conjugate pairs

The function $F(-x^2/4)=J_0(x)$ has infinitely many simple negative zeros in the $z$ variable. Fix one such zero $a$ and put $g=G(a)\ne0$. Taylor expansion on a fixed disk gives
$$
\frac{H_n(a+\delta,\epsilon)}{g^3}
=\delta^3+2a^2\epsilon-\frac{12a^2\delta}{n}
+O\left(|\delta|^4+\epsilon|\delta|+\epsilon^2+
\frac{|\delta|^2+\epsilon}{n}+\frac1{n^2}\right).
$$
[Distribution and simplicity of Bessel zeros](https://dlmf.nist.gov/10.21.i)

First suppose $t_n/n\to\infty$ and $t_n/n^{5/2}\to0$. Then $\epsilon\to0$ and $n\epsilon^{2/3}\to\infty$. Set $\delta=\epsilon^{1/3}w$ and divide by $\epsilon$. The limit is $w^3+2a^2$, locally uniformly in $w$. Its two nonreal roots are simple. Rouché's theorem on small disjoint disks off the real axis gives a zero in each disk for all sufficiently large $n$. For any fixed $J$ apply the argument at $J$ distinct zeros $a$. The resulting neighborhoods in $z$ are disjoint for large $n$, proving the theorem.

More precisely, if $n^{5/2}/t_n\to\lambda\in[0,\infty)$, use $\delta=w/\sqrt n$ and multiply by $n^{3/2}$. The limiting cubic and its discriminant are
$$
w^3-12a^2 w+2a^2\lambda,\qquad
108a^4(64a^2-\lambda^2).
$$
For $\lambda<8|a|$ there are three simple real roots in this cluster, since each conjugation-invariant disk about a limiting real root contains one zero counted with multiplicity. For $\lambda>8|a|$ there is one real root and one nonreal pair in this cluster. The equality case depends on smaller terms. All these conclusions concern a growing common pair weight. The original weight is $1$.

## Reproduction and scope

The certificate can be reconstructed by splitting the columns into two pairs and counting the intersection size of their row supports. The matching enumeration gives an independent calculation of each coefficient. A primitive integer Sturm sequence gives the sign variations from the coefficients. From the repository root run

~~~sh
python3 -I -O topics/balanced-arrays/code/verify_common_pair.py --certificate 32 216
~~~

With python-flint 0.9.0 installed, replay all recorded discovery observations with

~~~sh
python3 -I -O topics/balanced-arrays/code/verify_common_pair.py --verify-discovery topics/balanced-arrays/results/common-pair-discovery.jsonl.gz
~~~

The initial search retains all 553 coefficient vectors and exact square-free root counts up to its first nonreal example. The refinement located the 32-row example. [Independent certificate report and full refinement ledger](results/common-pair/referee.md) · [Discovery search](results/common-pair-discovery.jsonl.gz) · [Standalone verifier](code/verify_common_pair.py)

## Prior work and research decision

On November 25, 2026 we compared Alexandersson's source and its linked issue with the external balanced-array investigation. The latter recorded finite Newton checks and explicitly left real-rootedness open. GitHub issues searches used “uniform matroids” with “balanced arrays” and “balanced arrays” with “Bessel”. Web searches also used “pair weight”, “singleton weight”, “equal column sum binary matrices” and the author's name. Indexed X searches returned no relevant argument and a direct X query returned HTTP 403. These searches do not establish priority. The unweighted matching count and the Bessel zero theorem are inputs. The repository's earlier triangle example uses unequal pair weights. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs) · [External investigation](https://github.com/1337isnot1337/solved-conjectures/issues/165) · [Unequal-weight obstruction](triangle-weight-gap.md)

This rules out an all-positive, permutation-invariant row-weight extension as a proof route. The all-row problem at $t=1$ remains open. Quantitative sign control for that specialization or a bound valid on an interval containing $1$ would address the original problem.
