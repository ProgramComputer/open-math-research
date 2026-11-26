# Fractional matching gaps obstruct weighted real-rootedness

Keep the labeled rank-two array definition and give each singleton and
empty row weight one. Give a pair row $ij$ weight $t^{c_{ij}}$, where
$t>0$ and $c_{ij}\ge0$. Write $a_k(t)$ for the total weight with common
column sum $k$.

**Proposition.** Let $\nu$ be the maximum weight of a matching on the
columns with objective weights $c_{ij}$. Let $\nu^*$ be the optimum
of the fractional relaxation with nonnegative edge variables and
incident weight at most one at every vertex. If $\nu^*>\nu$, then
for every $n\ge2d$ the array polynomial has nonreal zeros for all
sufficiently large $t$. For a triangle of heavy edges on four columns,
the conclusion already holds for each $n\ge5$.

**Proof.** At quota one, the pair rows form a matching on the columns.
For $t\ge1$ this gives $a_1(t)\le n^d t^\nu$. Take an optimal
extreme fractional matching. Its positive entries consist of disjoint
unit edges and disjoint odd cycles of half-edges. Here is the short
extreme-point argument. In a connected component of strictly fractional
edges, the number of edges cannot exceed the number of tight incident
constraints. Otherwise a nonzero perturbation and its negative preserve
all tight constraints and stay feasible when sufficiently small. A tree
component has two slack leaves. A component containing a cycle must
therefore have exactly as many edges as vertices and every constraint
tight. All degrees are then at least two, so it is a cycle. Alternating
perturbations exclude even cycles, and on an odd tight cycle every
entry equals one half. [Balinski’s fractional matching result, 1965](https://doi.org/10.1287/mnsc.12.3.253)

Double the optimum and realize each resulting edge as one row. Complete
each column to quota two with singleton rows. There are at most $2d$
nonempty rows, and a single such array gives $a_2(t)\ge t^{2\nu^*}$.
The same proof applies at smaller $n$ whenever this configuration fits.
Thus $a_1(t)^2/a_2(t)\to0$ at fixed $n$. A real-rooted polynomial with
constant term one and positive coefficients factors as
$\prod_i(1+\lambda_i q)$ with $\lambda_i>0$ and satisfies
$a_1^2\ge2a_2$. This proves the proposition.

### Four columns and five rows

Take $c_{12}=c_{13}=c_{23}=1$ and all other exponents zero. The
fractional optimum is $3/2$ and the integral optimum is one.
The doubled optimum requires three distinct triangle pairs and two
singleton rows in column four, hence fits in five rows.
At $n=5$ direct enumeration gives
$$
P_5(q;t)=1+(300+240t)q+(1080t+1350t^2+60t^3)q^2 .
$$
At $t=256$ its coefficient vector is $(1,61740,1095383040)$ and its
discriminant is $-569704560$. At $t=1$ it is the original polynomial
$1+540q+2490q^2$, whose discriminant is $281640$. For this choice of
heavy edges, $n=4$ gives discriminant $9216+20736t+11304t^2>0$, and
$n<4$ gives at most one root. Five is thus the first possible row count
for this particular weighting.

The pair weights can even be written $w_{ij}=b_i b_j$ with
$b_1=b_2=b_3=\sqrt t$ and $b_4=1/\sqrt t$. Rescaling the four column
variables converts this to constant pair weights and unequal singleton
weights $1/b_i$, followed by the positive change $q\mapsto tq$.
Hence the uniform four-column problem requires care when allowing
unequal singleton weights. The coefficientwise nonnegativity of
Bézout *entries* holds throughout this counterexample. A proof that
makes every adjacent Bézout matrix positive semidefinite for every
positive specialization would give a false conclusion in this model.
[Rank-two coefficient inequalities](rank-two-row-minors.md) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

**⬜ None.** The five-row certificate was reconstructed independently
by enumerating the four column subsets. The general proof uses the
classical half-integrality theorem and the labeled-matching description.
[Independent check and literature search](triangle-weight-review.md) · [Executable certificate](code/verify_triangle_weight_gap.py)

~~~sh
python3 -I -B topics/balanced-arrays/code/verify_triangle_weight_gap.py
~~~
