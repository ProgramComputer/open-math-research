# Coefficientwise balancing with a correction for each column

Let $`A(\mathbf u;\mathbf w)`$ enumerate labeled $`0`$–$`1`$ matrices on a fixed set of rows and $`d`$ columns with column margins $`\mathbf u`$ and, for each row $`v`$, a fixed interval of allowed sizes $`[L_v,U_v]`$. Give each occupied cell its own commuting variable $`w_{vj}`$. Suppose $`\mathbf a\le\mathbf b`$ coordinatewise, and $`0\le t_j\le b_j-a_j`$ are integers. Use the same color for the smaller source quota in every column, so one copy has margins $`\mathbf a`$ and the other has $`\mathbf b`$. For any feasible pair of source margins, the following holds coefficientwise:

$$
A(\mathbf a+\mathbf t)A(\mathbf b-\mathbf t)
\succeq
\prod_{j=1}^d\frac{a_j!b_j!}{(a_j+t_j)!(b_j-t_j)!}
A(\mathbf a)A(\mathbf b).
$$

The notation $`\succeq`$ means that every coefficient of the difference is nonnegative. The stronger formula for each individual cell monomial below is the main point. The hypotheses allow arbitrary identical row intervals in the two copies, not only one common cap.

Fix the monomial. In each column the sites of exponent two are occupied by both copies, and the sites of exponent one by exactly one. Let $`c_j`$ be the number of double sites and put $`x_j=a_j-c_j,\ y_j=b_j-c_j,\ \delta_j=y_j-x_j`$. It suffices to treat monomials with a nonzero source. Add $`\delta_j`$ distinguishable dummy rows in column $`j`$, otherwise empty. Require all of these cells to be red in the source. In the target, prescribe $`\delta_j-t_j`$ of them red and the other $`t_j`$ blue. Both augmented copies now have margin $`b_j`$ in column $`j`$. Match the exclusive sites in each column into red-blue pairs, requiring that no pair join two dummies.

For each original coloring the number of such refinements in column $`j`$ is $`y_j!`$, since the dummies are all red. In a target coloring, assign the $`t_j`$ blue dummies distinct real red sites in $`(x_j+t_j)!/x_j!`$ ways, and assign the red dummies distinct real blue sites in $`(y_j-t_j)!/x_j!`$ ways. The remaining $`x_j`$ real sites of each color pair in $`x_j!`$ ways. Thus the refinement multiplicity on the target side is $`(x_j+t_j)!(y_j-t_j)!/x_j!`$. All choices here are made on the same fixed real cell monomial, and all pair collections are unordered after their members have been specified.

Forget the orientations in a refinement. Its pairs are labeled edges on row vertices; an edge is oriented from its red to its blue endpoint. The two original row intervals are identical on each real row. Consequently its lower bounds on indegree and outdegree coincide, by using the fixed total degree and the number of double sites in that row. At each dummy its source lower bounds are $`(1,0)`$ in outdegree, indegree order, and its target bounds either remain these or become $`(0,1)`$. For every fixed allowed pairing the graph-orientation inequality of Kahn–Neiman gives at least as many target as source orientations. Its hypotheses hold vertex by vertex, including equality of the sums of the two lower bounds. Parallel edges are labeled, as in that result. The exclusion of dummy–dummy pairs is a restriction on the common undirected skeleton and does not depend on the orientation. [Kahn–Neiman, §4, Lemma 8](https://arxiv.org/pdf/1001.0610) · [Earlier equal-margin orientation reduction](https://github.com/ProgramComputer/open-math-research/blob/ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2/topics/balanced-arrays/orientation-normalization.md)

Summing over the common allowed pairings and dividing out their respective multiplicities gives the monomial multiplier

$$
\prod_j\frac{x_j!y_j!}{(x_j+t_j)!(y_j-t_j)!}
=\prod_j\frac{\binom{y_j}{t_j}}{\binom{x_j+t_j}{t_j}} .
$$

This is at least the claimed global multiplier. To see it, replace $`t_j`$ by $`\min(t_j,\delta_j-t_j)`$, which leaves the factorial quotient unchanged. It is a product of factors $`(b_j-c_j-t_j+i)/(a_j-c_j+i)`$ for $`1\le i\le t_j`$. Each factor is nondecreasing in $`c_j`$ because $`b_j-t_j\ge a_j`$. Thus its minimum is attained at $`c_j=0`$. The case of a zero source coefficient is immediate.

For common quotas let $`a_k(\mathbf w)=A(k\mathbf1;\mathbf w)`$ and $`b_k=(k!)^d a_k(\mathbf w)`$. Every two-by-two Toeplitz minor of $`b_k`$ is coefficientwise nonnegative: its two terms have the same sum of quota indices, and the main-diagonal pair is weakly more balanced. Extend the sequence by zero off its feasible contiguous nonnegative support, as usual for an interval row cap. Equivalently this follows directly modulo any zero term using the same comparison. The corresponding unweighted two-term minors in the quota index, with row count $`n`$ varying have nonnegative binomial-basis coefficients when all rows have the same cap. Indeed the coefficient of $`\binom ns`$ groups array pairs using exactly a fixed set of $`s`$ row labels, and the fixed-monomial argument preserves the union of those row supports. This statement concerns Toeplitz minors in the quota index at each variable row count.

There is also a consequence for directed shifted rays. If $`F_{\mathbf u}(q)=\sum_k A(k\mathbf1+\mathbf u)q^k`$ and $`\mathbf e_i`$ is a positive coordinate step, the Laurent polynomial $`F'_{\mathbf u}F_{\mathbf u+\mathbf e_i}-F_{\mathbf u}F'_{\mathbf u+\mathbf e_i}`$ has nonnegative coefficients jointly in $`q`$ and the cell variables. After pairing its terms at indices $`k>l`$, the relevant difference is

$$
(k-l)\big(A(k\mathbf1+\mathbf u)A(l\mathbf1+\mathbf u+\mathbf e_i)-A(l\mathbf1+\mathbf u)A(k\mathbf1+\mathbf u+\mathbf e_i)\big).
$$

When the second product is nonzero apply the vector comparison to its lower and upper margins and move one unit only in coordinate $`i`$. This proves nonnegativity termwise. The claim supplies the directed Wronskian sign on the positive real axis. Directed interlacing also requires control on the negative axis; that is left open.
