# Mixed-phase extension intervals for the million-row cap transition

Mathematical argument and exact computation by Codex (lower_sign_replay), 2026-11-26.

For labeled arrays with $`(n,d,r)=(10^6,250000,127000)`$, the mixed-phase comparison certifies the exact disk count $`k`$ with no boundary zeros at the actual geometric radius for all 809 quotas from $`505662`$ through $`506470`$. The signed seven-term lower bounds exceed $`1/1000`$, with the smallest bound equal to $`0.00217539`$ when rounded down to eight decimal places. This continues the balanced-endpoint certificate through $`505661`$. Combining both with the independent last-95 certificate isolates at least $`506565`$ simple negative roots of degree $`508000`$, leaving $`1435`$ positions. At quota $`506000`$ the certified log decrement lies between $`62.487772`$ and $`62.524872`$, and its adjacent increment lies between $`0.105843`$ and $`0.179898`$. At quota $`507000`$, the same independent interval information allows a synthetic monotone slope sequence with a negative sign. The obstruction concerns the interval relaxation.

**Formal verification**　⬜ None. [Independent mathematical review](replay/review.md) · [Independent exact checker](replay/verify.py) · [Earlier marked-row certificate](../README.md)

## One extension phase

Let $`A(\boldsymbol q)`$ count capped arrays with column quota vector $`\boldsymbol q`$, and let $`P(\boldsymbol q)=A(\boldsymbol q)/\prod_h\binom n{q_h}`$. In the phase from balanced quota $`k`$ to $`k+1`$, let $`\ell`$ columns already have quota $`k+1`$, let the remaining quotas be $`k`$, and choose the next column $`i`$ among the latter. For a specified row $`X`$, the exact normalized insertion probability is

$$
\frac{P(\boldsymbol q+e_i)}{P(\boldsymbol q)}
=1-\Pr(|X|=r\mid X_i=0).
$$

Indeed adding a uniform unused entry in column $`i`$ generates the uniform column design at the next quota, and the insertion preserves the cap exactly when the chosen row was unsaturated. Row permutation symmetry identifies the mean fraction of saturated unused positions with the displayed conditional probability.

Given $`X_i=0`$, write $`f(S)`$ for the weight of a marked-row support $`S\subseteq[d]\setminus\{i\}`$, $`|S|\le r`$. It equals the capped completion count at height $`n-1`$ and residual quotas $`\boldsymbol q-\mathbf1_S`$. All such residual quotas and needed increments have positive counts on the tested range. Their coordinates are at most the residual height, and their total is at most the residual height times the cap. For feasibility with unequal quotas, split consecutive cyclic row labels into successive blocks of the specified column lengths. No label is repeated within a block and each row's occupancy is at most the cap.

When $`h\notin S\cup\{i\}`$ and $`|S|<r`$, the binomial normalization gives

$$
\frac{f(S\cup\lbrace h\rbrace )}{f(S)}
=\frac{q_h}{n-q_h}\frac1{1-e_{\mathrm{res},h}} ,
$$

where $`e_{\mathrm{res},h}`$ is the actual extension loss at residual height $`n-1`$ and base $`\boldsymbol q-\mathbf1_{S\cup\{h\}}`$. That base lies coordinatewise between $`k-1`$ and $`k+1`$. Its loss is bracketed by the balanced losses at those residual quotas, by the earlier orientation comparison. Let $`L`$ be a lower bound on the loss at $`(n-1,k-1)`$ and $`U`$ an upper bound on the loss at $`(n-1,k+1)`$. The resulting product support weights have odds $`q_h/[(n-q_h)(1-L)]`$ and $`q_h/[(n-q_h)(1-U)]`$, respectively.

For the lower product weight, $`f(S)`$ divided by that product is nondecreasing under set inclusion. Under an independent Bernoulli product law with any fixed odds, the set conditional on its size is stochastically increasing in the size. This is the integer Bernoulli case of Efron's result. Thus the conditional mean of that ratio increases with size, which proves likelihood-ratio domination of the lower truncated Poisson-binomial size law. The upper ratio is nonincreasing and gives the opposite bound. The top masses of these two truncated product laws therefore bracket the insertion loss. [Efron (1965)](https://doi.org/10.1214/aoms/1177700288), [orientation comparison](https://github.com/ProgramComputer/open-math-research/blob/research/topics/balanced-arrays/orientation-normalization.md).

## Rational bounds for the product laws

Put $`m=d-1`$, let $`w_0,w_1`$ be the odds of the two quota classes including their same residual factor, and set $`\beta=\log(w_1/w_0)>0`$. If a uniform $`j`$-subset of the $`m`$ columns contains $`H`$ of the $`\ell`$ higher-odds columns, its weight is $`w_0^j e^{\beta H}`$. Jensen's inequality gives a lower bound on the mean factor. The sampling-without-replacement comparison and Hoeffding bound give the upper factor $`e^{j\beta^2/8}`$. Thus the coefficient of size $`j`$ lies between $`\binom mj g^j`$ and $`\binom mj g^j e^{j\beta^2/8}`$, where $`g=w_0^{1-\ell/m}w_1^{\ell/m}`$. [Hoeffding (1963), Theorems 1 and 4](https://doi.org/10.1080/01621459.1963.10500830).

Let $`c=r(w_1/w_0-1)^2/8`$. The top mass of the truncated product law is between $`(1-c)`$ and $`1/(1-c)`$ times the top mass $`Q_r(g)`$ of the corresponding truncated binomial. This follows by applying the coefficient bounds at all sizes up through $`r`$ and using $`\beta\le w_1/w_0-1`$. Weighted harmonic and arithmetic means of $`w_0,w_1`$ bound $`g`$ by rationals. Since the truncated-binomial top mass increases with its odds, these rational means preserve the required bound directions. The replay uses summation of the exact downward recurrence from the cap atom, with outward integer rounding.

For a grid of phase endpoints, both continuous top-mass bounds are increasing with $`\ell`$. Thus lower and upper rectangular sums enclose the total log decrement $`S_k=-\log(P_{k+1}/P_k)`$. The implementation also uses a sharper, cheaper convex comparison when its rational guard holds. With log odds $`y`$, ordinary binomial parameter $`p`$, top mass $`Q_r`$ and conditional mean $`\mu`$, write $`h=r-\mu`$. Differentiation gives $`Q_r'=Q_rh`$ and $`Q_r''=Q_r(h^2-\mathrm{Var})`$. The exact mean identity $`\mu=mp-p(m-r)Q_r`$ yields $`\mathrm{Var}\le mp(1-p)\le m/4`$ by differentiation, since $`Q_r`$ and $`p`$ are increasing. When $`r-mp_{\max}\ge\sqrt m/2`$, the top mass is convex over the entire phase odds interval. So is the negative log survival after multiplying the mass by either positive constant $`1-c`$ or $`1/(1-c)`$. A midpoint value is a lower bound on the mean of the $`d`$ discrete phases, and the average of the two endpoints is an upper bound. The arithmetic mean of the phase fractions $`\ell/(d-1)`$ is exactly $`1/2`$. The program tests the convexity guard using rational arithmetic and otherwise uses 16 blocks and the rectangular comparison.

The residual lower loss is obtained by 18 applications of the earlier scalar recurrence, starting with zero. For a residual query of height $`N_0`$ and quota $`K_0`$, a rational cap tilt is an upper witness if $`d(z-K_0/N_0)\ge z(d-r)Q_r(z)`$. The exact implementation tests the inequality using an upper atom enclosure. [Earlier recursion and matched-mean comparison](../recursion-review.md), [two-sided endpoint review](../literature.md).

## Optimizing the seven-term sign on the slope box

Let $`B_j=\binom nj^d`$, and write $`w_j^0`$ for the normalized magnitude at offset $`j`$ on the unrestricted geometric circle centered at $`k`$. The actual circle has radius $`\sqrt{A_{k-1}/A_{k+1}}`$. Its normalized magnitudes are the unrestricted terms multiplied by the cap factors. Write $`x_j=S_{k+j}`$ for $`j=-3,\ldots,2`$. If $`A=x_0-x_{-1}`$, the two first neighbors both have cap factor $`e^{-A/2}`$. The exponents of their cap factors through offset three, written with positive sign in the denominator exponential, are

$$
x_0-x_{-2},\quad x_1-x_{-1},\quad
(3x_0+x_{-1})/2-x_{-2}-x_{-3},\quad
x_1+x_2-(x_0+3x_{-1})/2
$$

at offsets $`-2,2,-3,3`$, respectively. The exact check verifies that consecutive slope intervals are disjoint in increasing order. Hence the entire six-dimensional box consists of monotone slopes. On this box, the actual normalized local magnitude profile has at least the unrestricted coefficient curvature. Call the first-neighbor magnitude $`t`$ and the offset two and three magnitudes $`w_{\pm2},w_{\pm3}`$. In particular $`w_{\pm2}<t/2`$ and $`w_{\pm3}<w_{\pm2}`$.

In increasing variable order $`x_{-3}`$ through $`x_2`$, the seven-term parity is decreasing, increasing, decreasing, increasing, decreasing, increasing. The only derivatives needing a combined bound are those in $`x_{-1}`$ and $`x_0`$. In $`x_0`$ the derivative is $`t-w_{-2}-w_3/2+3w_{-3}/2>0`$. In $`x_{-1}`$ it is $`-t+w_2-3w_3/2+w_{-3}/2<0`$. The signs follow from outward decrease and the bound $`w_{\pm2}<t/2`$. The other four derivatives have signs directly from the formula. Thus the signed lower bound comes from taking upper endpoints for odd indices and lower endpoints for even indices, preserving the shared slope variable in every term. Outside offset three, consecutive outward pairs start at an even offset and have nonnegative total. A positive seven-term bound certifies the complete strict sign.

All certified centers are at an aspect where the earlier $`9/4`$ theorem gives exactly the centered disk count from this positive sign. Indeed the quotient is at least $`(1+2/n)^{2d}>9/4`$. This is the actual array's geometric radius, and consecutive certified counts and alternating signs yield one simple negative root per annulus. [Sharp one-sign count](https://github.com/ProgramComputer/open-math-research/blob/8c799d583509ae03f3e3caabc0e3d02449695f15/topics/balanced-arrays/root-distributions/single-sign/README.md).

## Exact obstruction to six independent intervals at quota 507000

The six computed phases admit the strictly feasible rational interval choices $`x=(514,514.3,516.5,516.5,518.9,519)`$. They are nondecreasing. Extend these synthetic log slopes constantly on either side, defining positive synthetic validity coefficients from $`P_0=1`$. The extension has normalized log-concavity. Its central cap curvature increment is zero, so the two normalized first neighbors exceed $`3/5`$ each. The unrestricted second neighbors are below $`7/50`$ each, and the cap factors reduce them by more than a factor of eight. All outward pairs beginning at offset three have nonpositive signed contribution. The full synthetic signed sum is therefore below $`1-2(3/5)+2(7/50)/8=-33/200`$. This certifies that the six independent intervals plus monotone slopes cannot settle that quota. It does not assert a sign reversal for the actual array.

## Replay

Run the following from this directory. The default run uses Python's standard library and only exact integer and rational calculations. The optional tilt-witness generator uses floating point to propose rational endpoints, then runs the same independent exact tests. The independent verifier uses a different fixed-point grid and checks the proposed tilts.

~~~sh
python3 -IB verify.py
python3 -IB verify.py --obstruction-only
python3 -IB replay/verify.py
~~~

## Source search

On 2026-11-26 I searched scholarly and web indexes for conditioned weighted subsets, Poisson-binomial bounds and capped margin counts. Efron gives the stochastic increase under conditioning on size, and Hoeffding gives the comparison of sampling with and without replacement used above. GitHub searches for code containing “capped,” “Poisson-binomial,” and “balanced arrays,” and for issues containing “balanced arrays” with “mixed-phase,” returned zero results. A web-indexed X search found no related result, and the native X query returned HTTP 403. These searches document scope and establish no priority claim.
