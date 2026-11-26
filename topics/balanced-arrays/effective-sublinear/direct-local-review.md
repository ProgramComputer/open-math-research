# Independent review of the direct local comparison

I checked the row cumulants and their logarithmic remainder in
[direct-row-expansion.md](direct-row-expansion.md), then the
fixed-profile estimate and both stages of the comparison in
[direct-comparison.md](direct-comparison.md). I accept the adjacent-quota
comparison in its stated window $`u=\log n\ge10^6`$,
$`100/u\le d/n=s\le1`$, including feasible saturation. I used the
stated off-chart estimate as an input. This review does not independently
check that estimate, which I derived separately.

## One-row expansion and summation

The inclusion-probability expansion gives the stated second and third moments.
In degree four the two terms with exactly two indices contribute
$`-4Q_4+3(Q_2^2-Q_4)`$. The three-index term is
$`12\sum_j y_j^2(y_j^2-Q_2/2)`$, and the four-index contribution follows
by subtraction from zero. The identities
$`P_2-2P_3+P_4=\xi`$ and $`P_1-P_2=a`$ yield the specified fourth
cumulant after subtracting $`3a^2Q_2^2`$. The bounds follow from
$`0\le\xi/a\le1/3`$ at nontrivial row sizes and
$`d^2\le2(d-2)(d-3)`$ for $`d\ge10`$. Empty and full rows are deterministic.

Gauss–Lucas applies in the open left half-plane and gives a
holomorphic logarithm on $`|z|<\pi/(2M)`$. After complementing if needed,
the elementary symmetric mean bound and
$`e^w\le1+w+w^2`$ for $`|w|\le1`$ bound the real part by
$`2v|z|^2Q_2`$. The nonnegative function
$`2vQ_2/M^2-\Re K(z)`$ on $`|z|=1/M`$ has that same constant as its
mean, giving the factor four in the complex Taylor coefficient bound.
Real coefficients then give the stated separate even and unrestricted
tails. In summation $`\sum_i v_i\le\lambda`$, so no extra row factor
is needed. The displayed summed bounds and Gaussian consequences
require only $`d\ge10`$ and $`\lambda\ge d/5`$. In the claimed wider
window, $`v=x(1-x)\ge2s/9`$ and $`B/n\le\eta^2<s/50`$, so
$`\lambda\ge n(v-\eta^2)>d/5`$. Here $`\eta=n^{-1/4}`$.

For the cubic, the mixed Wick term is zero by the row sums of the
projection matrix. The sum of cubes of its entries is
$`(d-1)(d-2)/d`$, giving the claimed cosine lower bound.
For the quartic covariance, with $`P_{ij}`$ the projection entries,
the exact covariance of the fourth powers of the centered
unit-precision variables is
$`72(1-1/d)^2P_{ij}^2+24P_{ij}^4`$. Summing yields the $`96d`$ variance
bound. For $`X\sim\chi^2_{d-1}`$ the exact
$`\mathrm{Var}(X^2)=8(d-1)(d+1)(d+2)<16d^3`$ at $`d\ge10`$.
This confirms both contributions to the stated $`L^2`$ bound on $`\Pi`$.

## Fixed-profile integral and correction

With one angle fixed at zero, on the small-diameter chart all the
angles have unique representatives at distance at most $`\epsilon`$
from that angle. Their differences have magnitude at most $`2\epsilon<\pi`$,
so the circular-diameter constraint actually bounds all differences
by $`\epsilon`$. Centering yields $`M\le\epsilon`$. Conversely every
centered vector with $`M\le\epsilon/3`$ lies in this chart after fixing
the last angle. The constraint on the total row size cancels the
common phase. The fixed-last-angle precision has determinant
$`\lambda^{d-1}/d`$, and centering the Gaussian produces covariance
$`P/\lambda`$ as used in the argument.

The remainder calculation gives $`|\Re R_{\ast}|\le6n^{-2/5}<1`$
and $`\|R_{\ast}\mathbf1_{\mathcal C}\|_2\le8n^{-1/5}`$.
The centered Gaussian and its coordinate average are independent.
On the chart after inserting $`|\bar Z|\le1`$ one has
$`|Z_j|\le2n^{1/10}`$, so
$`tZ_j^4\le Z_j^2/4`$ for $`t=8/\lambda`$.
The normal moment used here is
$`\mathbb E[Z_j^4 e^{Z_j^2/4}]=3\cdot2^{5/2}<20`$.
Thus the displayed bound $`2e^{840}`$ follows without invoking any
untruncated quartic exponential moment. Cauchy–Schwarz then bounds the
difference of the exponentiated corrections by the displayed
$`e^{422}(8n^{-1/5}+16/\sqrt d)`$.
Using $`d\ge n^{.99}`$, the exponents $`0.02u`$ and $`0.315u`$ absorb
that prefactor at $`u\ge10^6`$. The Gaussian chart loss is below
$`n^{-10}`$ because $`\lambda\epsilon^2\ge n^{.19}/5`$, and the
input torus loss is below $`n^{-10}`$. Together these give an
additive error below $`n^{-.18}`$ in Gaussian units, while
$`K_{\ell}\ge(7/12)e^{-15/8}>1/16`$.

## Adjacent quotas and averaging

For the continuous polynomial formulas in $`p`$, one has
$`|a'|\le10/9`$ and $`|\gamma'|\le (d/(d-2))(|a'|+2a)<5`$.
Differentiating the stated expression for $`dB_4`$ gives
$`d a'[2(4d-6)a-(d-1)]/[(d-2)(d-3)]`$, below $`20`$ in
absolute value. Then $`|A_4'|\le |a'|(1+12a)+6|B_4'|<30`$.
These bounds also apply along segments ending at $`p=0`$ or $`p=1`$.
Because each coupled coordinate increases and the total change in
the $`p_i`$ is one, summing costs just the derivative bounds.
Differentiating the cubic prefactor along the line segment costs
at most $`5^{3/2}(5+3)/(6d)<100/d`$. The quartic numerator varies
by at most $`50d`$ and is bounded by $`3d\lambda`$ along the segment.
The derivative of its quotient is therefore below $`1000/d`$.
The cosine factor has a positive uniform lower bound at both ends, so
the comparison of the correction factors and the subsequent logarithm
error $`64n^{-.18}`$ follow.

The scalar monotone coupling applies by log-concavity of the
capped binomial weights, including support endpoints. To check
the centered-square difference, both endpoint deviations are
at most $`\eta`$ and the sum of the absolute changes of the
deviations is at most $`1+n(1/n)=2`$. This gives
$`|B'-B|\le4\eta`$. The derivative of $`-\log(1-z)`$ on
$`[0,1/2]`$ is at most two. With $`v,v'\ge s/5`$, the resulting
determinant log variation is at most $`20\eta+25\eta^2/s`$ and
the determinant log itself is in $`[0,5B]`$. Together with the
fixed-profile factor bounds this gives the stated regular-pair estimate
and $`1/40\le H_k\le10e^{5B}`$ there.

Under the scalar law, tilted row sizes are dominated in convex
order by the binomial of the same mean. The common-mean
conditioning probability is at least $`1/(nd+1)`$ by interval
log-concavity and entropy. At saturation the row law is a point mass.
For the actual law, fixing all but two rows leaves the binary choices
only in the columns occupied in exactly one of those rows. Their
fair-binomial count is restricted to a symmetric central interval
by the equal row caps. This restriction decreases both gap tails.
The two stated bounds follow by Hoeffding and union bounds. The
actual law of the row profile is precisely the scalar law reweighted
by $`H_k/\mathbb EH_k`$.

For the second moment of $`H_k`$ restricted to regular profiles,
integrate the scalar Hoeffding tail to get
$`\mathbb E e^{10(S/d-x)^2}\le1+20/(2d-10)`$ per row.
Independence before conditioning and the conditioning lower bound
yield $`100(nd+1)e^{20n/d}\le n^3`$. For either marginal,
discarding its own irregular profiles loses at most $`t'`$ relative
mass by the actual-law estimate. Discarding profiles irregular only
in the other marginal loses at most $`80\sqrt{tn^3}`$ relative mass
by Cauchy–Schwarz. With $`d\eta^2\ge n^{.49}`$ their sum is below
$`1/n`$. Integrating the pointwise comparison on the common event and
restoring the two masses gives the log difference bounded by
$`n^{-1/6}+4/n<n^{-1/8}`$.

## Editorial fixes

Update the summed subsection of the row expansion to the current
aspect and cutoff, or replace that subsection's introductory
hypotheses by the sufficient bounds $`d\ge10`$ and $`\lambda\ge d/5`$.
The narrower working hypotheses there are obsolete.
The prior comparison link resolves from a sibling directory under
the public topic but is dangling in this scratch layout.

The published row expansion uses the broader hypotheses throughout. The local link to the earlier coupling proof resolves in the topic layout.
