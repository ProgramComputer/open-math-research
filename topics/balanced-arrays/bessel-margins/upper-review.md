# Independent audit of the fixed-profile Bessel upper bound

**Verdict.** The fixed-profile upper bound with exponent $72+\min(9e/d,58B)$ is valid. The initial scalar-coefficient consequence had incorrectly taken the profile-dependent $B$ outside the sum. The revised consequence takes a weighted expectation over profiles or uses $e^{9e/d}$ uniformly, which resolves that gap. No conclusion about real-rootedness follows from this one-sided estimate alone.

## Joint event, Bessel bounds, and far angles

Independent Bernoulli cells with a row's parameter $p_i=\ell_i/d$ give uniform independent $\ell_i$-subsets after conditioning on the row sums. The denominator is exactly the product of binomial mean masses, including unit factors at deterministic rows. Redundancy of the full margin coordinates does not change the Fourier orthogonality identity. One square root of the squared modulus bound gives the factor $\exp[-v_i(1-\cos(\phi_i+\theta_j))]$ per cell. The sum of cosines across the row has amplitude $R=|\sum_j e^{i\theta_j}|$, so integrating each row angle with normalized Haar measure gives $e^{-dv_i}I_0(v_iR)$.

For $J(z)=e^{-z}I_0(z)$, the short interval in the lower bound contributes at least $e^{-1/2}/(\pi\sqrt{1+z})>1/(6\sqrt{1+z})$. The cosine inequality gives $\sqrt\pi/(2\sqrt{2z})$ for the crude upper, which is at most $2/(3\sqrt z)$ and equals $(\pi/2)(2\pi z)^{-1/2}$ before relaxation. For the sharp bound, the derivative with respect to $u^2$ of $(1-u^2/4)^{-1/2}$ is at most $1/(2\sqrt2)<3/8$ for $u^2\le2$. Integrating the resulting quadratic factor against the half Gaussian gives $1+3/(8z)$ in the stated normalization. The discarded region has kernel at most $e^{-z}$ and normalized angle measure at most one. The function $\sqrt{2\pi}z^{3/2}e^{-z}$ decreases for $z\ge10$ and is less than $1/8$ there. Hence the sharp exponent $1/(2z)$ is justified.

Stirling gives the cost $1/(12dv_i)$ by dropping the positive numerator error and bounding the two denominator errors. For nondeterministic rows $dv_i\ge(d-1)/d\ge249/250$ and $v_i\le1/4$; even replacing the first by $1/2$ proves $b_i\ge(3\sqrt d)^{-1}$. On $R<d/2$ this and $I_0(v_iR)\le e^{v_iR}$ give the direct bound $(3\sqrt d)^n e^{-Ad/2}$. The displayed comparison against $(2n)^{-d/2}$ follows from $A\ge3n/20$, $n/4\le d\le n$, and $\log(5n)<3n/160$ for $n\ge1000$. The latter inequality holds at 1000 and its gap increases. Thus there is no omitted angular region or loss of the Gaussian scale from the far torus.

## Aligned-region constants

Writing $A_0=nx(1-x)$ and $\Delta=e/(nd)$, the variance loss is $\sum_i(p_i-x)^2=B-n\Delta^2$. The cap also gives $\sum_i p_i^2\le(x+\Delta)nx$, so the loss is at most $\min(B,xe/d)$, and $A\ge3n/20$. Each bad row has $x-p_i\ge1/10$ and $r/d-p_i\ge1/10$, which gives the stated count estimates $10e/d$ and $100B$. In the regime at hand $p_i\le0.81$, so a full row is impossible. The row-factor derivation itself handles both deterministic endpoints.

For good rows $v_iR\ge(9/100)d/2\ge11.25$; the exponent total is at most $4(13/12)(100/9)=1300/27<49$. For the other nondeterministic rows, $\log(\pi/2)+250/(12\cdot249)<27/50$ follows from $\pi<22/7$ and the cubic Taylor lower sum for $\exp(27/50-250/(12\cdot249))$. This yields the exact two bad-row costs $27e/(5d)$ and $54B$. The square-root factors are absorbed by $\frac12\log(d/R)\le(d-R)/d$ on $R/d\ge1/2$, leaving $A'=A-n/d\ge7n/50$.

The common-angle average $\int I_0(A'R)\,d\theta=I_0(A')^d$ follows by Fubini and periodicity. The lower Bessel bound costs at most $6\sqrt{nd}$, because $R\le d$ and $1+A'd\le nd$. For the remaining exponent, $d/(2A')\le25/7<4$, and

$$
\frac d2\log(A_0/A')
\le\frac d{2A'}\left(\min(B,xe/d)+n/d\right)
<15+\min(3e/d,4B).
$$

In fact the constant term here is at most $25/7$, and the coefficient in $e/d$ is at most $(25/7)(4/5)=20/7<3$. Combining with the bad-row costs uses $\min(a,b)+\min(c,d)\le\min(a+c,b+d)$, leaving at most $\min(9e/d,58B)$. The total constant is at most $49+\log6+4+15<70$. Adding the far-region bound keeps the exponent below $72$.

To remove $B$ uniformly while retaining a potentially smaller exponent than $9e/d$, write $e=qr+s$ with $0\le s<r$ and $r>0$. Convexity of the square gives $B\le(qr^2+s^2)/d^2$, achieved by filling the largest allowable deficits first. In particular $B\le\min((e/d)^2,(r/d)(e/d))$. The weighted expectation in the amended consequence preserves the actual spread of profiles.

## Attribution and scope

Canfield–Greenhill–McKay Theorem 1 and Sections 2–5 use the same multivariate coefficient-extraction setting, a detailed saddle expansion and an exterior modulus estimate. They give an asymptotic formula with a binomial-product baseline and density/variance correction. For comparable dimensions and density bounded away from zero and one, the hypothesis still requires every row deviation to be $O(d^{1/2+\varepsilon})$ and every column deviation to be $O(n^{1/2+\varepsilon})$, for sufficiently small $\varepsilon$. Such a condition does not follow from a relative near-saturation sum bound on the row deficits. I found no $I_0$ step in their proof. [Canfield–Greenhill–McKay, Theorem 1 and §5](https://web.maths.unsw.edu.au/~csg/papers/CGM.pdf)

Barvinok–Hartigan Section 2.5, equation (2.5.4), and Section 11 use the same joint Bernoulli Fourier integrand, with a pinned angular coordinate and explicit Gaussian, cubic and quartic contributions. In this equal-column model, the entropy maximizer is row-constant with entries $p_i$, by symmetry. Their theorem for $\delta$-tame margins applies for comparable large dimensions and $p_i\in[\delta,1-\delta]$. The pinned covariance determinant is $A^{d-1}\prod_i(dv_i)/d$, by taking the Schur complement of the row block $d\,\mathrm{diag}(v_i)$. Dividing the joint Gaussian term by the row masses in that tame range yields the scale $\sqrt d\,(2\pi A)^{-(d-1)/2}$ up to bounded factors when $d\asymp n$. This agrees with the polynomial/Gaussian scale of the upper bound after identifying $A\asymp A_0$, with the variance loss retained in the exponent. Their theorem is asymptotic and does not directly cover uniformly arbitrary thin nondeterministic rows. I found no row-angle $I_0$ integration in their proof. [Barvinok–Hartigan, §§2.5 and 11](https://dept.math.lsa.umich.edu/~barvinok/degree.pdf)

Liebenau–Wormald use switching and contraction methods for fixed-degree enumeration in different parameter regimes. The Bessel half of the search also found DeSalvo's approximation for $2\times c$ arrays conditioned on a row-sum difference with free column sums, which does not give the fixed-column balancing bound. Bessel powers for sums of planar unit steps are classical, as in the Kluyver representation discussed by Borwein–Straub–Wan–Zudilin. The common-angle identity here is its elementary moment-generating counterpart. The bounded source search did not find the precise finite row-angle Bessel majorant in binary-margin enumeration. This is neither a comprehensive literature survey nor a priority claim. [Liebenau–Wormald](https://doi.org/10.1002/rsa.21105) · [DeSalvo](https://arxiv.org/abs/2611.00263) · [Borwein–Straub–Wan–Zudilin](https://doi.org/10.4153/CJM-2011-079-2)

**Signed** — four_literature, independent agent-assisted mathematical review.
