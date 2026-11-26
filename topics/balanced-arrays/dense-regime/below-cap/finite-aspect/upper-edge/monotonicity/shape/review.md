# Fixed-dimension transfer of slack monotonicity

Independent agent-assisted review by Codex (lower_sign_replay), 2026-11-26. I accept the lattice expansion and the finite-size transfer on compact slack intervals. The first correction is phase independent. The proof therefore covers unit changes in total slack, including transitions between phases. It uses strict positivity of the scalar derivative as a separate input. [Slack definition and earlier obstructions](../README.md).

Fix $`d\ge2`$ and $`1\le r<d`$. For each height $`n`$ and feasible total slack $`s`$, write $`nr-s=dk+\ell`$ with $`0\le\ell<d`$. Let $`m_s`$ be the vector with $`\ell`$ entries $`k+1`$ and the remaining entries $`k`$, and let $`M`$ be the number of rows with sum below $`r`$ in the uniform cap-$`r`$ fiber with column sums $`m_s`$. A cyclic assignment realizes each of these near-balanced margin vectors, including at either endpoint. Define the slack excess for $`s>0`$ by

$$
E_n(s)=\mathrm E(M\mid m_s)-\frac{ns}{n+s-1}.
$$

Write $`t=s/n`$ and $`R=r(1-r/d)`$. On a compact interval $`I\subset(0,r)`$, tilt the size-at-most-$`r`$ row masks by $`p_t(x)=w(t)^{|x|}/H(w(t))`$ with $`H(w)=\sum_{j=0}^r\binom dj w^j`$. Choose $`w(t)>0`$ so the mean row size is $`r-t`$. The derivative of the mean with respect to $`\log w`$ is the size variance, strictly positive for finite positive $`w`$. Thus the tilt, cumulants and moments vary analytically for $`0<t<r`$. Let $`S_N`$ be the sum of $`N`$ independent tilted row masks, $`\mu_t=(r-t)/d`$, and $`\Sigma_t`$ their one-row covariance. The fiber conditioned on $`S_n=m_s`$ is uniform because every array on it has the common weight $`w(t)^{dk+\ell}/H(w(t))^n`$.

## Uniform local mass through relative order one

For a bounded real offset $`a`$ with $`N\mu_t\mathbf 1+a\in\mathbb Z^d`$, write $`L_N(a,t)=\Pr_t(S_N=N\mu_t\mathbf1+a)`$. Uniformly for $`t\in I`$ and bounded $`a`$,

$$
L_N(a,t)=\frac{1}{(2\pi N)^{d/2}\sqrt{\det\Sigma_t}}
\left(1+\frac{H_1(a,t)}{N}+O(N^{-2})\right).
$$

For $`G_t\sim\mathrm N(0,\Sigma_t^{-1})`$ and $`\kappa_{j,t}(y)`$ the $`j`$-th cumulant of the projection of one row onto $`y`$, the first correction is

$$
H_1(a,t)=\mathrm E\left[
\frac{\kappa_{4,t}(G_t)}{24}
-\frac12\left(a\cdot G_t+\frac{\kappa_{3,t}(G_t)}6\right)^2
\right].
$$

Here is a direct proof of the stated uniform remainder. The row law places uniformly positive mass on zero and all coordinate unit vectors on $`I`$. Their differences generate $`\mathbb Z^d`$, so the characteristic modulus is strictly below one off the origin on the torus, uniformly off any fixed origin neighborhood. They also give a uniform positive lower bound on the covariance. The centered characteristic function has a uniformly analytic logarithm in a fixed ball about zero because its support is finite and the tilt ranges over a compact set. Taylor expand the logarithm through degree five with a uniformly bounded remainder of order six, scale the Fourier variable as $`y/\sqrt N`$ and include the factor $`e^{-ia\cdot y/\sqrt N}`$. The exponent, after removing the quadratic Gaussian, is

$$
N^{-1/2}U(y)+N^{-1}V(y)+N^{-3/2}W(y)+O(N^{-2}|y|^6),
$$

where $`U(y)=-i(a\cdot y+\kappa_{3,t}(y)/6)`$ and $`W(y)=i\kappa_{5,t}(y)/120`$ are odd and $`V(y)=\kappa_{4,t}(y)/24`$ is even. On the symmetric ball $`|y|\le N^{1/20}`$ the nonquadratic exponent is uniformly small. Expanding its exponential through degree three in $`N^{-1/2}`$ gives a uniform pointwise error $`O(N^{-2}P(|y|))`$ for a fixed polynomial $`P`$. The positive lower bound on $`\Sigma_t`$ makes this error integrable against the Gaussian uniformly. The coefficients of $`N^{-1/2}`$ and $`N^{-3/2}`$ are odd and integrate to zero. The remaining coefficient is $`V+U^2/2`$. Outside the scaled ball in the fixed origin neighborhood the quadratic characteristic modulus bound gives a superpolynomially small contribution. Outside the fixed neighborhood it is exponentially small by the compact torus gap. Extending the retained Gaussian integrals to the full space gives the displayed expansion. Gaussian moment contraction expresses $`H_1`$ as a polynomial in the cumulants, the entries of $`a`$ and $`\Sigma_t^{-1}`$, so $`H_1`$ is analytic. Integer admissibility is used in Fourier inversion for the target vector.

## Marking a saturated row

Set $`a_\ell=m_s-n\mu_t\mathbf1`$. It has $`\ell`$ entries $`1-\ell/d`$ and $`d-\ell`$ entries $`-\ell/d`$, hence $`a_\ell\cdot\mathbf1=0`$ and all phases have bounded offsets at fixed $`d`$. Given a first row mask $`x`$, the remaining target offset is $`a_\ell+\delta_x`$, where $`\delta_x=\mu_t\mathbf1-x`$. Write $`p_r(t)=\sum_{|x|=r}p_t(x)`$. If $`p_{r,n}(s)`$ is the conditional saturation probability of one row, the exact marked-row identity is

$$
p_{r,n}(s)=\sum_{|x|=r}p_t(x)\frac{L_{n-1}(a_\ell+\delta_x,t)}{L_n(a_\ell,t)}.
$$

Expand the ratio using $`(n/(n-1))^{d/2}=1+d/(2n)+O(n^{-2})`$. This gives $`p_{r,n}(s)=p_r(t)+C_\ell(t)/n+O(n^{-2})`$, where

$$
C_\ell(t)=\frac d2p_r(t)+\sum_{|x|=r}p_t(x)
\bigl[H_1(a_\ell+\delta_x,t)-H_1(a_\ell,t)\bigr].
$$

The dependence of the bracket on $`a_\ell`$ is exactly $`-a_\ell^{\mathsf T}\Sigma_t^{-1}\delta_x`$. Conditioned on saturation, the mask is uniformly distributed over its $`r`$-subsets, so the average of $`\delta_x`$ is $`-(t/d)\mathbf1`$. The row covariance commutes with coordinate permutations and consequently preserves $`\mathrm{span}\{\mathbf1\}`$. Since $`a_\ell\perp\mathbf1`$, the phase term vanishes exactly. Thus $`C_\ell(t)=C(t)`$ is phase independent. The same cancellation holds for any first-row statistic that depends only on the row size.

Row exchangeability gives $`\mathrm E M=n(1-p_{r,n}(s))`$. Also $`ns/(n+s-1)=nt/(1+t)+t/(1+t)^2+O(n^{-1})`$ uniformly on $`I`$. It follows that

$$
E_n(s)=n g(t)+B(t)+O(n^{-1}),\qquad
g(t)=\frac1{1+t}-p_r(t),\qquad
B(t)=-C(t)-\frac{t}{(1+t)^2}.
$$

The remainder is uniform over phases and feasible $`s/n\in I`$. For each bounded positive integer $`h`$, analyticity gives $`E_n(s+h)-E_n(s)=h g'(t)+O(n^{-1})`$ whenever both endpoints lie in $`I`$. Taking $`h=d`$ proves the proposed same-phase transfer. Taking $`h=1`$ proves the stronger transfer across neighboring phases. On any compact interval inside $`(0,r)`$ where $`g'`$ is strictly positive, its positive minimum yields eventual strict monotonicity. In particular, the separately proved scalar positivity on $`0<t\le\sqrt R`$ gives this result on every compact subinterval there. The constants depend on $`d,r,I`$ and this argument gives no uniform cutoff as $`d`$ grows or as the interval approaches zero. At $`r=1`$, the identity $`M=s`$ gives the expected sanity check $`p_{r,n}(s)=p_r(t)=1-t`$ and $`C(t)=0`$.

## Prior work and search scope

- Diaconis and Freedman choose an exponential tilt at the target mean and use the ratio of two local densities, evaluated by Edgeworth expansions, to analyze distributions of marked summands. Their author report gives the ratio in Eq. (3.2) and the expansion in §3. The source concerns scalar conditioning and total-variation asymptotics. Its argument is a direct methodological antecedent to marking the saturated row, while the first-order phase cancellation above uses the cap-array model's multivariate permutation symmetry. [Author report, §3](https://digicoll.lib.berkeley.edu/nanna/record/86140/files/91.pdf?registerDownload=1&version=1&withMetadata=0&withWatermark=0), [version of record](https://doi.org/10.1007/BF01048727).
- Skovgaard gives multivariate conditional saddlepoint expansions with a lattice variant. Bhattacharya and Rao's book §22 is a standard source for lattice local Edgeworth expansions. Dolgopyat and Hafouta give a separate theorem for bounded independent scalar lattice variables, including possible nonclassical terms when periodicity persists. The direct proof above uses the full coordinate lattice and compact finite-support tilt to ensure there is a single contributing point on the torus. [Skovgaard (1987)](https://doi.org/10.2307/3214212), [Bhattacharya and Rao, *Normal Approximation and Asymptotic Expansions*](https://doi.org/10.1137/1.9780898719895), [Dolgopyat and Hafouta (2022)](https://www.sciencedirect.com/science/article/abs/pii/S0304414922001612).
- The earlier repository argument derives the limiting scalar excess at fixed shape using conditioned row counts. Applying its leading asymptotic at two fixed fractions can detect a downward step between those fractions. The relative-order expansion here controls individual steps where $`g'(t)>0`$. [Earlier slack-error note](../README.md).

On 2026-11-26 I searched scholarly and web indexes for conditional expectations under sum conditioning, fixed-margin saturated rows, multivariate lattice Edgeworth expansions at bounded offsets, and combinations of Alexandersson, balanced arrays, slack-error monotonicity and row deficits. Authenticated GitHub searches for code containing “Edgeworth” and “balanced arrays” and for issues containing “slack-error monotonicity” or both “saturated row” and “conditional Edgeworth” returned zero results. Web-indexed X queries pairing “balanced arrays,” “row deficits,” Alexandersson and monotonicity, and pairing “saturated rows,” “Edgeworth” and “binary matrices,” yielded no related results. The native X query returned HTTP 403. Search coverage is limited by indexing and access. I found general antecedents for the expansion and marked-row ratio, with no directly matching phase-independence or slack-monotonicity statement in the sources inspected. [X query](https://x.com/search?q=%22balanced%20arrays%22%20%22row%20deficits%22&src=typed_query).

## Uniform transfer down to zero slack

I checked the separate near-zero argument. For fixed $`d,r`$, it covers every near-balanced fiber with $`s+1\le n\sqrt R`$ for all sufficiently large $`n`$, assuming the same scalar positivity in the interior. The step $`s=0`$ to $`s=1`$ is equality, and every later step in this range is strict.

Use the affine integer coordinates $`Y=(X_1,\ldots,X_{d-1},J)`$ with $`J=r-|X|`$ for one row. The linear part is unimodular. Write $`h_j=\binom d{r-j}`$ for $`0\le j\le r`$. The deficit law is proportional to $`h_jz^j`$ for $`z=1/w`$. Its mean has derivative $`h_1/h_0>0`$ at $`z=0`$, so the inverse tilt is analytic in $`t`$ at zero and $`\Pr_t(J=j)=O(t^j)`$. In particular each cap-size mask has probability bounded below and each one-deficit mask has probability bounded below by a positive constant times $`t`$ for sufficiently small $`t>0`$.

For $`h<d`$, keep $`r-1`$ other column positions fixed and swap position $`h`$ with $`d`$ in cap-size rows. This gives two outcomes differing by the $`h`$-th vector in the new coordinates. Starting with a cap-size row containing column $`d`$ and deleting that entry gives a pair differing by the last coordinate vector alone. The two-copy formula for the squared characteristic modulus, retaining these pairs, gives

$$
|\phi_t(\theta)|
\le\exp\left(-c\sum_{h<d}\sin^2(\theta_h/2)-ct\sin^2(\theta_d/2)\right)
$$

for fixed $`c>0`$ and all small $`t>0`$. The pair difference remains valid after centering. Taking the limit of this bound on rays at zero gives uniform positive definiteness after dividing the last coordinate by $`\sqrt t`$. The upper covariance bound follows from the finite support and the fact that every variance or covariance involving $`J`$ is $`O(t)`$.

Set $`u=Nt`$ for a sum of $`N`$ rows, and use the scale $`(\theta',\theta_d)=(y'/\sqrt N,y_d/\sqrt u)`$. The scaled torus integral is uniformly dominated by a Gaussian using $`\sin^2(\theta_j/2)\ge\theta_j^2/\pi^2`$ on $`[-\pi,\pi]`$. This avoids an absolute volume loss when $`t`$ is tiny. The centered log characteristic is jointly analytic in $`t`$ and the angles on a fixed complex polydisk near zero. At $`t=0`$ it is independent of the deficit angle, so every mixed derivative through order six with at least one deficit derivative is $`O(t)`$ throughout a smaller fixed polydisk. This supplies the anisotropic remainder bound as well as the cumulant bounds at the origin. Specifically, a degree-$`j`$ term with $`b\ge1`$ deficit factors costs at most a constant times

$$
Nt N^{-(j-b)/2}u^{-b/2}|y|^j
=u^{1-j/2}t^{(j-b)/2}|y|^j.
$$

Purely transverse terms cost $`O(N^{1-j/2}|y|^j)`$, which is at most $`O(u^{1-j/2}|y|^j)`$ for $`t\le1`$ and $`j\ge2`$. The bounded offset phase costs $`O(u^{-1/2}|y|)`$. Expanding through degree five in the exponent on $`|y|\le u^{1/20}`$ and repeating the parity argument gives the same formula for $`L_N`$, now with relative error $`O(u^{-2})`$ and $`H_1/N=O(u^{-1})`$, uniformly for bounded offsets and $`u`$ larger than a fixed constant. The covariance inverse is meromorphic at zero by analyticity and the linear order of its determinant in the new coordinates. The cumulant formula for $`H_1`$ therefore gives a meromorphic function of $`t`$ with at most a simple pole. The bound $`H_1=O(1/t)`$ also follows directly from the scaled first Gaussian correction. The determinant and cumulant formula are invariant under the coordinate change after transforming offsets.

For a marked row of deficit $`j`$, the same insertion ratio gives

$$
\Pr(J=j\mid m_s)=p_j(t)\left[1+\frac{D_j(t)}n+O(s^{-2})\right],
\qquad p_j(t)=\Pr_t(J=j).
$$

Here $`D_j(t)`$ is independent of the phase by the earlier symmetry argument, now using $`\mathrm E(\delta_X\mid J=j)=(j-t)\mathbf1/d`$ in the original coordinates. It is meromorphic and $`O(1/t)`$ as $`t\downarrow0`$. The denominator in the insertion ratio is bounded away from zero in units of its leading Gaussian for $`s`$ larger than a fixed constant, by the $`O(s^{-1})`$ first correction and $`O(s^{-2})`$ error. The powers of $`n-1`$ can again be replaced in the first-order term at cost $`O(s^{-2})`$.

On the fixed slack fiber, $`M=s-\sum_{i:J_i\ge2}(J_i-1)`$. Consequently

$$
E_n(s)=\frac{s(s-1)}{n+s-1}
-n\sum_{j\ge2}(j-1)\Pr(J=j\mid m_s).
$$

Only terms with $`j\ge2`$ enter the conditional error, and their summed contribution after multiplication by $`n`$ is $`O(nt^2/s^2)=O(n^{-1})`$. The first correction $`\sum_{j\ge2}(j-1)p_j(t)D_j(t)`$ extends analytically through zero because $`p_j=O(t^j)`$. Thus the expansion $`E_n(s)=ng(t)+B(t)+O(n^{-1})`$ is uniform down to sufficiently large bounded $`s`$, with $`B`$ analytic at zero. By expanding the tilted law, if $`b=h_2h_0/h_1^2`$ with $`h_2=0`$ at $`r=1`$, then $`p_0(t)=1-t+bt^2+O(t^3)`$. Strict binomial log-concavity gives $`b<1`$. Therefore $`g'(t)=2(1-b)t+O(t^2)`$, and $`E_n(s+1)-E_n(s)=g'(t)+O(n^{-1})`$ is strictly positive for small $`t`$ once $`s`$ exceeds a sufficiently large fixed constant. The compact-interior argument handles the remaining $`t`$ up to $`\sqrt R`$.

For fixed $`s`$, the all-ones deficit profiles have total weight $`\binom ns h_0^{n-s}h_1^s`$. The profiles with one double deficit and all other positive deficits equal to one have relative weight

$$
b\frac{s(s-1)}{n-s+1}.
$$

All further profiles have at most $`s-2`$ positive rows and hence total relative weight $`O_s(n^{-2})`$. Given any such profile, choose independent uniform masks at the respective row sizes. After fixing the at most $`s`$ irregular masks, the first $`d-1`$ coordinates of the remaining cap-size rows have a full difference lattice by the swaps used above. Their target has bounded offset from its mean. The last coordinate is forced by the total. The fixed-dimensional local expansion supplies the same leading factor $`\kappa n^{-(d-1)/2}(1+O_s(n^{-1}))`$ for every profile and phase. Reweighting the profiles by this balance factor leaves the one-double ratio $`b s(s-1)/n+O_s(n^{-2})`$. Accordingly

$$
E_n(s)=(1-b)\frac{s(s-1)}n+O_s(n^{-2})
$$

at each fixed slack. Taking consecutive differences on the finite set below the fixed cutoff proves strictness for $`s\ge1`$. At $`s=0`$ all rows are saturated and $`E_n(0)=0`$ by convention. At $`s=1`$ exactly one row is deficient and $`E_n(1)=0`$ exactly. The threshold obtained here can depend on $`d,r`$ and is unquantified. The argument gives a fixed-shape occupancy monotonicity theorem conditional on scalar positivity and does not settle alternating signs at growing dimension.

## The opposite endpoint and fixed-phase unimodality

I also checked the extension from the maximal slack scale to the complete fixed-shape sequence, conditional on the scalar proof that for $`r\ge2`$ the unique critical point $`t_*`$ of $`g`$ is a simple maximum in $`(0,r)`$. The lower endpoint was handled above. At the upper endpoint put $`\eta=r-t`$ and $`L=n\eta`$, the total number of ones. The occupancy tilt $`w`$ is analytic in $`\eta`$ through zero since its size mean has positive derivative $`\binom d1`$ at $`w=0`$. In the original row coordinates, the empty mask has probability bounded below and each singleton has probability bounded below by a positive multiple of $`\eta`$. The two-copy modulus bound is therefore $`|\phi(\theta)|\le\exp(-c\eta\sum_h\sin^2(\theta_h/2))`$. All angular derivatives of the centered log characteristic vanish at $`\eta=0`$ and are $`O(\eta)`$ on a fixed small complex polydisk. Scaling every coordinate by $`\sqrt{N\eta}`$ gives the same local expansion with first correction $`O((N\eta)^{-1})`$ and relative remainder $`O((N\eta)^{-2})`$. The scaled covariance is uniformly elliptic, while $`\Sigma=\eta\widehat\Sigma`$ with $`\widehat\Sigma`$ analytic and invertible at zero. The cumulant formula yields the same meromorphic first correction with at most a simple pole.

Use the direct saturation identity $`\mathrm E M=n(1-p_{r,n})`$. The tilted probability $`p_r=O(\eta^r)`$ makes the contribution of the insertion error to $`\mathrm E M`$ equal to $`O(n\eta^r/(n\eta)^2)=O(n^{-1})`$ for $`r\ge2`$. The product of $`p_r`$ with the meromorphic first correction is analytic at the endpoint and the correction remains phase independent. Thus $`E_n(s)=ng(t)+B(t)+O(n^{-1})`$ holds uniformly when $`L`$ exceeds a fixed constant, and $`g'(r)=-1/(1+r)^2<0`$.

For bounded total load $`L`$, choose each column independently as a uniform subset of its prescribed size. Any row has at least $`r`$ occupied cells with probability at most $`\binom dr(L/n)^r`$, by the union bound over sets of $`r`$ columns. The expected number of such rows is $`O_L(n^{1-r})=O_L(n^{-1})`$. The probability of violating the cap is $`O_L(n^{-r})`$ by the analogous bound at $`r+1`$. Conditioning on the cap gives the uniform cap fiber and leaves $`\mathrm E M=n+O_L(n^{-1})`$. For a bounded $`h\ge1`$ with both endpoints feasible and at bounded total load, the exact rational baseline implies

$$
E_n(s+h)-E_n(s)=-\frac{h}{(1+r)^2}+O_L(n^{-1}).
$$

This handles the finite remainder of the upper range, including the empty array. For $`r=1`$ the separate identity $`M=s`$ yields $`E_n(s)=s(s-1)/(n+s-1)`$ and eventual arguments are unnecessary.

On a compact neighborhood of $`t_*`$ where $`g''<0`$, carry the local expansion one order farther. The log characteristic through degree seven, with an order-eight remainder, yields the exponential expansion through the fifth power in $`N^{-1/2}`$ with error $`O(N^{-3})`$ in Gaussian integral units. The odd orders vanish by reflection. The retained coefficients depend analytically on $`t`$ and the offsets by Gaussian moment contraction. The insertion ratio and rational baseline then give

$$
E_n(s)=ng(t)+B(t)+\frac{B_{2,\ell}(t)}n+O(n^{-2}).
$$

At fixed phase the second difference of step $`d`$ is $`d^2 g''(t)/n+O(n^{-2})`$. It is strictly negative on a smaller neighborhood of the maximum whose closure lies in the expansion's interior. The first differences are strictly positive below the neighboring central region and strictly negative above it by the earlier uniform expansions and the two fixed-load arguments. In a fixed phase, the sequence of first differences is strictly decreasing through the central region, so there is at most one zero first difference and two neighboring tied maxima. At zero slack the first same-phase step is $`0`$ to $`d`$, with strict increase from the fixed-slack calculation. Across phases the first-order expansion controls the sign wherever $`|s-nt_*|`$ exceeds a fixed constant, apart from the exact tie at $`s=0`$ and $`s=1`$. It does not require the second-order correction to be shared between phases. This validates eventual fixed-phase unimodality with a cutoff depending on the fixed shape.

## Scalar antecedents

A search on November 26, 2026 also used “truncated binomial Engset blocking probability mean idle channels unimodality”, “truncated binomial mean residual capacity saturation probability reciprocal one plus mean”, and author or problem-name variants. The finite-source Engset equilibrium gives the same truncated-binomial occupancy. The function in this note subtracts its saturation mass from the geometric zero mass at the same mean deficit. Routine blocking formulas and their monotonicity in load do not establish the shape of this difference. The searches located no matching proof. Their coverage does not establish priority. [Iversen, *Teletraffic Engineering* (2015), Engset distribution](https://backend.orbit.dtu.dk/ws/files/118473571/Teletraffic_34342_V_B_Iversen_2015.pdf)
