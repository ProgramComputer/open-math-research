# Mixed angular and geometric test radii

At bounded aspect, the interface has a quantitative ordering rule. The previous finite sign tests leave a coverage gap at aspect four, including a cap-transition family. Actual reversal of two sign-correct radii occurs at aspect 72. [Existing overlap reduction](../../../effective-sublinear/angular-overlap.md) · [Bounded-aspect signs](../README.md) · [Fixed lower quotas](../../edges/fixed-lower-quota-signs.md)

**Formal verification**　⬜ None. The proof has independent agent-assisted review. The finite replay uses exact rational arithmetic and the existing dyadic enclosures for the phase nodes. [Review](review.md)

## Quantitative interface rule

Write $a_j$ for the balanced-array coefficients, $D=\lfloor nr/d\rfloor$, $c_j=a_{j-1}/a_j$ for $1\le j\le D$, and $b_j=\log(c_{j+1}/c_j)$ for internal $j$. The coefficients are positive on $[0,D]$. The orientation inequality yields

$$
b_j\ge d\left(\frac1{j+1}+\frac1{n-j+1}\right)\ge\frac{4d}{n+2}>0.
$$

The first inequality is from normalized log-concavity. [Orientation inequality](../../../orientation-normalization.md)

The geometric radius is $t_j=\sqrt{c_jc_{j+1}}$. For the exact angular radius $u_j=w_j^d$, define the ratios of the neighboring term magnitudes by

$$
L_j=\frac{a_{j-1}}{a_j u_j}=\frac{c_j}{u_j},
\qquad R_j=\frac{a_{j+1}u_j}{a_j}=\frac{u_j}{c_{j+1}}.
$$

The identity $L_jR_j=e^{-b_j}$ gives three equivalent tests for dominance of the central term.

$$
\max(L_j,R_j)<1
\quad\Longleftrightarrow\quad c_j<u_j<c_{j+1}
\quad\Longleftrightarrow\quad \bigl|\log(u_j/t_j)\bigr|<b_j/2.
$$

The geometric radii always lie in their own intervals $(c_j,c_{j+1})$. If each chosen angular radius satisfies the same interval condition, then any mixed selection is strictly ordered. The exact separation identities hold whenever the corresponding geometric neighbor exists.

$$
\log(u_j/t_{j-1})=b_{j-1}/2-\log L_j,\qquad
\log(t_{j+1}/u_j)=b_{j+1}/2-\log R_j.
$$

In particular, dominance leaves a logarithmic separation at least $2d/(n+2)$ at either mixed seam. When $n/d\le K$ and $n\ge2$, this is at least $1/K$. Direct mixed ordering needs only $L_j<e^{b_{j-1}/2}$ or $R_j<e^{b_{j+1}/2}$ on the relevant side. Hence these formulae can also be used when the angular term narrowly fails to dominate.

The bounded-aspect proof gives $L_j,R_j\to e^{-s_0/(2v_0)}$ along the proportional-variance subsequences, where $s_0$ is the limit of $d/n$ and $v_0$ the limit of $V/d$. Since $v_0\le1/4$, this limit is at most $e^{-2/K}$. The two remaining variance cases give both ratios tending to zero. This yields eventual dominance uniformly on compact interior density and aspect ranges, with an existential height cutoff. The explicit rare-overflow estimate gives both ratios at most $e^{-.499}$ under its stated hypotheses. The fixed-quota proof gives both ratios tending uniformly to zero at fixed quota as dimension grows.

For an effective geometric edge reduction, take $K>1$, $n/d\le K$, and $n\ge6K$. At any internal $j$ with $\min(j,n-j)/n\le1/(2K)$, the baseline gives $b_j\ge2n/(n+2K)\ge3/2>\log4$. The signed geometric test applies for every cap in these density ranges. Therefore a quantitative version of the bounded-aspect interior sign and dominance estimate on $[1/(2K),1-1/(2K)]$ would suffice for an all-cap conclusion. For $K=4$ this leaves a central estimate on $[1/8,7/8]$.

## A finite point outside the previous criteria

Take $(n,d,r,k)=(10^6,250000,127000,500000)$. Here $k$ and both neighbors are internal, and the cap is strictly between one and $d$. For uncapped arrays at quota $i\in\lbrace k-1,k,k+1\rbrace$, a row has a binomial load with $d$ trials and probability $i/n$. Put $q_i=a_i/\binom ni^d$. Hoeffding and the union bound give

$$
q_i\ge 1-n\exp[-2d(r/d-i/n)^2]>1-1/n.
$$

The last inequality holds because twice $d$ times the square of the smallest gap is greater than 30, and $e^{30}>10^{12}$ by a Taylor lower bound $e^5>100$. Therefore the *actual* geometric curvature satisfies

$$
\frac{a_k^2}{a_{k-1}a_{k+1}}
\le\frac{(1+2/n)^{n/2}}{(1-1/n)^2}
<\frac{3}{(1-1/n)^2}<4.
$$

The actual coefficients thus fail the factor-four sufficient test. At the same node,

$$
0<\frac d2\left(\frac rd-\frac{k+3}{n}\right)^2<8<\log n,
$$

so the previous finite angular lemma fails its overflow hypothesis. The compact-interior theorem has an existential cutoff, and the fixed-quota theorem controls fixed $k$ as dimension grows. The aspect lies below the earlier effective linear all-cap threshold $d/n\ge59/200$, and the height is below the earlier effective sublinear all-cap height threshold. The finite point remains in a small-overflow regime. Even at binomial parameter $(k+3)/n$, the union bound over all rows is below $10^{-6}$, since $2d(r/d-(k+3)/n)^2>30$.

## The cap-transition gap persists even for a stronger rare-event comparison

Let $d$ grow through even squares, $n=4d$, $k=n/2$, and $r=d/2+2\sqrt d$. For $d>16$ the cap is proper and the degree is $D=k+8\sqrt d$. This gives $d/n=1/4$, density $k/n=1/2$, and every fixed offset from $k$ feasible eventually. The cap is four standard deviations above the uncapped mean at quota $k$. The previous rare-overflow condition fails for all sufficiently large parameters. The fraction of uncapped arrays that obey the cap tends to zero.

To see this, under independent uniform column supports of quota $k$, the probability $p_d$ of overflow for one row tends to $1-\Phi(4)>0$. The overflow indicators of two rows have nonpositive covariance. Conditional on the first row, each second-row cell has success probability $(k-1)/(n-1)$ or $k/(n-1)$ according as the first-row cell is one or zero. The conditional overflow probability decreases with the first row's load, since columns remain independent and the conditional law depends only on that load. Its covariance with first-row overflow is therefore nonpositive. If $M$ counts overflowing rows, $\mathrm{Var}(M)\le np_d$ and

$$
a_k/\binom nk^d=\Pr(M=0)\le (np_d)^{-1}\longrightarrow0.
$$

The geometric curvature remains below the factor-four threshold eventually in this family. For the cap-conditioned tilt to mean $d/2$, write the underlying binomial parameter as $p=1/2+v_d/\sqrt d$. For a binomial row size $S$ at parameter $1/2+v/\sqrt d$, the scaled variable $(S-d/2)/\sqrt d$ converges to a normal distribution of mean $v$ and variance $1/4$. Conditional on the cap, its limit is the same normal distribution restricted to $(-\infty,2]$. The first two moments converge because the scaled binomial has uniformly bounded fourth moment. The same argument applies along any convergent sequence of $v$ in $[0,1/2]$. Writing $\alpha=2(2-v)$ and $\lambda=\phi(\alpha)/\Phi(\alpha)$, the truncated normal mean is $v-\lambda/2$. It is negative at $v=0$ and positive at $v=1/2$. Strict monotonicity of the cap-conditioned binomial mean in its tilt puts $v_d$ in $(0,1/2)$ eventually.

At every convergent subsequence of $v_d$, the row variance $V/d$ consequently tends to

$$
v_0=\tfrac14(1-\alpha\lambda-\lambda^2)>9/40,
$$

since $3\le\alpha\le4$ and $\lambda<e^{-9/2}<1/50$. The aspect, density, feasible offsets and positive limit of $V/d$ put this subsequence in the proportional-variance case. The two local ratios at the exact angular node tend to $e^{-1/(8v_0)}$. Their product is $e^{-b_k}$, so every subsequential limit of $b_k$ is $1/(4v_0)<10/9<\log4$. This family has a genuine cap effect on the coefficient and curvature too weak for the elementary geometric sign bound. The bounded-aspect proof treats the change of the cap correction between adjacent quotas. [Proportional-variance calculation](../bounded-aspect-angular-signs.md#proportional-row-variance)

## Scope of universal interface claims

The archived exact brackets pass all 16,942 comparisons between an angular node and a neighboring geometric node. Dominance itself fails at 273 of the 9,162 archived nodes, all in dimensions two and three. There is also an exact order reversal with both parity signs correct outside that archive. At $(n,d,r)=(144,2,1)$, the dimension-two formula gives

$$
w_4=\tfrac12\tan\left(\frac{(17/4)\pi}{n+1/2}\right)>\frac{51}{4(2n+1)}.
$$

The fourth power of the rational lower bound exceeds $t_5^2=5/1817844$. The all-height dimension-two theorem gives $P(-w_4^2)>0$. To check $P(-t_5)<0$, put $Q=t_5^2$, $E(Q)=\sum_j a_{2j}Q^j$, and $O(Q)=\sum_j a_{2j+1}Q^j$. The exact rank-one coefficients give $E(Q)^2<QO(Q)^2$. This reversal goes from an angular index to a higher geometric index near the lower edge at aspect 72. The aspect-four results concern coverage of the previous sufficient tests. [Dimension-two sign theorem](../../edges/all-quota-signs.md#dimension-two-at-every-height)

From this directory, run `python3 -IB check_interfaces.py`. The script checks the SHA-256 hashes of the tracked coefficient archive and dyadic certificates from commit `5114bad2c04b8f50098f04a5f028e24cfad24662` before reading them. It compares endpoint powers to the rational dominance boundaries and squared geometric radii, then checks the finite examples with exact fractions. [Replay script](check_interfaces.py) · [Coefficient archive](../../screen-angular-signs.jsonl.gz) · [Dyadic certificates and phase replay](../../exact-node-signs/README.md)
