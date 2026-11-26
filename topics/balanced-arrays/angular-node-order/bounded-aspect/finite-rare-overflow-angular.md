# Explicit angular signs with rare overflow at aspect three to four

Let $n\ge10^6$, $3\le n/d\le4$, $1\le r<d$, and
$1/4\le x=k/n\le3/4$. Suppose

$$
\frac rd-\frac{k+3}{n}\ge\sqrt{\frac{2\log n}{d}}.
$$

Let $w_{\ast}$ be the exact ordered angular tilt of phase $k\pi$.
Then $(-1)^kP_n(-w_{\ast}^d)>0$. This is an explicit finite sign
bound at each quota satisfying the overflow gap. It leaves the
other quotas and the full array root count outside the bound.
The angle and the node differ from the previously studied
geometric radius. In particular this proof does not invoke the
factor-four coefficient separation test.
[Angular ordering](https://github.com/ProgramComputer/open-math-research/blob/8d9a0cfdd12bf23086bcc2db05691310b9d3a126/topics/balanced-arrays/angular-node-order/README.md)
· [Earlier effective geometric signs](https://github.com/ProgramComputer/open-math-research/blob/6a91a65e940e8aa9adadb3be9fe344266eb22d59/topics/balanced-arrays/effective-sublinear/README.md)

## Angular tilt from the uncapped binomial

Write $\theta=\pi/d$, $\nu=(d-1)/2$, and $p=w/(1+w)$.
The principal phase is
$n\arg\phi(\theta)-\nu\arg A(\theta)$, where
$\phi(t)=\mathbb E e^{itS}$ and
$A(t)=\mathbb E[q_S e^{itS}]/\phi(t)$ for
$q_j=j(d-j)/(d(d-1))$. For the capped row, $S$ is a
$\mathrm{Bin}(d,p)$ law conditioned on $S\le r$. For the
uncapped row, using the factorial moments of a binomial gives

$$
\phi_0(t)=(1-p+pe^{it})^d,\qquad
A_0(t)=\frac{p(1-p)e^{it}}{(1-p+pe^{it})^2}.
$$

Thus the uncapped lifted phase at $\theta$ is
$(nd+d-1)\arg(1-p+pe^{i\theta})-\nu\theta$.
For a centered Bernoulli $X$ of parameter $p$,
$\Re\mathbb E e^{itX}\ge1-t^2/8$ and
$|\Im\mathbb E e^{itX}|\le |t|^3/24$, since $|X|\le1$
and $\mathbb E |X|^3\le\mathbb E X^2\le1/4$.
It follows that
$|\arg(1-p+pe^{i\theta})-p\theta|\le\theta^3/20$.
This changes the full principal phase from
$\pi[(n+1-1/d)p-\nu/d]$ by at most $26/n$,
using $d\ge n/4$, $\pi^3<32$ and $n\ge10^6$.

Set $p_c=(k+1/2)/(n+1)$ and $p_\pm=p_c\pm100/n^2$.
At $p_c$, the linear phase less $k\pi$ is
$\pi(1/2-p_c)/d$, of absolute value less than $7/n$.
The change in the linear phase from $p_c$ to either
bracketing probability has magnitude at least $300/n$.
Both probabilities are in $[1/5,4/5]$ and at most $(k+3)/n$.

For either probability the unconditioned cap overflow chance is
at most $\delta=n^{-4}$ by Hoeffding. For all $0\le t\le\theta$,
the uncapped $|\phi_0(t)|$ is at least
$(1-t^2/8)^d>.99$. Conditioning changes either bounded
expectation $\mathbb E e^{itS}$ or $\mathbb E[q_S e^{itS}]$
by at most $2\delta$. Since $|A_0(t)|\le.26$ and
$|A_0(t)|\ge p(1-p)\ge .16$, dividing the two expectations
gives $|A(t)-A_0(t)|\le5\delta$. The phase changes in
$\phi$ and $A$ are at most $5\delta$ and $64\delta$,
using $|\arg(1+z)|\le 2|z|$ for $|z|\le1/2$.
These branches agree with the phases started at $t=0$.
For the actual phase expression the precision branch also
agrees with the lift $\theta+\arg B-\arg H$: the ratio
$we^{it}B(we^{it})/H(we^{it})$ starts positive and equals
$A(t)$, where the sector arguments of $H,B$ start at zero.
The resulting angular phase error is at most $100n\delta$.
The two phases therefore bracket $k\pi$ strictly. By ordering,
the true parameter $p_{\ast}=w_{\ast}/(1+w_{\ast})$ lies between $p_-$ and $p_+$.

## Seven terms at the exact angular tilt

At every $i=k+j$, $|j|\le3$, the coefficient
$a_i$ differs from $F_i=\binom ni^d$ only by a relative error
in $[0,n^{-3}]$, with $a_i\le F_i$. Indeed at fixed uncapped
column quota $i$ each row individually has
$\mathrm{Bin}(d,i/n)$ load, so a union bound over rows after
Hoeffding gives this range. All these quotas are feasible by
the hypotheses. The effect on any log ratio relative to $a_k$
is at most $2n^{-3}$.

Put $v=x(1-x)$ and $w_0=x/(1-x)$.
For $p_{\ast}$ in the bracket,
$|p_{\ast}-x|\le1/n$ and
$|p_{\ast}-x-(1/2-x)/n|\le101/n^2$.
For the logit $L(p)=\log(p/(1-p))$, the first derivative satisfies
$L'(x)=1/v\le16/3<6$ at the expansion point $x\in[1/4,3/4]$.
The second derivative satisfies $|L''(p)|\le 50$ throughout
$p\in[1/5,4/5]$, since $p^{-2}+(1-p)^{-2}\le 50$ there.
Taylor's theorem therefore yields

$$
\left|\log(w_{\ast}/w_0)-\frac{1/2-x}{nv}\right|\le650/n^2 .
$$

For $1\le j\le3$, the successive binomial coefficient
ratios give

$$
\log\frac{\binom n{k+j}}{\binom nk}+j\log w_0
=\sum_{i=1}^j
\left[\log\left(1-\frac{i-1}{n(1-x)}\right)
-\log\left(1+\frac{i}{nx}\right)\right].
$$

Replacing the logarithms by their linear terms costs at most
$400/n^2$: use $|\log(1+z)-z|\le z^2$ for $|z|\le1/2$
and $16\sum_{i=1}^3[(i-1)^2+i^2]=304$.
The linear contribution is
$-j^2/(2nv)-j(1/2-x)/(nv)$.
For negative $j$, reflection replaces $(k,p_{\ast})$ with
$(n-k,1-p_{\ast})$ and yields the same formula with signed $j$.
Combining the phase bracket, the binomial ratios (raised to the power $d$), and the cap correction gives

$$
\left|\log\frac{a_{k+j} w_{\ast}^{d(k+j)}}{a_k w_{\ast}^{dk}}
       +a j^2\right|<\frac{1000}{n}\le .001,
\qquad a=\frac{d}{2nv}\ge\frac12
\qquad(1\le |j|\le3).
$$

Here the sum of the binomial and log odds errors before
multiplication by $d$ is at most $(400+3\cdot650)/n^2$.

The ideal signed sum of the seven terms is
$S(a)=1-2e^{-a}+2e^{-4a}-2e^{-9a}$.
Its derivative is positive for $a\ge1/2$, since
$e^{3a}\ge e^{3/2}>4$. At $a=1/2$, the rational bounds
$e^{-1/2}<.607$, $e^{-2}>.135$, and $e^{-9/2}<.012$
give $S(a)>.032$. These follow from Taylor bounds:
for $e^{1/2}$ and $e^{9/2}$ take lower sums through
degrees four and ten respectively. For $e^2$ take the sum
through degree eight and bound the remaining terms by
$(2^9/9!)/(1-2/10)$.
Each of the six normalized terms differs from its ideal
magnitude by less than $.002$ using $e^{.001}<1.002$.
Thus the signed actual seven-term lower bound exceeds $.02$.

The first outward ratios are already less than one since
$a\ge1/2$ and their log errors are below $.001$.
The normalized log-concavity of the coefficients implies
that the successive outward term ratios decrease. The
first omitted term on either side has even offset four,
so each omitted tail has nonnegative signed sum by pairing
consecutive terms. A left or right tail can terminate,
possibly with an unpaired positive term. This proves the
strict sign of the whole polynomial at the exact node.
[Normalized log-concavity](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/orientation-normalization.md)
