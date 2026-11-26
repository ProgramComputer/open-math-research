# Independent review of the explicit rare-overflow signs

Agent-assisted review by the quota referee, 2026-11-26. I independently checked the theorem and constants in [finite-rare-overflow-angular.md](finite-rare-overflow-angular.md). I found no mathematical gap. The theorem gives the strict sign at the exact angular node for each quota satisfying its stated conditions, including $n\ge10^6$, $3\le n/d\le4$, $k/n\in[1/4,3/4]$ and the specified overflow gap. It does not require a Fourier remainder argument or establish a full root count.

## Exact phase and its comparison

Put $b(t)=1-p+pe^{it}$. For an uncapped binomial, the characteristic function is $b(t)^d$. In the precision numerator, the weight $q_S=S(d-S)/(d(d-1))$ counts ordered occupied-empty cell pairs divided by the number of ordered pairs of distinct cells. Exposing this pair gives numerator $p(1-p)e^{it}b(t)^{d-2}$, so the precision is $A_0(t)=p(1-p)e^{it}/b(t)^2$. Both arguments along the arc start at zero as $t$ increases from zero to $\theta=\pi/d$. The lifted phase is therefore $(nd+d-1)\arg b(\theta)-\nu\theta$, with $\nu=(d-1)/2$.

For a centered Bernoulli, $\Re\mathbb E e^{itX}\ge1-t^2/8$ and $|\Im\mathbb E e^{itX}|\le |t|^3/24$ using $|X|\le1$, $\mathbb E X=0$ and $\mathbb E X^2\le1/4$. Here $\arg b(t)-pt$ is the continuous argument of the centered characteristic function, which lies in the open right half-plane. Since $1-\theta^2/8\ge5/6$, the error at $\theta$ is at most $\theta^3/20$. On multiplying by $nd+d-1$, the bound is strictly below $26/n$ using $d\ge n/4$, $\pi^3<32$, and $n\ge10^6$. The linearized phase is $L(p)=\pi[(n+1-1/d)p-\nu/d]$. At $p_c=(k+1/2)/(n+1)$ it differs from $k\pi$ by $\pi(1/2-p_c)/d$, of magnitude at most $2\pi/n<7/n$. The changes from $p_c$ to $p_\pm=p_c\pm100/n^2$ exceed $300/n$ in magnitude, from $L'(p)\ge n\pi$ and $\pi>3$. Also $|p_\pm-k/n|\le1/(4(n+1))+100/n^2<1/n$. Thus both endpoints lie in $[1/5,4/5]$ and below $(k+3)/n$.

At each endpoint the given gap and Hoeffding's inequality give $\Pr(\mathrm{Bin}(d,p)>r)\le e^{-2d(r/d-p)^2}\le n^{-4}=\delta$. The shift from $S>r$ to the cutoff threshold $r$ only weakens the upper bound. Conditioning changes expectations of tests of modulus at most one by at most $2\delta$ by total expectation over the two events. This applies to the numerator for precision because $q_S\le 1$, and to both characteristic functions. On the entire arc Bernoulli's inequality gives

$$
|\phi_0(t)|\ge (1-t^2/8)^d\ge1-\pi^2/(8d)>.99.
$$

The row precision satisfies $.16\le |A_0|\le .26$, using $p\in[1/5,4/5]$, $|b(t)|\le1$, and $|b(t)|\ge 1-t^2/8$. Specifically, if $N$ is the precision numerator then

$$
|A-A_0|\le
\frac{|N-N_0|+|A_0|\thinspace{}|\phi-\phi_0|}{|\phi|}
\le \frac{2\delta(1+.26)}{.99-2\delta}<5\delta.
$$

The quotient perturbations $\phi/\phi_0-1$ and $A/A_0-1$ have modulus bounded by $2\delta/.99$ and $5\delta/.16$. They stay in the disk of radius $1/2$ centered at zero. Adding the continuous argument of each quotient to the corresponding reference lift therefore gives the argument started at zero, and the two argument changes at $\theta$ are below $5\delta$ and $64\delta$. For the capped law, write $H(z)=\sum_{j=0}^r\binom djz^j$ and $B(z)=\sum_{j=0}^{r-1}\binom{d-2}jz^j$. The identity $q_j\binom dj=\binom{d-2}{j-1}$ yields $A(t)=we^{it}B(we^{it})/H(we^{it})$. Both $B$ and $H$ have their values in a sector of width below $\pi$ on the arc, and their continuous arguments start at zero. The angular ordering convention therefore agrees exactly with the lift $t+\arg B-\arg H$, with no added multiple of $2\pi$. The phase perturbation is less than $100n\delta$, which together with $26/n+7/n$ is less than $300/n$. The overflow hypothesis implies $nr/d>k+3$, so $k$ is internal and angular ordering applies. The unique exact $p_{\ast}$ belongs to the claimed bracket.

## Local coefficients and global tails

For each quota $i=k+j$, $|j|\le3$, uncapped choices make distinct labeled column supports independent, each uniform among $i$-subsets. A specified row has independent $\mathrm{Bernoulli}(i/n)$ cells across the columns. Hoeffding and then the union bound over rows give $a_i/\binom ni^d\in[1-n^{-3},1]$. These quotas are within $[0,n]$. The bound also verifies positive support at all seven positions. Taking the difference of two logarithms from the interval $[\log(1-n^{-3}),0]$ costs at most $2n^{-3}$, since $n^{-3}<1/2$. The support of all feasible quotas is contiguous, as also follows by splitting a cyclic word of $di$ column labels into row blocks of sizes at most $r$.

The bracket gives $|p_{\ast}-x|<1/n$ and $|p_{\ast}-x-(1/2-x)/n|\le101/n^2$. In the Taylor bound for the logit, the first derivative is at most six at the expansion point $x\in[1/4,3/4]$. The second derivative is at most 50 in absolute value throughout $[1/5,4/5]$. Stating these domains separately clarifies the source wording because the first derivative at $1/5$ is $25/4$. Thus the logit error is at most $(6\cdot101+25)/n^2<650/n^2$.

For $j>0$ the binomial ratio is a product of factorial ratios. After extracting $(1-x)/x$, the logarithmic errors are bounded by $16\sum_{i=1}^3[(i-1)^2+i^2]/n^2=304/n^2$, with all log arguments within $1/2$ of one. Summing the linear terms gives $-j^2/(2nv)-j(1/2-x)/(nv)$. For $j<0$, apply this calculation to the binomial coefficients with $k'=n-k$, $p_{\ast}'=1-p_{\ast}$ and shift $-j$; their bracket reflects exactly and the linear $j$ term changes sign. This reflection is only for the uncapped factors. The cap correction still uses the original quota, via the separate union bound at every shift. Combining the binomial and logit errors with $d\le n/3$, and including the cap correction, gives the uniform log budget

$$
\frac{d(400+3\cdot650)}{n^2}+\frac2{n^3}<\frac{1000}{n}\le .001.
$$

Since $d/n\ge1/4$ and $v\le1/4$, the Gaussian exponent $a=d/(2nv)$ is at least $1/2$. The model sum $S(a)=1-2e^{-a}+2e^{-4a}-2e^{-9a}$ strictly increases there because $S'(a)=2e^{-4a}(e^{3a}-4)+18e^{-9a}>0$. At $a=1/2$, the three stated rational estimates give $S(a)> .032$. The absolute errors in the six normalized positive term magnitudes are below $.002$ each because the ideal magnitudes are at most one. The actual parity-corrected seven-term normalized sum is therefore strictly above $.02$.

Let $T_i=a_i w_{\ast}^{di}$. Ordinary log-concavity follows from the known normalized log-concavity by multiplying by the positive log-concave sequence $\binom ni^d$ on the support. Thus the outward ratios of $T_i$ are nonincreasing on either side. In particular, the first outward ratios are at most $e^{-a+.001}<1$. The omitted terms begin at even offset four on both sides, so pairing each even-offset term with the following odd-offset term contributes nonnegative signed mass. Any unpaired final term has even offset. This proves the strict sign on the full support, including either finite endpoint. As a separate absolute check, the outward ratios beyond the seven-term window are bounded by $T_{k\pm3}/T_{k\pm2}\le e^{-5a+.002}<1/10$. Each $T_{k\pm3}/T_k<.013$, giving combined absolute tail below $2\cdot .013/9<.003$.

## Rational replay

The Taylor sums used here for $e^{1/2}$ and $e^{9/2}$ are $211/128$ and $4102015261/45875200$. The upper sum with geometric remainder for $e^2$ is $20948/2835$. The following exact arithmetic checks the endpoint constants, using $3<\pi<22/7$.

~~~python
from fractions import Fraction as Q
from math import factorial

def exp_sum(x, degree):
    return sum((x**k / factorial(k) for k in range(degree + 1)), Q(0))

n = 10**6
dmin = n // 4
pi = Q(22, 7)
theta = pi / dmin
delta = Q(1, n**4)

assert pi**3 < 32
assert Q(1, 24) / (1 - theta**2/8) < Q(1, 20)
assert 32 * Q(16, 20) * (1 + Q(1, n)) < 26
assert 2*pi < 7
assert 1 - pi**2/(8*dmin) > Q(99, 100)
assert Q(1, 4) / (1 - theta**2/8)**2 < Q(26, 100)
assert 2*(1+Q(26, 100)) / (Q(99, 100)-2*delta) < 5
assert 4/Q(99, 100) < 5
assert 10/Q(16, 100) < 64
assert Q(100, n**2) + 26 + 7 < 300
assert 6*101 + Q(50, 2) < 650
assert 16*sum((i-1)**2+i**2 for i in range(1, 4)) < 400
assert Q(400+3*650, 3) + Q(2, n**2) < 1000
assert exp_sum(Q(3, 2), 3) > 4
assert exp_sum(Q(1, 2), 4) > Q(1000, 607)
assert exp_sum(Q(2), 8) + Q(2**9, factorial(9))/(1-Q(2, 10)) < Q(1000, 135)
assert exp_sum(Q(9, 2), 10) > Q(1000, 12)
assert 1/(1-Q(1, 1000)) < Q(1002, 1000)
assert 1-2*Q(607, 1000)+2*Q(135, 1000)-2*Q(12, 1000) == Q(32, 1000)
assert Q(32, 1000)-6*Q(2, 1000) == Q(2, 100)
assert exp_sum(Q(1249, 500), 4) > 10
assert Q(12, 1000)*Q(1002, 1000) < Q(13, 1000)
assert 2*Q(13, 1000)/9 < Q(3, 1000)
~~~

All 23 assertions passed under Python with exact rational arithmetic. The source argument needs only the signed tail bound. The sole editorial correction is to state the two derivative domains explicitly.
