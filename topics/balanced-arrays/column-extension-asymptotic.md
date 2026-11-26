# An eventual obstruction for the adjacent-column multiplier at row cap five

Let $a_{n,k}^{(c)}$ count the labeled binary arrays on $c$ columns, with every column sum $k$ and every row sum at most five. Set $\alpha=5/6$, $\beta=5/7$, $m_n=\lfloor\alpha n\rfloor$, and $K_n=\lfloor\beta n\rfloor$. The adjacent-column multiplier symbol
$$
S_n(q)=\sum_{k=0}^{K_n}\binom{m_n}{k}\frac{a_{n,k}^{(7)}}{a_{n,k}^{(6)}}q^k
$$
has nonreal zeros for all sufficiently large $n$. The threshold here is existential. This conclusion concerns the multiplier symbol. It does not assert nonreal zeros for the balanced-array polynomials themselves.

For either column count and every $k$ in its degree range, positivity of the coefficient follows by listing the column indices cyclically $k$ times and filling successive rows from the list in blocks of size five and a possible shorter final block. Each block has distinct columns and the capacity inequality ensures that at most $n$ blocks are needed. The constant terms are one.

## Entropy rates and the small positive saddle

Write
$$
Z_c(x)=\sum_{j=0}^5\binom cj x^j,\qquad
\mu_c(x)=\frac{x Z'_c(x)}{c Z_c(x)}.
$$
For $0<\theta<5/c$, the inverse $x_c(\theta)>0$ exists and is real-analytic. Indeed $x\mu'_c(x)$ is the positive row-size variance divided by $c$, and the endpoint means are 0 and $5/c$. Let
$$
g_c(\theta)=\log Z_c(x_c(\theta))-c\theta\log x_c(\theta),\qquad
B(\theta)=\alpha\log\alpha-\theta\log\theta-(\alpha-\theta)\log(\alpha-\theta).
$$
On every compact subinterval of $(0,\beta)$, uniformly in lattice quotas $\theta=k/n$ the log of the coefficient of $q^k$ in $S_n$, divided by $n$, converges to
$$
f(\theta)=B(\theta)+g_7(\theta)-g_6(\theta).
$$
Assign each allowed row support $A$ probability $\pi_A=x_c(\theta)^{|A|}/Z_c(x_c(\theta))$. Under independent rows the balanced event has probability $a_{n,k}^{(c)}x_c(\theta)^{ck}/Z_c(x_c(\theta))^n$, which is at most one. For a matching exponential lower bound, choose the number of copies of each support of size at least two to be $\lfloor n\pi_A\rfloor$. Then choose the singleton counts so that each margin is exactly $k$, and choose the empty support count so that all counts sum to $n$. Since the tilted mean of each margin is precisely $k$, the resulting count $N_A$ of every support satisfies $N_A=n\pi_A+O(1)$, uniformly on each compact quota subinterval. All $\pi_A$ are bounded below there, so these integers are feasible for sufficiently large $n$. The probability of this type is
$$
\frac{n!}{\prod_A N_A!}\prod_A \pi_A^{N_A}
=\exp(O(\log n))
$$
uniformly, by Stirling's bounds and $N_A/n=\pi_A+O(1/n)$. This supplies the lower exponential rate. Stirling's bounds give the binomial contribution $B$ uniformly.

The convergence extends uniformly to any closed interval $[0,\delta]$ with $\delta<\beta$. Deleting the last column gives $a_{n,k}^{(7)}\le a_{n,k}^{(6)}\binom nk$. In the other direction $a_{n,k}^{(7)}\ge1$ and $a_{n,k}^{(6)}\le\binom nk^6$. Since $\binom{m_n}{k}\le\binom nk$, the normalized logarithm of the symbol coefficient lies between $-6H(\theta)$ and $2H(\theta)$, where $H(\theta)=-\theta\log\theta-(1-\theta)\log(1-\theta)$. Also $f(\theta)\to0$, since $x_c(\theta)\sim\theta$ as $\theta\downarrow0$. This gives the extension by combining the compact-interval convergence with the entropy bounds near zero.

In the interior,
$$
-f'(\theta)=\log Q(\theta),\qquad
Q(\theta)=\frac{\theta}{\alpha-\theta}\frac{x_7(\theta)^7}{x_6(\theta)^6}.
\tag{1}
$$
Here $Q(\theta)\sim\theta^2/\alpha$ as $\theta\downarrow0$, with an analytic expansion at zero by the analytic inverse of $\mu_c(x)=x+O(x^2)$. In particular $Q$ is strictly increasing for small positive $\theta$. Fix $\delta>0$ within that region. All symbol coefficients are at most $2^{m_n+n}$ by the deletion bound, so for sufficiently small positive $q$, the aggregate contribution from $\theta\ge\delta$ to $S_n(q)$ is exponentially small, since the exponent is at most $(\alpha+1)\log2+\delta\log q<0$. On $[0,\delta]$, the function $f(\theta)+\theta\log q$ has its unique strict maximum at $\theta=Q^{-1}(q)\in(0,\delta)$. This follows from (1), $Q(0)=0$ and strict increase. Its value is positive because the value at zero is zero and the function initially increases. Uniform convergence of the normalized logarithms now gives exponential concentration of $k/n$, under weights proportional to the terms of $S_n(q)$, in any fixed neighborhood of $Q^{-1}(q)$. Indeed any closed set avoiding that point has a strictly smaller maximum, while the term of nearest quota to the maximizer supplies a lower bound for the denominator. In particular,
$$
\frac{q S_n'(q)}{n S_n(q)}\longrightarrow Q^{-1}(q)
\tag{2}
$$
for all sufficiently small positive $q$. This argument makes no global concavity assumption.

## What an unbounded sequence of real-rooted symbols would imply

Suppose there is an unbounded sequence of $n$ with real-rooted $S_n$. All roots in that sequence are strictly negative, since each coefficient is positive and the constant is one. For a root $-\rho$, count multiplicity and place mass $1/n$ at $p=1/(1+\rho)\in(0,1)$. Along a subsequence the finite measures on $[0,1]$ converge weakly to $\nu$ of mass $\beta$, by compactness. For each $q>0$ define $p_q=qp/(1-p+qp)$ and $T(q)=\int p_q\,d\nu(p)$. Factorization and the weak limit give
$$
\frac{q S_n'(q)}{n S_n(q)}\longrightarrow T(q)
$$
along this subsequence for each $q>0$. The integral is real-analytic on $(0,\infty)$, since near any fixed positive $q$ the denominator is uniformly bounded away from zero for all $p\in[0,1]$. By (2), $T$ is nonconstant, so $\nu((0,1))>0$. Hence $0<T(q)<\beta$ for every finite $q>0$ and $T'(q)>0$.

By (2), $Q(T(q))=q$ for small positive $q$. The composition is real-analytic on all $q>0$, so the identity holds throughout that interval. Since $T$ is increasing, it tends to $\beta$ as $q\to\infty$. Any smaller limit would be an interior point of $(0,\beta)$, where $Q$ is finite and continuous, contradicting $Q(T(q))=q$. On the other end $T(q)\to0$ by (2). Thus $T$ attains every interior quota, and $Q$ coincides there with its inverse. This also rules out a switch between competing saddles under the real-rootedness hypothesis.

## Negative localizing determinant

At the target $\theta_*=\mu_7(1/2)=179/543$, put $q_*=Q(\theta_*)$. Let $s_j=\int p_{q_*}^j\,d\nu(p)$. Then $s_0=\beta$ and $s_1=\theta_*$. The moments for $j\ge1$ are determined by the power series identity
$$
\sum_{j\ge0}s_{j+1}z^j=\frac{T(q_*(1-z))}{1-z}.
\tag{3}
$$
Indeed $p_{q_*(1-z)}=(1-z)p_{q_*}/(1-zp_{q_*})$. The germ on the right is determined by (1) and the inverse identity. If $\nu$ is positive, the $13\times13$ matrix
$$
L_{ij}=s_{i+j}-s_{i+j+1},\qquad 0\le i,j\le12,
$$
is positive semidefinite by the Gram formula with measure $(1-p_{q_*})\,d\nu$, so its determinant must be nonnegative.

The accompanying script [moment verifier](code/verify_column_extension_moments.py) instead certifies
$$
-3\cdot10^{-101}<\det L<-10^{-101}.
$$
It brackets $x_6(\theta_*)$ by 200 bisections in exact rationals using the strict monotonicity of $\mu_6$. After converting the bracket into an Arb enclosure, it builds the jets of $x_c(\theta_*+u)$ by formal series reversion of $\mu_c(x_c(\theta_*)+v)-\theta_*$. The constant term is exactly zero in each such centered reversion, though its independent interval evaluation can have positive radius. Substituting these jets in (1) gives the jet of $Q(\theta_*+u)$ and a strictly positive linear term. Reversion of $z=1-Q(\theta_*+u)/q_*$ gives $T(q_*(1-z))=\theta_*+u(z)$. Division by $1-z$ in the ring of power series gives the coefficients in (3). The script uses 26 terms, which include every moment through $s_{25}$ needed in $L$. Arb's determinant enclosure at 640 bits verifies the strict rational inequalities displayed above. With Python and python-flint 0.9.0 it reports
$$
\det L=[-2.130856436499024468315465\cdot10^{-101}\ \mathbin{+/-}\ 4.94\cdot10^{-126}].
$$

This contradicts the existence of an unbounded subsequence of real-rooted symbols. Thus there is an integer after which each $S_n$ has a nonreal conjugate pair. This proof has no checked Lean or Rocq coverage.

[Independent review and second computation](review-column-extension-asymptotic.md)
