# Independent review of the rare-overflow strip

**Verdict.** The finite extension inequality and the necessary near-cap location of a normalized-curvature drop hold with the stated thresholds. The argument leaves the near-cap strip open.

For a uniform quota-$i$ column, conditional on the first row bit, the second row bit has success probability $i/(n-1)$ if the first bit is zero and $(i-1)/(n-1)$ if it is one. The columns remain conditionally independent. The first-row overflow indicator increases in its bits, while the conditional second-row overflow probability decreases in them, as witnessed by coupling with shared uniforms. An increasing and a decreasing function of independent Bernoulli bits have nonpositive covariance: condition on the last bit, apply the induction hypothesis to the conditional covariance, and then use the opposite monotonicity of the two conditional expectations. This gives the joint overflow bound $T_i^2$ needed by Bonferroni.

Writing $v=nT_*$, we have $v\le n^{-15}<1/2$. The logarithm bounds follow from $-\log(1-v)-v\le v^2$ and $\log(1+y)\le y$, so $2n^2T_*^2$ is a conservative error. Subtracting the neighboring logarithms costs at most $4n^2T_*^2/d$ before multiplying by $n-i$. Nesting gives $A\le0$, and Taylor's bound adds at most $2n^2T_*^2/d^2$ before that multiplication, yielding the stated $6n^3T_*^2/d$.

On the four-quota interval, $z,1-z>0.19$, and

$$
B(z)=r/z-(d-r-1)/(1-z),\qquad
-B'(z)=r/z^2+(d-r-1)/(1-z)^2<28d .
$$

The distance hypothesis gives $B\ge4d\delta$, while $B\le r/z<6d$. Thus $B^2\ge128d\log n$, and $B>40$. Substituting these estimates in the integrand leaves at least $(0.095-2/40)B^2>B^2/25$. The monotone logarithmic derivative gives $T_*\le F(z_*)/B(z_*)$, and integrating $B\le6d$ over a range of length $3/n$ gives $F_{\min}\ge e^{-18}F(z_*)$. The triangular kernel for a centered second difference has mass $n^{-2}$. These facts give the coefficient $64e^{-18}/25>10^{-8}$. The error-to-leading ratio is bounded by $24\cdot64\cdot10^8/n^{27/2}<1$ using $nT_*\le n^{-15}$ and $\delta>n^{-1/2}$. The positivity in the claimed region is strict because $T_*>0$.

For the sign criterion, the three extensions at center $k$ compare the normalized curvatures at indices $k$ and $k+1$. Indeed, orientation gives $u_{k+1}/u_k\le(n-k-1)/(n-k)$, and concavity bounds $u_{k-1}u_{k+1}$ by $u_k^2-(u_k-u_{k+1})^2$. Thus $p_{k+1}/p_k=(u_k/(n-k))^d$ is log-concave at $k$. A drop at $j$ therefore requires the theorem to fail at $k=j-1$, where its rightmost quota is $j+1$. The sign criterion's window $0.23n<j<0.77n$ puts $k$ in the required window, and substituting $k=j-1$ gives exactly the strip width $1+n\sqrt{8\log n/d}$. The conclusion is a necessary location for a coefficient comparison to fail, and supplies no root location or sign conclusion within the strip.

**Signed** — four_literature, independent agent-assisted mathematical review.
