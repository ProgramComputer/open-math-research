# Exterior coefficient sums

Let $P=E_{n,k}$, $Q=E_{n+1,k}$, and let $V$ be the complete insertion lag including its factor $X$. For one rank $1\le h\le H$, write $a=[X^h]P>0$, $u=a/[X^{h+1}]P>0$, $L=7u/8$, $U=9u/8$, and $r=1/300$. The finite norm $M$ is `frontCoefficientNorm _ h L U`. The weight $w_j$ is $U^{j-h}$ on $j\ge h$ and $1/L^{h-j}$ on $j<h$.

Use the following per-index assumptions from the [effective-front estimates](../../effective-front.md). They are assumptions on **weighted absolute coefficients**, evaluated at the endpoint giving the largest weight for their relative exponent.

- At $j=h-\ell\ge0$, for $\ell\ge1$, $|[X^j]P|w_j\le a(51/10)(\ell+1)r^\ell$. At $j=h+1+\ell$, for $\ell\ge1$, the bound is $9a(\ell+1)r^\ell$. The degree-zero coefficient for the actual polynomial is zero, so the left estimate also covers $j=0$.
- For $j\le J$, $|[X^j]V|w_j\le (8/25)|[X^j]P|w_j$. Here $J=\lfloor\sqrt n/2\rfloor$ and both central indices are at most $J$.
- For $j>J$, write $j=h+1+\ell$. The far lag estimate is $|[X^j]V|w_j\le 36a\ell(\ell+1)r^\ell$. The published $\ell\ge14$ is stronger than the $\ell\ge2$ used below.

For the actual row the scale is $u=\rho(h/(h+1))^n$, where $\rho$ is the ratio of normalized old coefficients at $h,h+1$. The old envelope at $L$ gives the left estimate, and at $U$ gives the right estimate because the factor $8|X|/u$ is then $9$. The near lag envelope is a coefficient-wise ratio, so its transfer to the same weight requires no common evaluation endpoint. On the far side the unconditional lag bound contributes a factor $j<4\ell$ and the earlier coefficient envelope contributes $9(\ell+1)r^\ell$. The rank estimates used here are $n\ge10000$ and $h\le H=\lfloor7\sqrt n/20\rfloor$. The remaining analytic obligation is to formally derive these per-index bounds, positivity of both central coefficients and the stated adaptive scales from the original enumerator and lag, including the near multiplicative lag estimate.

Put $T=P-aX^h(1+X/u)$ and $D=XP'-(h+1)P+aX^h$. The two central coefficients vanish exactly in both. For $T$ this uses $a/u=[X^{h+1}]P$, and for $D$ the coefficient multiplier before adding $aX^h$ is $j-(h+1)$. Away from the central pair, $T$ has the same coefficients as $P$, while $D$ has a factor $\ell+1$ on the left and $\ell$ on the right. In each left or right sum, each $\ell$ represents at most one polynomial degree. Missing degrees and coefficients outside the support are zero. One may pad each finite sum with zeros before comparing to the finite geometric interval, so the argument uses no degree bound.

For $\ell\ge1$, $\ell+1\le2^\ell$, $(\ell+1)^2\le4^\ell$, and $\ell(\ell+1)\le 4^\ell/2$. The last inequality is equality at one and follows by induction because $(\ell+2)/\ell\le3$. Comparing each finite sum to the geometric total gives the strict rational margins

$$
M(T)\le a\frac{51/10+9}{149}<a/10<a/8,
\qquad
M(D)\le a\frac{51/10+9/2}{74}<3a/20.
$$

For the near lag, the two central weighted coefficients are exactly $a$ and $(9/8)a$. Since $M(P)\le a+(9/8)a+M(T)$, the near contribution is at most $(8/25)(1+9/8+1/10)a$. In the far lag, even the weaker $\ell(\ell+1)\le4^\ell$ gives the contribution at most $36a\sum_{\ell\ge2}(1/75)^\ell=36a/(75\cdot74)$. Thus

$$
M(V)\le a\left[\frac8{25}\left(1+\frac98+\frac1{10}\right)
                  +\frac{36}{75\cdot74}\right]<18a/25.
$$

The recurrence is $Q=nXP+(1-X)XP'+V$. Choose $G=nX+(1-X)(h+1)$ in the certificate. Its precise successor residual is

$$
W=Q-GP+(1-X)aX^h=(1-X)D+V.
$$

For arbitrary finite polynomials $A,B$, $M(A+B)\le M(A)+M(B)$ by extending the coefficient sums to the union of the supports, and $M(XA)\le U M(A)$ since $w_{j+1}\le U w_j$. Below $h$ the ratio of consecutive weights is $L$, including at $j=h-1$, and from $h$ onward it is $U$. Consequently $M(W)\le(1+U)M(D)+M(V)<a$ as soon as $U\le1/2$, since $(3/2)(3/20)+18/25=189/200$.

The exterior cap gives $U\le (459/40)(H/(H+1))^n$. Writing $z=\sqrt n\ge100$, one has $H+1\le(9/25)z$ and $n/(H+1)\ge z/(9/25)>22$. The inequality $\log(1+1/H)\ge1/(H+1)$ gives $(H/(H+1))^n\le \exp(-n/(H+1))$, and $\exp(n/(H+1))\ge 1+n/(H+1)>23>2(459/40)$. Hence the cap gives $U<1/2$ uniformly, independent of the finer middle-phase seam.

## Formal scope and replay

`front_certificates_of_weighted_envelopes` in [FrontLagSum.lean](FrontLagSum.lean) proves both strict coefficient tests for arbitrary finite polynomials under the displayed per-index estimates and the insertion identity. [RepositoryExteriorEnvelopes.lean](RepositoryExteriorEnvelopes.lean) specializes this to the literal enumerators and the full lag supplied by the pinned recurrence. Its scale is the actual coefficient ratio. It derives $U<1/2$ from the prescribed scale cap and $h+2\le J$ from the rank range, and then applies the [exterior coefficient reduction](../front-middle-join/RepositoryExteriorCertificates.lean). The conclusion is strict negative interlacing of the reduced rows and weak real interlacing of the original rows in the stated large-size regime, conditional on the exterior coefficient hypotheses.

The remaining hypotheses concern the actual coefficients. They include positivity of the two central coefficients, order and the uniform cap of their ratios, the two signed-side weighted bounds for the old row away from the central pair, the coefficientwise near-lag bound, and the weighted far-lag bound. No exterior root or exact sign is assumed.

Use the [common-pin setup](../common-pin/README.md) with Lean 4.33.1 and the mathlib revision recorded there. Run the thin driver from the repository root with a fresh project path. It accepts the optional frozen import-object archive used by the shared driver.

```sh
python3 -Bu topics/long-cycle-excedances/lean/front-envelope-sums/check.py /path/to/fresh/project
```

The [workflow](../../../../.github/workflows/long-cycle-front-envelope-sums.yml) compiles the shared modules before checking the six modules here, records input SHA-256 values, checks the declared axiom reports and replays each new module with the pinned `leanchecker`.
