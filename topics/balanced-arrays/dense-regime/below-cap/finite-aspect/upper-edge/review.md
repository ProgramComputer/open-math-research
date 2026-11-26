# Independent review of the row-deficit theorem

Agent-assisted review by Codex (`edge_referee`), 2026-11-26.

I accept the curvature inequality and the simple negative outer-root count for the original labeled balanced-array polynomial. For $`n,d\ge2`$, $`1\le r<d`$, and $`1\le k<D=\lfloor nr/d\rfloor`$, put $`c=d-r`$, $`R=rc/d`$, and $`e=nr-dk`$. The reviewed estimate is

$$
\frac{a_k^2}{a_{k-1}a_{k+1}}\ge\left[\frac{k+1}{k}\left(1+\frac HB\right)\right]^d\quad\text{if } X<1,
$$

where

$$
\begin{aligned}
\delta(s)&=\min\left\lbrace \frac{s(s-1)}{Rn(n-1)}+\frac{s}{nR}+\frac{2s}{nr},\left(\frac2R+\frac2r\right)\frac{s(s-1)}{n(n-1)}\right\rbrace ,\\
X&=\delta(e)(n+e+d-1)/d,\\
H&=\frac{cn(n-1)(1-X)}{(n+e-1)(n+e+d-1)},\qquad B=\min\lbrace n-k,(c+1)e/d+1\rbrace .
\end{aligned}
$$

I checked the regular-margin switching ratio, including the negative correlation of marked cells and the conditional Bernoulli representation of the overlap. The dummy row converts mixed column margins to regular margins. Allowing all choices of high columns introduces a factor depending only on their number, which cancels in each row-profile comparison. The conditional split of two row deficits is symmetric and unimodal. Summing its endpoint deficit over partner rows gives the stated bounds for the expected count of nonsaturated rows. For each extension, the conditional availability difference between a low and a high column is the fraction of active singleton rows. The reverse deletion has exactly the new quota as its multiplicity. Thus the two extension paths telescope with the stated gain and denominator. At an internal quota all the denominator availabilities are positive, including when the last extension reaches saturation.

Under $`X<1`$ and $`dH/(B+H)>\log9`$, the curvature is strictly above nine. The test persists at higher internal quotas since $`H`$ increases and $`B`$ decreases. At each certified geometric circle, the central monomial strictly dominates the sum of the other magnitudes by log-concavity. Its disk count and negative-ray sign isolate one simple negative root per successive outer interval, giving the claimed $`D-k`$ roots. [Manuscript](paper.tex)

I checked both stated sufficient conditions.

- For $`n\ge d\ge4`$, $`256e(1+e/n)^2\le d\min(r,c)`$ gives $`X\le1/32`$ and $`B/(dH)+1/d\le11/32<1/\log9`$. When $`\min(r,c)/d`$ stays bounded below, this certifies order $`\min(d,(n^2/d)^{1/3})`$ outer roots uniformly for $`d\le n`$ as $`d\to\infty`$, irrespective of the residue of $`nr`$ modulo $`d`$.
- For $`n\ge d^2`$, $`d\ge16`$, $`d/4\le r\le3d/4`$, and $`e\le d^2/16`$, the second bound on $`\delta`$ gives $`X\le21/256<.1`$ and $`H>c/2`$. It follows that $`B/(dH)+1/d<1/4`$. When $`n=d^2`$ this certifies at least $`\lfloor d/16\rfloor`$ outer roots.

For $`(n,d,r)=(10^6,250000,127000)`$ I independently enclosed $`n\Pr(\mathrm{Bin}(d,(k+3)/n)>r)`$ by integer summation from the first tail term. Its enclosure lies below $`1/100`$ at $`k=502387`$ and above $`1/100`$ at $`k=502388`$. For $`k=507905`$, the rational comparison gives $`X<1`$ and $`2.2073<dH/(B+H)<2.2074`$. The certified inner and outer intervals contain 502,387 and 95 simple negative roots respectively, giving 502,482 of degree 508,000. Their intervening annulus contains exactly 5,518 roots counted with multiplicity. The types of those roots remain unclassified. [Exact threshold and root-count checker](verify.py)

Both checker replays passed. The direct profile enumeration checks 84 feasible cap-margin cases and 72 positive extension identities, from 12,074 labeled arrays before imposing the cap. The finite checks supplement the analytic proof. Formal verification status is ⬜ None. [Direct profile enumeration](verify-profiles.py)

| Reviewed file | SHA-256 |
| --- | --- |
| [paper.tex](paper.tex) | `1d18dbe32a53a8758e240d494fefbd9fd2fd90abdd5bed3600583d4176e1dd3a` |
| [verify.py](verify.py) | `5764f0ceb5da5626d8c916f693ae8e34a2bbcfc2a67650040fc4f4d4a3ae36ad` |
| [verify-profiles.py](verify-profiles.py) | `a560e21b1944891161c10feedf8a7b2e7adf7caf71979ac04285947d84000e37` |
