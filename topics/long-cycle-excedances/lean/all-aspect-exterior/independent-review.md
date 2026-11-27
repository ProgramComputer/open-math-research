# Independent review of the all-aspect exterior witnesses

27 November 2026. Agent-assisted mathematical and source review of commit `f18cc7ada51d94ce122980ceb259b5c8b1de69fd`. I found no mathematical gap. The argument establishes the proposed exterior witnesses for old size $n\ge10{,}000$ and $2\le k\le n$. This review checks the logic and the exact arithmetic. It does not independently rebuild the integrated Lean theorem.

## The second grid and the endpoints

Write $d=k-1$, $m=n-d=n+1-k$, $a=kp/n$, and $L=[t^p]V/p^n$, where $V$ includes the insertion factor of $t$. In the active case $2k\le n+1$, we have $m\ge k\ge2$, $m\ge(n+1)/2$, and $2d\le n-1$. The front rank restriction $1\le p\le\lfloor\sqrt n/2\rfloor$ gives $200p\le n$. Split at $p=50$ and use $n\ge10{,}000$ below that split and $4p^2\le n$ above it. Consequently $100(p-j)\le m$ at every sample. The residual acceptance estimate applies to the residual word of size $m$ on $i=p-j>0$ colors and gives real count at most $151m i^{m-1}/(100k)$. At $j=p$, the residual has no words because $m>0$, and $i^{m-1}=0$ because $m-1\ge1$. Thus that endpoint is also zero after cancellation. At $j=0$, $j^d=0$ since $d\ge1$. In particular for $p=1$ these are the only two points, both grids and the full lag coefficient are zero, and the old coefficient is exactly one. Rank $p=0$ uses the separate global lag bound and requires no normalization.

The original transformed successor difference bounds the untransformed nonnegative full lag. After replacing the residual count by the bound above, use $m\binom nd=n\binom{n-1}d$. The residual powers now sum to $d+(m-1)=n-1$, so division by $p^n$ leaves a factor $1/p$. Multiplying by $a$ cancels the remaining factor $n/(kp)$ and yields $aL\le(151/100)B_{n-1,d}$. The upper bound one for residual acceptance gives $L\le B_{n,d}$. When $n+1<2k$, the residual size lies in $[1,k-1]$ because $k\le n$. The lag then vanishes at every rank. The equality case $2k=n+1$ uses the active grids with $m=k$ and $2d=n-1$.

## Scalar and coefficient lower bound

For $k\ge151$ in the active case, both binomial sizes $N=n,n-1$ satisfy $2d\le N$, $d\ge150$. Their densities have interior mode $d/N$ and zero endpoints. The supplied frozen atom bounds the maximum by $\sqrt N/(2\sqrt{d(N-d)})\le1/\sqrt{300}<29/500$. The latter strict inequality follows by squaring positive quantities. The unimodal mesh costs one maximum plus $p$ times the Bernstein integral $1/(N+1)$, so both sums are at most $p/n+29/500\le1/200+29/500$. Multiplying the old lower envelope by its denominator and combining the separate estimates for $L$ and $aL$ gives

$$
\frac{L}{\alpha}\le
\frac{100}{99}\left(1+\frac83\frac{151}{100}\right)
\left(\frac1{200}+\frac{29}{500}\right)
=\frac{2639}{8250}=\frac8{25}-\frac1{8250}.
$$

For $2\le k\le150$, $a\le3/4$ follows from the same sample-size bound. The first grid is at most $1/500$ by the lower-tail tilt and geometric sum, including the zero endpoints. The old lower envelope gives $\alpha\ge33/100$, so this alone strictly improves $8\alpha/25$. The high-cutoff vanishing branch gives the strict inequality by positivity of $\alpha$.

To check the strengthened old lower coefficient, let $f$ be the length-only acceptance probability and $b=\lceil4a/3\rceil$. For $4k\le3n$ one has $b\le p$, including equality. The marking comparison uses the orbit-only lower mass $1/(2b-1)$, subtracts the strict error $1/[250(2b-1)]$, and then uses $(2b-1)(f-\alpha)\le3/4000$. This gives $(2b-1)\alpha\ge99/100$ and $2b-1\le1+8a/3$. The all-color cycle event has probability $1/p$ and guarantees acceptance for every word because $k\le n$. Since $p(f-\alpha)\le3/4000$, it alone gives $p\alpha\ge99/100$. It applies whenever $p\le1+8a/3$, including the other branch $4k>3n$. It also applies whenever $b\ge p$: the integer ceiling then implies $p-1<4a/3$, hence $p<1+8a/3$. Thus the single-cycle argument only uses a subset of accepted outcomes, and needs no assertion that every accepted outcome has one color cycle.

## Witness scope and earlier proof

At zero-based index $i$, the coefficient pair is at $h=i+1$ and $h+1$. The strict endpoint error bounds give an old root in the open box and the literal successor sign $(-1)^{i+2}$. Strict separation of positive adjacent centers orders all $H$ boxes. The modulus cap lies strictly below the integer seam at angle $(H+1)\pi/n$, with positive seam log. The final Lean declaration `original_all_aspect_exterior` supplies $H$ distinct increasing positive moduli, the old-root equations and these strict successor signs before the seam. The preceding `original_exterior_root_witnesses_all` supplies the open boxes for the same chosen roots. The final declaration itself does not state the boxes.

The witness statement gives at least $H$ distinct exterior roots, without asserting simplicity, uniqueness within the boxes, exact absolute rank, absence of additional exterior roots, or any middle or reflected family. In particular, discussion of “the first $H$” should refer to the ordered witness list. The existing written `effective-front.md` starts at $k=3$ and also proves simplicity and rank by complex root counting, successor placement, and reflection. The new explicit domain includes $k=2$ and its claim for $k\ge3$ is weaker than the earlier written theorem. It packages a different lag argument and a candidate formal verification of the exterior witnesses. Full interlacing still needs the middle and center interfaces. [Prior written theorem](https://github.com/ProgramComputer/open-math-research/blob/f18cc7ada51d94ce122980ceb259b5c8b1de69fd/topics/long-cycle-excedances/effective-front.md) · [Frozen atom](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/BandBinomial.lean#L77-L86)

## Exact arithmetic

For $n+1<3k$, at most two cycles are possible in either row. A cycle on a fixed set of size $r$ contributes $tA_{r-1}(t)$, since starting at the largest label gives one compulsory last-to-first ascent and one compulsory initial descent, with the other ascents counted by the Eulerian polynomial. In the checked candidate, the ordered support sum counts each two-cycle permutation twice, including equal lengths, so dividing by two is valid. The lag uses $\binom n{k-1}$ choices of the $k-1$ old labels joined by the new one. Its product of two cycle polynomials agrees coefficientwise with the insertion difference $`c'_{p}-pc_p-(n+1-p)c_{p-1}`$. The four large examples include $n+1=2k$ with a new two-cycle row at $(10001,5001)$, a two-cycle old row at $(10000,5000)$, strict zero lag at $(10000,5002)$, and several allowable two-cycle size pairs at $(10008,5000)$.

The checked-in exact checker was rerun against its recorded output. A separately written oracle generated the required Eulerian prefixes by the Eulerian recurrence and summed unequal-size supports directly, halving only the equal-size split. It reproduced the four old-row, new-row and lag digests through rank 50 and independently checked the insertion differences and the strict relative bound. The candidate checker also compared all 33 small complete rows with literal permutation enumeration. These checks concern the arithmetic and the enumerator conventions. The infinite root statement is supported by the argument above.

For the repository replay, run the following from the repository root at the reviewed commit. The checker and expected output had SHA-256 values `eec74c02b190860cc964ddb557efd215c81a77775475638decc6b7d9b981e670` and `389253347d9587c705d5d0c72d3ca5c00358537285729638c86fce71a44a19b8`, respectively. The independent recurrence script had SHA-256 `93868ccce4f78a3ac590e0fcc777cedc1d219b62ac597f0515f10e744928603c`.

~~~sh
python3 -I topics/long-cycle-excedances/lean/all-aspect-exterior/check-half.py |
  diff -u topics/long-cycle-excedances/lean/all-aspect-exterior/check-half-output.txt -
~~~
