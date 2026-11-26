# Independent agent-assisted check of common pair-weight counterexamples

In a labeled $n\times 4$ binary array with equal column sums $k$ and row cap two, give every two-one row the common weight $t$ and each other row weight one. Let $a_{n,k}(t)$ be its total weight and $P_n(q,t)=\sum_k a_{n,k}(t)q^k$.

The degree-16 rows at the following points are square-free and have exactly 14 negative real roots and one nonreal conjugate pair.

| $n$ | $t$ | Certificate |
|---:|---:|---|
| 33 | $264$ | [Original weighted example](weight-264-row-33.json) |
| 32 | $216$ | [Lower row count](weight-216-row-32.json) |
| 33 | $176$ | [Smaller integer weight](weight-176-row-33.json) |
| 32 | $431/2$ | [Rational weight](weight-431-over-2-row-32.json) |
| 33 | $351/2$ | [Rational weight](weight-351-over-2-row-33.json) |

## Independent counts

Split the columns into $12\mid34$. Let $a$ be the number of rows consisting of the pair $12$ and $b$ the number consisting of $34$. Choose those rows in $\binom na\binom{n-a}b$ ways. On the remaining $L=n-a-b$ rows let $r=2(k-a)$ and $s=2(k-b)$ be the numbers of occupied positions in the two column pairs. Each pair can use any support of the required size because these remaining rows contain at most one entry from each pair. If the supports intersect in exactly $h$ positions, the count of ordered supports is $\binom Lr\binom rh\binom{L-r}{s-h}$. The assignments to individual columns have counts $\binom r{r/2}$ and $\binom s{s/2}$. The two-one rows are exactly the $a+b$ chosen rows and the $h$ intersections, so the contribution has weight $t^{a+b+h}$. Summing this expression over $a,b,h$ reconstructs $a_{n,k}(t)$ directly from the array definition. This primary computation uses row supports. A separate recurrence for labeled matchings, followed by row injection and the exact quota-factorial quotient, independently reproduces every coefficient in the recorded weight-polynomial vectors.

For a rational weight $t=A/B$ with $B>0$, the integer certificate uses $P_n(B^2q,A/B)$. Each coefficient is obtained by replacing $t^p$ by $A^pB^{2k-p}$ in the $k$th entry. The change of variable preserves the root counts, and $p\le2k$ ensures integer exponents.

## Exact root certificate

A signed Sturm sequence starts with the coefficient polynomial and its derivative. The next polynomial is the negative remainder. The checker carries out remainder subtraction using integer arithmetic, multiplying at each elimination by the positive absolute value of the divisor's leading coefficient and removing positive content. This yields a positive multiple of the negative rational remainder with the same signs. A second replay using rational FLINT arithmetic gave the identical sign strings.

For all five certificates the sign variations at $-\infty$, $0$ and $+\infty$ are $(15,1,1)$. The last Sturm polynomial is a nonzero constant, which establishes square-freeness. The constant coefficient of each row is one. Thus precisely 14 roots are real, all negative. No floating-point root approximation enters the certificate.

The reconstructed [unweighted rows](unweighted-26-33.json) at $t=1$ agree coefficient by coefficient with the published original vectors for $26\le n\le33$ and have full distinct negative root counts.

## Search range and scope

An exact scan by Sturm counts at integer weights $2\le t\le264$ found no failure for $26\le n\le31$. The first failures were at $216$ and $176$ for rows 32 and 33, respectively. A cheaper negative-discriminant scan for $26\le n\le31$ through integer weight 2048 found no negative discriminant. That test alone does not certify real-rootedness on the extended range. The searches give no minimality result over all positive real weights or over lower rows outside the tested range.

The examples concern the symmetric extension with **all** pair types given the same tunable weight. They do not refute the unweighted conjecture at $t=1$, the deformation weighting only the two pure pair types, or the negative-rootedness of an individual fixed-singleton symbol. They do obstruct proving the original weighted sum by arbitrary positive compatibility of the fixed-total singleton slices. Indeed, after $q\mapsto q/t^2$, a matching with $2s$ singletons contributes the slice weight $t^{-s}$. The examples show that even this geometric weighting of the slices can give nonreal roots.

## Reproduction and data

The stand-alone checker is `verify_common_pair.py`. Its default location for the source unweighted archive is `../results/four_column_mehler.jsonl` relative to the script. The results may be kept together in a single directory. For example, from the repository root:

```sh
python3 -I -B topics/balanced-arrays/code/verify_common_pair.py \
  --verify-examples topics/balanced-arrays/results/common-pair
python3 -I -B topics/balanced-arrays/code/verify_common_pair.py --unweighted \
  | diff topics/balanced-arrays/results/common-pair/unweighted-26-33.json -
```

The exact scan record is [common_pair_scan.json](common_pair_scan.json). For each row $n$, its `by_quota[k][p]` stores $[q^kt^p]P_n(q,t)$. This records the coefficient vector at every weight losslessly without repeating large integer evaluations. The scan sections specify the exact method, the inclusive integer ranges or explicit rational weights, and every result. The integer scans store nondefault outcomes alongside the range. Discriminant sign and exact root counts have separate fields. The ledger includes the initial integer discriminant and Sturm scans, the extended disc-sign scan, the dyadic sign probes within $[215,216]$ or $[175,176]$, and the separated integer spot probes.

The scans use python-flint for exact discriminants and rational Sturm remainders. Use the same command to reconstruct the entire ledger and compare it:

```sh
python3 -I -B topics/balanced-arrays/code/verify_common_pair.py \
  --verify-ledger topics/balanced-arrays/results/common-pair/common_pair_scan.json
```

On the host the exact scan took 7.89 seconds and used about 28 MB resident memory. The extended discriminant scan took 6.94 seconds with about 27 MB resident memory. The certificate and unweighted replays use only Python's standard library. No downloads or builds were needed.
