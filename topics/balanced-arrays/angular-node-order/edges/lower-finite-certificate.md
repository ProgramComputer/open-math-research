# Exact finite certificate for the lower angular signs

Write $T_m=(U_{d,k}^m/m!)^d$ with
$U_{d,k}=((\pi/d)/\sin(\pi/d))(k+(d-1)/(2d))$.
The [gamma-mixture proof](lower-gamma-mixture.md) leaves these two
ranges for finite checking.

| Dimension | Quota | Pairs |
| --- | --- | ---: |
| $3\le d\le7$ | $d/4<k<100d$ | 2,491 |
| $8\le d\le127$ | $d/4<k<128$ | 13,260 |

Both independent programs give a strictly positive lower bound
for $(-1)^k\sum_{m\ge0}(-1)^mT_m$ on all 15,751 pairs.

## Outward-rounded integer computation

The [Python verifier](verify-lower-gamma.py) encloses all quantities
on a dyadic grid of step $2^{-b}$. Machin's identity gives an
interval for $\pi$ using alternating arctangent series. The verifier
encloses sine with its alternating Taylor series at the lower
endpoint of the angle interval, then enlarges by the angle error
using the Lipschitz constant one. Positive interval multiplication
and division enclose $U=U_{d,k}$ and $U^d$.

Divide the signed series by the positive center term $T_k$. At
offset $j\ge1$, the two terms have sign $(-1)^j$. Their normalized
magnitudes are enclosed using the ratios
$((k-j+1)/U)^d$ to the left while $j\le k$, and
$(U/(k+j))^d$ to the right. Left terms past $j=k$ are zero.
Even offsets use lower endpoints and odd offsets use upper endpoints
to accumulate a lower bound on the signed partial sum. For
acceptance the truncation offset $j$ must be odd and the upper
endpoint of $U$ must be at most $k+j+1$. The first omitted terms
on either side then have positive sign, and the outward magnitudes
are nonincreasing. On the right this uses $U\le k+j+1$, and on
the left it uses the checked inequality $U\ge k$. Pairing each
first positive omitted term with the following negative term
gives nonnegative tails. Absolute convergence justifies the
pairing on the right.

A strictly positive dyadic lower endpoint therefore certifies
the entire normalized signed series. Precision, truncation limits,
and the early exit for terms too small to improve the current
enclosure only govern which attempts the program makes. An
unsuccessful attempt, or hitting a threshold, does not certify a
sign. A pair unresolved at every tested precision raises an error.

The [compressed ledger](lower-gamma-signs.jsonl.gz) stores one
row $[d,k,b,j,e]$ per accepted pair. The final integer endpoint
implies a lower bound of $2^e$ after the central normalization.
The largest precision is 1,536 bits and the largest certified offset
is 479. The SHA-256 digest of the uncompressed ledger is
`9e3a446f9b90daee2579de1e322a1cbc91bc0f216a016fca67fa286c28704d88`.

From this directory, replay with Python 3 in standard mode so the
arithmetic assertions are enabled.

~~~sh
replay_dir=$(mktemp -d)
python3 -IB verify-lower-gamma.py "$replay_dir/lower-gamma-signs.jsonl"
gzip -dc lower-gamma-signs.jsonl.gz | cmp - "$replay_dir/lower-gamma-signs.jsonl"
gzip -n -9 -c "$replay_dir/lower-gamma-signs.jsonl" | cmp - lower-gamma-signs.jsonl.gz
~~~

## Independent directed-rounding check

The [independent C verifier](lower-independent/README.md) instead
sums the unnormalized series from $m=0$ with directed MPFR
rounding. Its accepted last index has opposite parity to $k$ and
lies beyond the upper endpoint of $U$. The ordinary alternating
tail then has the desired sign. This checker also requires a
strictly positive lower endpoint. Its archived output certifies
15,751 pairs, with maximum final indices 1,066 and 184 for the
two ranges respectively.
