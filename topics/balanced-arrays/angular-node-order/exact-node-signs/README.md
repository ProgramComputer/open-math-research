# Signs at exact angular nodes

Let $c_j$ count labeled $n\times d$ binary arrays with $j$ ones in each column and at most $r$ ones in each row. Put $D=\lfloor nr/d\rfloor$ and $P(q)=\sum_{j=0}^D c_jq^j$. For $1\le k<D$, the target is the sign of $P(-w_k^d)$ at the unique positive solution of $\Psi(w_k)=k\pi$, where

$$
\begin{aligned}
\theta&=\pi/d,\qquad \nu=(d-1)/2,\\
H(z)&=\sum_{j=0}^{r}\binom dj z^j,\qquad
B(z)=\sum_{j=0}^{r-1}\binom{d-2}{j}z^j,\\
\Psi(w)&=(n+\nu)\arg H(we^{i\theta})-\nu\arg B(we^{i\theta})-\nu\theta.
\end{aligned}
$$

The checker uses the [strict phase ordering theorem](../README.md) to identify each bracketed zero with its labeled node.

**Formal verification**　⬜ None. The certificates use MPFR directed rounding and exact integer arithmetic.

## Certified scope

At every node in these ledgers, $(-1)^kP(-w_k^d)>0$.

| Input family | Triples | Internal nodes certified | Reversals | Unresolved |
| --- | ---: | ---: | ---: | ---: |
| [Pinned sample archive](replay.csv.gz) | 745 | 9,162 | 0 | 0 |
| [Rank-one extension](rank-one.csv.gz) | 234 | 2,404 | 0 | 0 |
| [Corank-one extension](corank-one.csv.gz) | 71 | 1,690 | 0 | 0 |
| [Corank-one saturation crossover](corank-crossover.csv.gz) | 8 | 275 | 0 | 0 |

The four ledgers contain 13,531 certificates for 13,459 distinct nodes. The extensions contribute 4,297 distinct nodes outside the original archive.

The archive covers $2\le n\le 48$ and $2\le d\le \min(n,10)$ at ranks one and corank one, together with 18 coefficient vectors from the repository's 36-row inventory. The checker covers every archived quota. It reconstructs rank-one and corank-one coefficients from their endpoint formulas and checks the 18 other vectors against the pinned inventory. The original rational samples choose nearby brackets. Neither the signs recorded in that archive nor the search arithmetic enters the enclosure calculation.

The rank-one extension includes dimensions through $1024$ and heights through $22{,}527$. It samples dense cases at $n/d$ near fixed small integers and cases at heights near $d^2/2$, $d^2$, $2d^2$, and $4d^2$. The corank-one extension examines dimensions through $256$, including heights near $d$ and $2d$ as well as moderately tall cases. The corank-one crossover uses heights $d^2$ and $d^2+1$ in dimensions $9,13,19,23$. It also samples around $k=n^{1-1/d}$, where the expected number $n(k/n)^d$ of full rows of an unrestricted balanced array passes one. `make_input.py` specifies each finite family and the quotas. It uses all internal quotas through degree 24, then selected upper and lower edge quotas and evenly spaced bulk quotas. Coverage of the larger parameters is confined to these finite families.

The coefficient at quota $j$ for rank one is $n!/((j!)^d(n-dj)!)$, since the $d$ labeled column support sets must be disjoint. At corank one the row cap forbids full rows. Inclusion–exclusion over their locations gives $\sum_{a=0}^j(-1)^a\binom na\binom{n-a}{j-a}^d$. The input script evaluates these formulas with exact integers.

## Why the enclosures certify the signs

MPFR's downward and upward rounding gives dyadic intervals enclosing $\pi$ and the coefficient real and imaginary parts $\binom tj \cos(j\pi/d)$ and $\binom tj \sin(j\pi/d)$. All angles are between zero and $\pi$. Cosine decreases on that interval. The program checks that the sine interval lies wholly on the increasing or decreasing side of $\pi/2$ before using endpoint evaluation, and uses the exact value one at $j=d/2$. Exact integer coefficients use GMP before conversion to MPFR intervals.

At a positive dyadic tilt $w$ the program evaluates both parts of each row polynomial by outward Horner arithmetic. For any row polynomial of positive degree, the imaginary part is positive because every nonconstant term has angle strictly between zero and $\pi$. The checker requires a strictly positive lower endpoint for that part. The arguments continued from $w=0$ therefore agree with the values of positive-half-plane `atan2`. On $y>0$ this function decreases in $x$ and has derivative in $y$ with the sign of $x$. Choosing the resulting extremal box corners gives an outward interval for each argument. The argument of the constant row polynomial is zero.

The phase comparison is made with the interval for

$$
(2n+d-1)\arg H-(d-1)\arg B-(2kd+d-1)\theta = 2(\Psi-k\pi).
$$

The checker retains endpoints $\ell,u$ only when the phase comparison is strictly negative at $\ell$ and strictly positive at $u$. Bisection can change an endpoint only after another strict MPFR comparison. Continuity and strict ordering give $\ell<w_k<u$.

For any $w\in[\ell,u]$, the checker encloses $w^d$ using its monotonicity for positive arguments. Outward Horner arithmetic with the interval $-[\ell^d,u^d]$ encloses $P(-w^d)$ on the whole bracket. Acceptance requires an interval strictly on one side of zero. Each CSV row records $n,d,r,k$, the certified sign, the refinement count, both bracket endpoints and the polynomial interval endpoint closest to zero. The last three fields are exact hexadecimal dyadics. The program checks MPFR's range and domain flags and exits with failure if a node remains unresolved.

An independent archived-polynomial check reads the exact recorded dyadic endpoints. It evaluates the even and odd term sums $E$ and $O$ using integer arithmetic throughout. Both sums increase weakly with $w$, so for every bracket $[\ell,u]$,

$$
E(\ell)-O(u)\le P(-w^d)\le E(u)-O(\ell).
$$

This supplies a second sign check on the entire archived brackets. The phase comparisons on those endpoints were also repeated at 256 bits. That run certified the same signs and selected identical brackets.

## Reproduce

The [input script](make_input.py) reuses the two tracked ledgers below. It checks their SHA-256 hashes against the inputs at commit `2cadc6002bda2bec41c982f5899cad820033074e`. Each extended coefficient vector is rebuilt from its triple.

- [Angular sample archive](../screen-angular-signs.jsonl.gz)
- [36-row coefficient inventory](../../finite-36/exact-vectors.jsonl)

Run the following commands from this directory with Python 3, `gzip`, a C11 compiler, MPFR 4.2.0, and GMP 6.3.0. The compile command uses the Homebrew paths from the recorded run. The search and scope of the extension cases are determined by integer or MPFR operations. Compression with `gzip -n` omits the filename and timestamp.

```sh
set -eo pipefail
angular_check_dir=$(mktemp -d)
clang -O2 -std=c11 -Wall -Wextra -Werror \
  -I/opt/homebrew/opt/mpfr/include -I/opt/homebrew/opt/gmp/include \
  verify_nodes.c -L/opt/homebrew/opt/mpfr/lib -L/opt/homebrew/opt/gmp/lib \
  -lmpfr -lgmp -o "$angular_check_dir/verify_nodes"
for family in replay rank-one corank-one corank-crossover; do
  precision=512
  if [ "$family" = replay ]; then precision=128; fi
  python3 -IB make_input.py "$family" | "$angular_check_dir/verify_nodes" "$precision" \
    | gzip -n -9 > "$angular_check_dir/$family.csv.gz"
  cmp <(gzip -dc "$family.csv.gz") <(gzip -dc "$angular_check_dir/$family.csv.gz")
done
python3 -IB check_replay_integers.py "$angular_check_dir/replay.csv.gz"
python3 -IB make_input.py replay | "$angular_check_dir/verify_nodes" 256 \
  > "$angular_check_dir/replay-256.csv"
cmp <(gzip -dc replay.csv.gz | cut -d, -f1-8) <(cut -d, -f1-8 "$angular_check_dir/replay-256.csv")
```
