# Low-height exterior certificate from dominant monomials

For old size $n$ and minimum cycle size $k$, put $H=\lfloor7\sqrt n/20\rfloor$.
The certificate treats the actual consecutive pair at fixed $k$. It certifies
the first $H$ old roots in increasing modulus as simple and negative, with
their signs in the new reduced row equal to $(-1)^h$ at rank $h$. It also
certifies that the new root of rank $h$ lies strictly before the old root,
and all remaining new roots lie after the old root, in modulus. The last old
root in the front is before the common-circle entrance
$t_{\ast}=-\exp[-\pi\cot((H+5/6)\pi/n)]$. Reflect for the far end. This
supplies an exterior input, with the central and middle roots requiring
a separate argument.

## Certificate

Use the exact positive coefficients $c_p=[t^p]E_{n,k}$ and
$c_p^{\prime}=[t^p]E_{n+1,k}$. At index $h$ form the rational adjacent balances
$u=c_h/c_{h+1}$ and $v=c_h^{\prime}/c_{h+1}^{\prime}$. Certify $v<u$ and then set
$L=(u+v)/2$, $R=u+(u-v)/2$. For both rows the test bounds the sum of
the moduli of all monomials except the two at $h,h+1$ on the
circles of radii $L$ and $R$. The four required strict dominances are

| Row | At $L$ | At $R$ |
| --- | --- | --- |
| Old | $c_h L^h$ | $c_{h+1}R^{h+1}$ |
| New | $c_{h+1}^{\prime}L^{h+1}$ | $c_{h+1}^{\prime}R^{h+1}$ |

Each entry exceeds the sum of all other monomial moduli in its
row at its indicated radius. Rouché's theorem counts $h,h+1$ zeros
of the old row in the two disks and $h+1$ of the new row in each.
There are no zeros on the circles. The zero at zero is included
in each count. The old annulus therefore has exactly one root
counting multiplicity. The dominant monomials give opposite old
signs at $-L,-R$, so this root is negative, simple and of rank $h$
in modulus. The new polynomial is nonzero throughout the annulus
and has the sign of $c_{h+1}^{\prime}(-L)^{h+1}$ at its old root. Division by
$t$ yields $(-1)^h$. The counts also establish the assertion about
the new roots' moduli. If the middle theorem is used to verify all
roots, these counts give the ordinary strict order at both ends.

Use computed terms from $p=\max(1,h-3)$ to $p=h+4$. Any omitted
nonnegative coefficient is at most $p^N$ in a size $N$ row. Cut
each cycle at the ascents, which are precisely the excedance
edges. There are $p$ nonempty decreasing runs in total since
every cycle has length at least three. Label the runs by $p$
distinct colors. The assignment of the $N$ labels to colors
and the successor permutation on the colors jointly determine
the original permutation. Each run is read in decreasing order,
and its successor is recorded by that permutation on colors.
Thus each original permutation yields $p!$ distinct pairs of
assignments and successor permutations, among at most $p^N p!$
such pairs. This is the coefficient bound used in the published
front result.

The sequence $p^N y^p$ for $y=L,R$ has decreasing successive
forward ratios. Each omitted tail is consequently bounded by its
first term divided by one minus the ratio to the second term
(when proceeding away from the retained interval). Each ratio is
tested to be strictly below one. Arb checks the rational dominances
by outward enclosure and checks the trigonometric entrance by the
same interval arithmetic. An undecidable inequality counts as a
failure. The last right radius comparison $R_H<|t_{\ast}|$ suffices
because every smaller old root has modulus below the rank $H$ root.

For $n\ge251$, the entrance itself has $n\sin^2\theta_{\ast}>1$. In
fact $\sqrt n\ge15$ gives
$(61/180)\sqrt n<h+5/6\le (73/180)\sqrt n$ for $h=H$,
so $\theta_{\ast}\le(73/2700)\pi<.086$ and
$\sqrt n\sin\theta_{\ast}\ge (61/180)\pi(1-.086^2/6)>1$.
Phase modulation still has to be checked in the middle argument.

## Coefficient generation

Let $A_{j-1}$ be the ordinary Eulerian row at size $j-1$. A
single $j$-cycle on fixed labels contributes $tA_{j-1}$. Start
above half the maximal new size, where every nonzero row is
single-cycle. On descending from cutoff $k+1$ to $k$, add $a$
cycles all of size $k$ with multiplicity
$\binom{N}{ak}(ak)!/((k!)^a a!)$. Multiply their weights and
the residual row at cutoff $k+1$. On the reduced rows $E/t$,
the shift is $a$ when the residual is nonempty and $a-1$ when
it is empty. Updating sizes in descending order retains the
required old residual. Polynomial arithmetic is over exact
integers, truncated only above the retained prefix.

Run with python-flint 0.9.0, FLINT 3.6.0.

```sh
python check.py 251 1000
python check-prefix.py
```

The primary run selects only $k\ge4$ and $n\ge4k$, since the
reviewed lower-cycle theorem covers the other pairs. Old sizes
through 250 were separately certified in full by reciprocal
reduction. The prefix cross-check uses the independent insertion
recurrence for its specified cutoff sample. The [independent review](review.md)
links a separate replay covering the entire certified range.

## Completed range

All 114,750 remaining pairs with old size $251\le n\le1{,}000$
passed, a total of 991,894 tested exterior ranks on one side.
The run used 104.70 seconds and 51.0 MB of maximum resident
memory. [Sign log](check-251-1000.txt)

The independent insertion comparison matched 15,685 whole
width-15 prefixes through row 1,001 at 17 cutoffs.
[Coefficient replay](prefix-output.txt)

The [four-term replay](fast.py) retains only indices from
$\max(1,h-1)$ to $h+2$, with the same geometric majorants
beginning one index earlier. For small cutoffs it uses the
insertion recurrence to generate all rows in a single pass.
It repeated the complete calculation in 34.57 seconds and
52.8 MB maximum resident memory. [Sign log](fast-251-1000.txt)

```sh
python fast.py 251 1000
```
