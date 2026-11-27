# Computing low coefficients at large sizes

Let $E_{n,k}$ be the original strict-excedance enumerator with minimum cycle length $k\ge2$. Write $A_m$ for the ordinary Eulerian polynomial, with $A_0=1$. A cycle of length $j\ge2$ has enumerator $tA_{j-1}(t)$, and a singleton has enumerator one. Removing the singleton cycles from the ordinary Eulerian exponential generating function gives

$$
(1-t)\sum_{a\ge0}t^a\exp\big((a-(a+1)t)z\big).
$$

Exclude the cycles of lengths $2,\ldots,k-1$ by multiplying by $\exp(-\sum_{j=2}^{k-1} t A_{j-1}(t) z^j/j!)$. The result is $\sum_{n\ge0} E_{n,k}(t)z^n/n!$. For target rank $p$, only $0\le a\le p$ contributes. After removing $e^{az}$ from the term indexed by $a$, its remaining factor has $z$-degree at most $(k-1)(p-a)$ at that rank.

The checker expands the residual exponential by distinguishing one label of its first block. For a block of size $j$ among $\ell$ labels, the other labels in the block have $\binom{\ell-1}{j-1}$ choices. Multiplication by $e^{az}$ then uses the factors $\binom n\ell a^{n-\ell}$. All operations use integers. The lag is obtained both from its Eulerian cycle factor and by subtracting the derivative and multiplication terms of the old row from the independently calculated successor. [Source](check-coefficient-prefixes.py)

| Old size $n$ | Cutoff $k$ | Positive ranks tested |
|---:|---:|---:|
| $32001$ | $8$ | $1$ through $24$ |
| $1000000$ | $8$ | $1$ through $12$ |
| $600001$ | $150$ | $1$ through $4$ |
| $1200001$ | $300$ | $1$ through $4$ |

The inequalities are tested on the unreduced coefficients by integer cross multiplication. For each case the output records $n,k,p$ and SHA-256 digests of the complete old and lag prefixes, including rank zero. Each nonnegative integer is encoded in minimal-length big-endian bytes, preceded by its byte count as an eight-byte big-endian integer. The checker also compares full polynomial rows against literal permutations for $0\le n\le8$ and $2\le k<\max(n+2,4)$. [Output](coefficient-output.txt)

~~~sh
python3 -I topics/long-cycle-excedances/color-load-bounds/check-coefficient-prefixes.py \
  --literal --case 32001 8 24 --case 1000000 8 12 --case 600001 150 4 --case 1200001 300 4
~~~
