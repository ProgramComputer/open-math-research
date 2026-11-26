# Independent check of the finite sign ranges

Write

$$
F_d(q)=\sum_{m\ge 0}\frac{q^m}{(m!)^d},\qquad
U=\frac{\pi/d}{\sin(\pi/d)}\left(k+\frac{d-1}{2d}\right).
$$

This check certifies $(-1)^kF_d(-U^d)>0$ for the following integer pairs.

| $d$ | $k$ | Certified pairs |
| --- | --- | ---: |
| $3\le d\le 7$ | $d/4<k<100d$ | 2,491 |
| $8\le d\le 127$ | $d/4<k<128$ | 13,260 |
| | **Total** | **15,751** |

## Enclosure and tail bound

The checker rounds every lower endpoint toward $-\infty$ with MPFR's `MPFR_RNDD` and every upper endpoint toward $+\infty$ with `MPFR_RNDU`. The finite MPFR endpoints are dyadic rationals. Directed computations of $\pi$ and division by $d$ enclose $x=\pi/d$. The checker verifies that these endpoints lie in $(0,3/2)$, where sine is increasing. Therefore evaluating sine at the lower and upper endpoints with outward rounding encloses $\sin(x)$. It divides the lower $x$ endpoint by the upper sine endpoint and the upper $x$ endpoint by the lower sine endpoint. Multiplication by the positive rational $(2dk+d-1)/(2d)$ gives the interval $[U_L,U_H]$.

For $t_j=(U^j/j!)^d$, the recurrence $t_0=1$, $t_j=t_{j-1}(U/j)^d$ uses positive inputs and is increasing in both $t_{j-1}$ and $U$. Applying the recurrence with the lower endpoints and downward rounding, and with the upper endpoints and upward rounding, encloses every $t_j$. The checker accumulates the even and odd terms independently through index $m$, yielding enclosures $[E_L,E_H]$ and $[O_L,O_H]$. The partial sum $S_m=\sum_{j=0}^m(-1)^j t_j$ is at least $E_L-O_H$, and its negative is at least $O_L-E_H$.

When the program tests a partial sum, it has verified $m\ge U_H\ge U$ and that $m$ and $k$ have opposite parity. The terms beyond $m$ decrease to zero since $t_{j+1}/t_j=(U/(j+1))^d$ for $j\ge m$. The alternating series bound implies that $F_d(-U^d)-S_m$ has weak sign $(-1)^{m+1}$. Therefore $(-1)^k F_d(-U^d)\ge (-1)^k S_m$. For each accepted pair, downward rounding of $E_L-O_H$ for even $k$, or of $O_L-E_H$ for odd $k$, yields a finite endpoint strictly greater than zero. No tolerance or estimate of the magnitude of the cancellation enters the acceptance test. A failure to find a positive lower endpoint before index 4096, or an MPFR exception other than inexact rounding, aborts the check.

## Reproduction

The recorded run used MPFR 4.2.0, GMP 6.3.0, and Apple clang 21.0.0 on arm64, with a 1,024-bit significand for each MPFR variable. From this directory on the Homebrew installation used for the run:

```sh
clang -O2 -std=c11 -Wall -Wextra -Werror \
  -I/opt/homebrew/opt/mpfr/include -I/opt/homebrew/opt/gmp/include \
  check_lower_signs.c -L/opt/homebrew/opt/mpfr/lib -L/opt/homebrew/opt/gmp/lib \
  -lmpfr -lgmp -o /tmp/open-math-check-lower-signs
/tmp/open-math-check-lower-signs > /tmp/open-math-lower-signs.out
diff -u output.txt /tmp/open-math-lower-signs.out
```

[Recorded output](output.txt) lists the pair counts and maximum certificate indices. This numerical certificate depends on MPFR's directed rounding guarantees and the alternating series bound.
