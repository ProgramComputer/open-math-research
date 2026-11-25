# Balanced arrays with at most 24 rows

**Theorem.** For $0\le n\le24$, every positive dimension $d$ and every cap $1\le r\le d$, the balanced-array polynomial has only real zeros. For $d\ge2$ every zero is simple and negative. For $d=1$ the polynomial is $(1+q)^n$. This computer-assisted result has no checked Lean or Rocq proof. [Definition and formal scope](README.md)

For $m\ge1$ and $A>m-1$, the symbol for the coefficient multiplier $\binom Ak$ is
$$
\sum_{k=0}^m\binom mk\binom Ak q^k=(1-q)^m P_m^{(0,A-m)}\!\left(\frac{1+q}{1-q}\right).
$$
Jacobi orthogonality gives $m$ distinct negative roots after the displayed change of variable. The finite Schur–Szegő composition theorem therefore makes multiplication by $\binom Ak$ a preserver of negative real-rootedness on polynomials of degree $m$. At $r=d$, apply the multiplier $A=m=n$ to $(1+q)^n$ a total of $d-1$ times, giving the coefficients $\binom nk^d$. At $r=1$, the columns use disjoint $k$-subsets, giving $n!/((n-dk)!(k!)^d)$. Write $n=dm+s$, $0\le s<d$, and set $A_j=(n-j)/d$ for $0\le j<d$. Since $A_s=m$, grouping the factorials modulo $d$ expresses the coefficient as $d^{dk}\prod_{j=0}^{d-1}\binom{A_j}{k}$. Start with $(1+q)^m$, apply the $d-1$ multipliers with $j\ne s$, and scale the variable by $d^d$. [Jacobi expansion](https://dlmf.nist.gov/18.5.E8) · [Zeros of orthogonal polynomials](https://dlmf.nist.gov/18.2.vi) · [Schur–Szegő composition](https://www.numdam.org/item/CRMATH_2008__346_5-6_271_0.pdf)

For simplicity, assume $d\ge2$ and positive degree $m$. The first of the $d-1$ binomial multipliers sends $(1+q)^m$ to a Jacobi symbol with $m$ distinct negative roots. Each subsequent multiplier is an invertible diagonal linear map on the space of coefficient vectors of length $m+1$ and preserves polynomials of degree $m$ with negative roots and positive leading coefficient. The interior of this latter set consists exactly of polynomials with simple negative roots. This follows by continuity of simple roots and, at a repeated root $x$, perturbing a factor $(q-x)^2$ to $(q-x)^2+\varepsilon$ with $\varepsilon>0$. An invertible linear map preserving a set sends its interior into the interior. Positive rescaling of the variable in the cap-one case preserves simplicity. The degree-zero case is immediate.

For $n\ge1$ and $d\ge n$ the universal normalized log-concavity theorem bounds every internal coefficient ratio $a_k^2/(a_{k-1}a_{k+1})$ below by $(1+2/n)^{2d}\ge1+4d/n\ge5$. Strict separation by a factor exceeding four gives simple negative zeros. For $n=0$ the polynomial is one. Thus the remaining finite domain is exactly $1<r<d<n\le24$. Its size is $\binom{23}{3}=1771$. [Normalized log-concavity](orientation-normalization.md)

For each remaining triple set $D=\lfloor nr/d\rfloor$. At an internal index $k$ the stronger lower bound is
$$
\left(\frac{(k+1)(n-k+1)}{k(n-k)}\right)^d.
$$
The expression inside parentheses equals $1+(n+1)/(k(n-k))$ and is smallest at $\min(D-1,\lfloor n/2\rfloor)$. An exact integer comparison at this index suffices. In the archive, 1,641 triples pass the strict test. For the other 130, the full coefficient vectors were counted by two methods and the full degree of simple negative roots was verified by exact root counts. The archive records a method for each triple and the coefficients and Sturm report for each exception. [Complete finite archive](results/linear_tail_ranges.jsonl) · [Verifier](verify_small_rows.py)

A separate replay computed a rational Sturm chain for each of the 130 exceptions and checked all 1,641 separation tests directly from binomial coefficients. The package verifier recomputes every exceptional coefficient from labeled column choices and checks the exact Sturm root counts. From the repository root, install python-flint 0.9.0 and run

~~~sh
python -I -O topics/balanced-arrays/verify_small_rows.py
~~~
