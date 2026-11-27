# Discrete signed odd-pole moment bounds

Let $k\ge100$, $x\ge44$, $P_j=s+(2j+1)i\pi$, $r=\sqrt{s^2+\pi^2}$ and $S=\pi/r$. Assume $xkS^2\ge1$. Define $f_j=(r/|P_j|)^{k-1}$. Both nonnegative signed series converge, with

$$
 \sum_{j\in\mathbb Z} f_j\le3\sqrt{x},\qquad
 \sum_{j\in\mathbb Z}|2j+1|f_j\le4x .
$$

The two principal terms at indices $0,-1$ each contribute one to both bounds. For row size $n$, substitution of $x=n/k$ gives the conditions $n/k\ge44$ and $nS^2\ge1$. The theorem uses the same literal pole function as the original Fourier coefficient argument.

For a positive nonprincipal label $p=2i+3$, put $B=5x$ and $F(p)=B^2/(B+p^2)^2$. Let $m=\lfloor(k-1)/4\rfloor$. Since $k\ge100$, $25m\ge6k$. The exact ratio square is $[1+(p^2-1)S^2]^{-1}$, so taking the $4m$th power gives an inverse square of the $m$th power of that denominator. Natural Bernoulli and $p^2-1\ge(8/9)p^2$ yield

$$
 [1+(p^2-1)S^2]^m\ge1+m(p^2-1)S^2
 \ge1+\frac{16p^2}{75x}\ge1+\frac{p^2}{5x}.
$$

Since the ratio is at most one, this proves $f_{i+1}\le F(p)$ for the pole of label $p$.

For the first moment, write $H(t)=B^2/(B+t^2)$. The exact difference is

$$
 H(p-2)-H(p)=\frac{4(p-1)B^2}{(B+(p-2)^2)(B+p^2)}
 \ge\frac83 pF(p).
$$

Summing positive nonprincipal labels telescopes to at most $3H(1)/8\le3B/8$. Reflecting the entire half and adding the two principal terms gives $2+3B/4\le4x$.

For the zeroth moment take $L=\sqrt{B/3}\ge8$. The square $(p-L)^2\ge0$ gives $F(p)\le(9/4)L^2/(L+p)^2$. Consequently

$$
 2F(p)\le\frac94 L^2
 \left(\frac1{L+p-2}-\frac1{L+p}\right).
$$

This telescopes to at most $(9/4)L^2/(L+1)$, already counting both nonprincipal halves. Since $L\ge8$, adding two gives at most $(9/4)L\le3\sqrt{x}$. No improper integral is needed.

The Lean source separates finite prefix bounds from their passage to signed infinite sums. The original Fourier pole abbreviation is definitionally equal to the checked numerator pole, and the row-size theorem specializes the parameter $x$.

The [scalar estimates](DiscretePoleEnvelope.lean) give the pointwise and prefix bounds. The [literal signed sums](LiteralDiscretePoleMoments.lean) include the result in row-size coordinates and its normalization with an explicit positive principal radius.

Run the common-pin checker from the repository root with Lean 4.33.1 on the path.

    python3 -Bu topics/long-cycle-excedances/lean/fourier-odd-moments/check.py /tmp/fourier-odd-moments

The [workflow](../../../../.github/workflows/long-cycle-discrete-pole-moments.yml) prepares the frozen dependency manifest, compiles the three source modules and audits the named declarations and bundled LeanChecker replays.
