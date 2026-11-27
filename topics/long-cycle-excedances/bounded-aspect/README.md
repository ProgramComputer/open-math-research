# Consecutive long-cycle excedance interlacing at bounded aspect

For every $`n\ge1{,}000`$ and $`4\le n/k\le20`$, the nonzero roots of the consecutive fixed-threshold excedance rows at $`n`$ and $`n+1`$ are simple, negative and strictly interlace. The next row supplies both outer nonzero roots. Zero is a simple common root of the unreduced rows. Formal verification is ⬜ None. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles)

The [exterior proof](exterior.md) gives the first $`H=\lfloor7\sqrt n/20\rfloor`$ old root ranks in modulus and their reciprocals at heights below $`10{,}000`$. It determines the sign of the actual next row at those ranks. The [middle proof](grouped-proof.md) gives the signs at the remaining old roots, using joint value and derivative bounds on $`[4,15/2]`$ and the distinct-pole and paired-residue comparisons on $`[15/2,20]`$. The middle boxes overlap at $`k=100`$. At heights from $`10{,}000`$ the [previous bounded-aspect theorem](../paired-residues/README.md) applies. [Independent exterior review](review-exterior.md) · [Independent middle review](review-middle.md)

## Joining the exterior and middle ranks

Write $`P_n=E_{n,k}/t`$. On the first half of the negative axis put $`t=-\exp(-\pi\cot\theta)`$ with $`0<\theta\le\pi/2`$. The first $`H`$ old roots precede the integer sample at $`\theta=(H+1)\pi/n`$, where $`n\sin^2\theta>6/5`$. This angular inequality persists to the midpoint. The signs of $`E_{n,k}`$ at $`\theta=j\pi/n`$ alternate from $`j=H+1`$ through $`j=\lfloor n/2\rfloor`$. There is at least one old root in each intervening gap, giving $`\lfloor n/2\rfloor-1`$ roots of modulus below one when combined with the exterior. Reciprocity gives as many roots beyond modulus one and supplies the root at $`-1`$ for odd $`n`$. This exhausts degree $`n-2`$, so all these roots are distinct and simple.

In the gap from $`j\pi/n`$ to $`(j+1)\pi/n`$ the old root has rank $`j`$ in increasing modulus. The middle comparison gives the actual next sign $`(-1)^j`$ for $`P_{n+1}`$ there. For odd $`n`$ the same comparison at $`\theta=\pi/2`$ gives this sign with $`j=(n-1)/2`$. The exterior comparison gives $`(-1)^h`$ at every old rank $`h\le H`$. Reciprocity of the next row of degree $`n-1`$ carries these signs to the other half in the same rank convention. The constant and leading coefficients of $`P_{n+1}`$ are positive. The signs therefore give a next root in every gap between old roots and one on each outer side. These exhaust its degree and give strict interlacing.

## High-angle estimate at smaller sizes

The separate [high-angle result](high-251.md) proves the middle signs from $`n=251`$ when $`4\le n/k\le20`$, $`n\sin^2\theta\ge6/5`$ and $`k\sin\theta\ge7`$. Its table gives lower entrances on several subranges. This estimate supplies signs on the stated part of the angular interval.

## Reproduction

~~~sh
python3 -I -B check-narrow.py
python3 -I -B verify-1000.py
python3 -I -B high-251.py
python3 -I -B check-exterior.py
python3 -I -B verify-independent-middle.py
~~~

The primary replays use the Python standard library. The final command uses Python-FLINT 0.9.0 and FLINT 3.6.0. [Narrow output](narrow-output.txt) · [Grouped output](replay-1000-exact.txt) · [High-angle output](high-251-output.txt) · [Exterior output](exterior-output.txt) · [Independent middle output](independent-middle-output.txt)
