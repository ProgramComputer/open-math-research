# Independent review of the high exterior theorem

November 26, 2026. Agent-assisted review of proof SHA-256
`851a7c4705d9e55938a163a28816ca5cd72496ee15660745e7761b395a4c2803` and
checker SHA-256
`99d93a575857d5b7a9a42e03dd8e94f0f819c19659f1ffea9d186f4899cfa1d7`.
The proof establishes the stated exterior comparison at every old size
$1001\le n\le9999$, $k\ge3$, $n/k\ge20$. The theorem statement now includes $k\ge3$ explicitly,
as required by the run encoding and common zero. I found no mathematical correction in that
range. The comparison is with the actual next row. The middle root
argument and formal verification are separate.

## Run model and adjacent coefficient control

I checked the coefficient floor for both sizes, including $N=10000$ when
the old size is $9999$. For a uniform permutation of $p$ colors,
the derangement probability is between $1/3$ and $1/2$ for $p\ge2$.
For each proper cycle of size $j\ge2$, conditional on derangement the
expected count is $d(p-j,2)/(j d(p,2))\le3/(2j)$. Residual size
one gives count zero and the full cycle cannot fail. The binomial
exponent for a proper cycle is at least
$j v(.975-.00875v)^2/(2\cdot .382)$, where
$v=\sqrt N\in[\sqrt{1001},100]$. The increasing and then
decreasing cubic has its minimum at a boundary. The independent
replay checks the resulting $1.3 j$ bound, the geometric union
bound, and the subtraction of the word-boundary error. This gives
the required $.30$ floor on every central coefficient. At $p=1$
the one descending run gives the unique admissible cycle.

Appending a label gives the binomial kernel stated in the proof. The
expected marked cycle count and its chance of receiving the new
color cancel to $1/p$, and the full color cycle cannot be the
failing cycle. The proof may drop the acceptance requirement for
the residual cycles, since it needs an upper bound. The small
threshold case uses the half-mean Chernoff bound. In the other
case $p\le\sqrt n/2$ implies $k-1\ge31$ and $n/k\ge20$ gives
the complementary mode parameter at least $19/20$. The unimodal
lattice estimate is valid by omitting a largest sampled value and
charging every other sampled value to the interval toward it.
The beta integral gives $1/(n+1)$. Both row boundary errors can use
$\lfloor n/2\rfloor$ in the exponent, and their sum multiplied by
$p$ is bounded by $4p^2 e^{-\lfloor n/2\rfloor/p}
\le n e^{-(n-1)/\sqrt n}$. These yield the claimed absolute
$.1$ comparison.

## Root locations, sign and consecutive order

After balancing adjacent monomials the pure outward ratios decrease
on either side. The immediate bases are $1-1/h^2$ and
$1-1/(h+1)^2$. The omitted left tail at $h=1$ incurs no cost.
All ratio comparisons are against one of the two central
coefficients, so the central floor and the global upper bound
$\alpha\le1$ suffice. At the disk $|z+1|<.05$ Rouché's theorem gives one
root, including multiplicity. On the circles $|z|=1/2$ and $|z|=3$,
multiply by $z^{h-1}$ to get a polynomial proportional to
$E_{n,k}(uz)/z$. The comparison polynomial $z^{h-1}(1+z)$ has
exactly $h-1$ and $h$ roots in the two disks, respectively. The disk
near $-1$ lies strictly within the resulting annulus. The one annulus
root is real by conjugation, negative by its bracket, and simple.
The same proof holds for the new row at ranks $h\le H$ because its
central coefficient floor holds through size $10{,}000$.

At an old root, subtracting $h E_{n,k}$ leaves the value of the
actual new row. After normalization by $\alpha_{n,h}h^n t^h$,
the old central weights are $0,1$, giving $z<-.95$. The old tails
carry weights $\ell$ and $\ell+1$. The perturbation is written
directly using $p(\alpha_{n+1,p}-\alpha_{n,p})$ on the same pure
monomial scales. This also handles a new top degree absent in the
old row, taking its old coefficient as zero. The two central
perturbations have absolute total at most $(1+1.05)/3$.
The local tails use the absolute $.1$ estimate, and the farther
right ones use $\ell\ge4$ and $p<5\ell$, deduced directly from
$p>\sqrt n/2$ and $h+1\le .382\sqrt n$. The exact scalar
sum stays strictly below $.95$. The normalized next row is thus
negative, and undoing the factor $t^h$ and dividing by $t$
gives sign $(-1)^h$ for $P_{n+1}$.

The old root is strictly inside the new annulus. I checked the
coefficient ratio factors separately for $h=1$ and all $h\ge2$.
The sign of the new reduced row at the inner annulus endpoint is
$(-1)^{h-1}$. The strictly opposite sign at the old root and
uniqueness of the new annulus root give its required position.
All higher new ranks are outside the annulus. These counts refer
to all zeros in modulus, including nonreal ones and counting
multiplicity, so they do not assume the remaining real-rootedness.

## Earlier phase sample

The old rank $H$ modulus is at most
$(7/2)(H/(H+1))^n$ from the disk and the adjacent coefficient
ratio. Jensen's inequality for the integral of $1/(H+x)$ gives

$$
\log(1+1/H)-\frac1{H+5/6}
\ge\frac1{H+1/2}-\frac1{H+5/6}
\mathrel{>}\frac1{3(H+1)^2}.
$$

The rational exponential replay certifies
$e^{1/(3(.382)^2)}>7/2$. Together with $\theta\cot\theta<1$
this puts the last exterior root strictly before the earlier
sample $(H+5/6)\pi/n$, and hence before $(H+1)\pi/n$.
The independent checker verifies the floor and separate sine
and cosine endpoint inequalities at every integer height
$1001$ through $9999$. The proved range starts at the next old size after the separate
finite certificate. The $9999$ pair uses the established new-row
coefficient estimates at size $10000$. Reflecting
the real annuli under reciprocal symmetry gives the other end.

The original checker replayed with identical stdout. The
[independent scalar replay](check-independent.py) uses Machin's formula,
a unit-interval exponential lower bound raised to an exact
power, and an integer loop over all 8,999 phase endpoints.
[Recorded output](independent-output.txt)
