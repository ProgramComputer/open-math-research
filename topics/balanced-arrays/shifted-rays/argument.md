# Shifted-ray interlacing can fail after one abstract row update

Let $d=3$ and cap $r=2$. This example concerns the abstract class of Laurent-polynomial rays with positive coefficients, shift equivariance and oriented proper interlacing along all positive coordinate steps. It does not assert a failure for rays coming from actual balanced arrays.

For $u\in\mathbb Z^3$, write $s=\sum_i u_i$, $h=\lfloor s/3\rfloor$, $c=u-h\mathbf1$ and $j=s-3h\in\{0,1,2\}$. Define

$$
F_u(q)=q^{-h}b(c)(1+(3-j)q),
$$

where $b=10$ on the permutations of $(2,0,0)$, $b=1000$ on the permutations of $(3,-1,-1)$ and $b=1$ elsewhere. This makes the whole family invariant under permutation of the coordinates. Since $c$ and $j$ are invariant under $u\mapsto u+\mathbf1$, we have $F_{u+\mathbf1}=q^{-1}F_u$.

To check the directed interlacing, clear each pair by a common monomial. Scalar weights do not affect the zeros or direction. For $j=0,1$ the old and new polynomials have degree one, and the old zero is strictly to the right of the new zero ($-1/3>-1/2>-1$). For $j=2$, the pair after clearing is $q(1+q),1+3q$. The new zero $-1/3$ is strictly between the old zeros $-1$ and $0$. All steps therefore have the same proper orientation, given by $f'g-fg'>0$ for the ordered old and new pair.

Define the row update by

$$
G_u(q)=\sum_{|S|\le2}F_{u-\mathbf1_S}(q).
$$

At $u=(2,0,0)$ the cap-two sum has contributions $10(1+q)$, $3(1+2q)$ and $3(1+3q)$ grouped by size of $S$. Hence $G_u=16+25q$. At $v=u+e_1=(3,0,0)$, the common factor $q$ clears the Laurent pole in $G_v$. The three grouped contributions are $1+3q$, $12q(1+q)$ and $1002q(1+2q)$, so

$$
qG_v=1+1017q+2016q^2.
$$

Both updated rays are real-rooted. The quadratic has positive discriminant and two negative zeros. At the only nonzero root $-16/25$ of $qG_u$, its value is $109921/625>0$ and its derivative is $-39087/25<0$. Thus $-16/25$ lies strictly to the left of both quadratic zeros. In particular $qG_u$ and $qG_v$ fail to interlace, even weakly. This remains a failure if the monomial of each ray is stripped independently.

An abstract induction using just these adjacent interlacing inequalities and periodic shift equivariance therefore cannot prove that the updated family again has adjacent interlacing. A strengthened invariant could use additional coefficient constraints supplied by the actual counts.

## The same assumptions do give individual one-step real-rootedness

Suppose all nonzero $F_u$ have nonnegative real coefficients after clearing monomials, have only nonpositive real zeros, satisfy $F_{u+\mathbf1}=q^{-1}F_u$, and satisfy the indicated proper orientation along every positive coordinate step joining two nonzero rays. Fix an output offset $u$ with at least one positive-weight nonzero contribution. Assume that each contributing vertex is on a positive-coordinate path from $u-\mathbf1$ to $u$ whose rays are all nonzero. Full nonvanishing on the cube suffices. For $z$ in the open upper half-plane, each adjacent ratio $F_{v+e_i}(z)/F_v(z)$ maps into the closed lower half-plane. Indeed, after canceling common factors, ordinary interlacing gives real simple poles and polynomial part of degree at most one. The sign condition $f'g-fg'\ge0$ makes each pole residue of $g/f$ nonnegative and the linear coefficient nonpositive, proving the mapping assertion. The ratio is nonzero in the upper half-plane and positive on the positive real axis. Thus its argument has a continuous lift in $[-\pi,0]$ with positive-axis limit zero. A constant ratio is positive and has argument identically zero.

For each contributing $u-\mathbf1_S$, choose such a path through that vertex. The product of all adjacent ratios on that path is $z^{-1}$. Their continuously lifted arguments therefore sum to $-\arg z$ modulo $2\pi$, and equality holds without the modulus by continuity and the positive-axis limit. Every summand is nonpositive, so the argument of $F_{u-\mathbf1_S}(z)/F_u(z)$ lies in $[0,\arg z]$. This sector has width less than $\pi$. Therefore any positive linear combination of these ratios is nonzero, even allowing arbitrary nonnegative update weights with at least one positive weight. The corresponding linear combination of the rays has no zero in the upper half-plane, so by real coefficients all its zeros are real after clearing a monomial. This establishes one-step real-rootedness at every output whose relevant paths satisfy the nonvanishing condition. The counterexample above establishes that this conclusion cannot by itself be iterated as an adjacent-ray invariant.

The nonvanishing hypothesis cannot be replaced by requiring proper orientation only where both members of an adjacent pair are nonzero. For $d=2$, put $F_{(a,b)}(q)=q^{-b}f_{a-b}(q)$, with $f_{-1}=1$, $f_1=q$ and all other $f_j=0$. Shift equivariance holds and every coordinate edge has a zero endpoint. With cap one, however, $G_{(0,0)}=1+q^2$. The independent review records this boundary caveat.

## Finite symmetric input failing real-rootedness after two updates

Use three column variables and write $H=1+e_1+e_2$ for the ordinary cap-two row polynomial. Take
$$
A(x)=H(x)+47\sum_{i=1}^3 x_i^2.
$$
Its support is precisely the nonnegative exponent vectors of total degree at most two. Each nonzero shifted diagonal ray of $A$ is a monomial. At offset $u$ its exponent is $-\lfloor \sum_i u_i/3\rfloor$, because only one integer quota can make the total exponent lie in $[0,2]$. Along any positive coordinate step between nonzero rays this exponent is unchanged or drops by one. After common monomial clearing the ordered pair is therefore two positive constants or a positive multiple of $q$ followed by a positive constant, in both cases satisfying weak proper orientation.

After one ordinary update the total degree is at most four. Each nonzero shifted ray then has at most two consecutive possible exponents, so it is still real-rooted after clearing its monomial. Two ordinary updates give $H^2 A$. Its equal diagonal is
$$
1+24q+147q^2.
$$
For quota one, the three contributions from the constant, singleton and pair terms of $A$ are $6$, $3\cdot4$ and $3\cdot2$, respectively. Square terms cannot contribute. For quota two, an $e_2$ term leaves residual margins a permutation of $(1,1,2)$, which have two realizations in the two capped rows. A square term leaves $(0,2,2)$ up to permutation, with one realization. Thus the second coefficient is $3\cdot2+3\cdot47=147$. Higher quotas are excluded by the total degree bound six. The discriminant is $24^2-4\cdot147=-12$. This finite permutation-symmetric family starts in the weak adjacent class, but after two updates even its unshifted ray has nonreal zeros. The initial polynomial $A$ is an auxiliary input, rather than an ordinary array polynomial.
