# An explicit growing-degree interlacing bound for ordered partitions

Let $`d=\lfloor n/j\rfloor`$ be the degree of the old ordered large-block partition polynomial. For every $`d\ge2`$, the polynomials at sizes $`n`$ and $`n+1`$ have simple negative zeros and strictly interlace whenever

$$
j\ge J_d=(64(d+2))^{32768(d+2)^7}.
$$

In increasing modulus the new row supplies the first zero. It also supplies the last zero at a degree increase. The bound works as the old degree grows and gives a finite residual range for any specified maximum degree. Its size makes that range impractical to check exhaustively. [Written proof](closed-form.md) · [Independent review](review-closed-form.md) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

**Formal verification**　⬜ None. A separate exact rational constructor gives smaller sufficient cutoffs for individual degrees. Its proof uses simple roots and strict motion of the limiting hard-rod polynomials. On a nested branch, shrinking parameter cells and still smaller coefficient padding eventually validate the root brackets, including the last root at the left endpoint. The branch then stops. A binary tree with no infinite branch is finite, so the constructor returns a rational certificate for every fixed $`d\ge2`$. [Constructive termination argument and independent checks](review.md) · [Constructor and verifier](certify.py)

| Old degree | Certificate cells | Sufficient threshold |
|---:|---:|---:|
| [2](d2.json) | 9 | 295165919577862307840 |
| [3](d3.json) | 33 | 2305851805306716160000000 |
| [4](d4.json) | 244 | 84605484731424852764031713280 |
| [5](d5.json) | 2,203 | 3568239041377104088491821545553920 |

The degree-five fixture leaves all thresholds below its sufficient cutoff to other arguments. For the already settled low degrees, the repository has much smaller cutoffs and complete residual checks. [Low-degree theorem](../bounded-degree/README.md)

From this directory, use Python 3.10 or later. Replaying stored certificates and generating a new one require only the standard library.

~~~sh
for d in 2 3 4 5; do
    python3 -B certify.py "d${d}.json"
done
python3 -B certify.py /tmp/ordered-degree-five.json --generate 5
~~~
