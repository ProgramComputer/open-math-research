# Interlacing at growing outer ranks of ordered partitions

Let $`O_{n,j}(t)`$ sum over all ordered partitions of $`[n]`$, giving each partition weight $`t^b`$ when $`b`$ blocks have size at least $`j`$. Put $`m=\lfloor n/j\rfloor`$. For an integer $`h\to\infty`$ with $`h=o(m)`$, consider the zero-based rank $`h`$ counted from the smallest modulus of the reversed polynomial $`y^m O_{n,j}(1/y)`$, including all complex zeros. Both results below prove simplicity, negativity and strict consecutive order at this rank and its fixed neighboring ranks, uniformly in the remainder $`n-mj`$. [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Tracking issue #1](https://github.com/ProgramComputer/open-math-research/issues/1)

- The theta argument applies when $`j/\sigma\to a\in(0,\infty)`$, where $`\sigma`$ is the standard deviation of the centered coefficient tilt at rank $`h`$. Adjacent moduli in the reversed row have ratio tending to $`\exp(a^2)`$. When $`j/\sqrt m\to\infty`$ this includes $`h/\sqrt m\to1/a`$. [Proof](theta.md) · [Independent review](review-theta.md)
- The moving-pole argument applies when $`m,j\to\infty`$, $`h/\sqrt m\to\infty`$ and $`hj/m\to\infty`$. A contour across several pole pairs controls the full error uniformly and keeps a factor $`1/j`$ in the consecutive comparison. [Proof](moving-poles.md) · [Compact rank start](compact-start.md) · [Independent review](review-moving-poles.md) · [Uniformity audit](review-pole-overlap.md)

At equal degrees the old reversed root of rank $`h`$ lies strictly between the new roots of ranks $`h-1`$ and $`h`$. At a degree increase it lies strictly between new ranks $`h`$ and $`h+1`$. In the original polynomial this is the inequality $`q_{n+1,j,k}<q_{n,j,k}<q_{n+1,j,k+1}`$ in increasing modulus, with one-based rank $`k=m-h`$.

Formal verification is ⬜ None. These asymptotic results cover the stated growing ranks. The earlier theorem covers each fixed number of outer ranks with one eventual cutoff across every threshold. [Fixed outer ranks](../outer-ranks/README.md)

## Exact examples

The fixture program reconstructs all coefficients by choosing the first block and recursing on the remaining labels. It uses numerical roots only to propose rational separators. Exact integer Horner signs give one negative root in each indicated interval, and the number of intervals exhausts both degrees. The examples give strict interlacing for 15 consecutive pairs and verify 719 sign-changing intervals, including five degree increases. These finite examples illustrate the orientation and degree transition. [Checker](check.py) · [Recorded output](check-output.txt)

With Python-FLINT 0.9.0 installed, run from the repository root.

```sh
python -B topics/ordered-large-blocks/growing-outer-ranks/check.py
```
