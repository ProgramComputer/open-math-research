# Every balanced-array polynomial of degree at most fourteen is real-rooted

Let $a_k$ count labeled $n\times d$ binary arrays with $k$ ones in every column and at most $r$ ones in each row. Take $n\ge0$, $d\ge1$ and $1\le r\le d$. Write $P(q)=\sum_k a_kq^k$ and $D=\lfloor nr/d\rfloor$.

**Theorem.** If $D\le14$, then $P$ has only real zeros. For $d\ge2$, every zero is simple and negative. For $d=1$, the polynomial is $(1+q)^n$. Thus any counterexample to the balanced-array conjecture must have degree at least fifteen. The finite part of the proof uses exact arithmetic. This theorem has no checked Lean or Rocq proof. [Conjecture and existing results](README.md)

## Reduction to a finite set

The total row capacity requires $dk\le nr$. For $n>0$ and $k\le D$, list the row labels cyclically and assign a successive block of $k$ labels to each column. Since $k\le n$, a column receives distinct labels. The resulting maximum row load is $\lceil dk/n\rceil\le r$. Thus every coefficient from $a_0$ through $a_D$ is positive. When $n=0$, the polynomial is one. Degrees zero and one give the stated root property immediately.

For $d=1$ the only cap is $r=d=1$, and independent choices in the single column give $(1+q)^n$. For $d\ge2$, both endpoint ranks are covered at every row count by the Jacobi multiplier proof. At $r=d$, each column can be chosen independently, so $a_k=\binom nk^d$. At $r=1$, the column subsets are disjoint, so $a_k=n!/((n-dk)!(k!)^d)$. In either endpoint formula the first Jacobi multiplier yields simple negative roots. The remaining multipliers preserve simplicity because they are invertible and preserve negative real-rootedness. The 24-row theorem supplies the remaining cases with $n\le24$. [Endpoint proof and 24-row theorem](finite-linear-reduction.md)

For any internal index $1\le k<D$, normalized log-concavity gives

$$
\frac{a_k^2}{a_{k-1}a_{k+1}}
\ge \left(\frac{k+1}{k}\frac{n-k+1}{n-k}\right)^d
>\left(\frac{14}{13}\right)^d.
$$

Here $k\le13$ and the second factor inside the parentheses is greater than one. The least dimension $d$ with $14^d\ge4\cdot13^d$ is 19, by integer comparison. Hence $d\ge19$ gives a strict coefficient ratio greater than four and forces simple negative roots. [Normalized log-concavity and the strict separation criterion](orientation-normalization.md#coefficient-separation-for-the-original-polynomial)

After these reductions the only cases to check satisfy

$$
3\le d\le18,\qquad 2\le r<d,\qquad
25\le n\le\left\lfloor\frac{15d-1}{r}\right\rfloor.
$$

The last bound is the integer form of $nr<15d$. There are 1,929 triples. At 1,541 of them the exact binomial ratio in the displayed inequality is greater than four at every internal index. For the other 388 triples, the exact polynomials have $D$ distinct negative zeros, as certified by Sturm's theorem. [Complete finite archive](results/degree_reduction.jsonl)

## Reproduction

The verifier enumerates the finite domain and evaluates every binomial comparison with integers. For each of the 388 remaining triples it recomputes the whole coefficient vector. It classifies the first $d-2$ labeled columns by row loads and counts completions by the overlap of the last two columns. A row at load $r$ must avoid both final columns. A row at load $r-1$ must avoid their intersection. These conditions give the exact binomial choices for placing the two load groups. The script then counts roots on $(-\infty,0)$ using an integer Sturm chain and checks that the derivative has no common factor. [Standalone verifier](verify_degree14.py)

From the repository root, run with Python 3.10 or later. The script uses only the standard library.

~~~sh
python -I -B topics/balanced-arrays/verify_degree14.py topics/balanced-arrays/results/degree_reduction.jsonl
~~~

The optional archive argument also compares every classification and regenerated coefficient to the saved record. With that argument omitted, the verifier runs all the same mathematical checks from scratch. A clean isolated run reconstructed 5,179 coefficients and matched the full archive.
