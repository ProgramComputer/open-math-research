# Strict interlacing through the first transition to four cycles

Let $E_{n,k}$ count permutations of $[n]$ with every cycle of length at least $k$, by the number of excedances. Set $P_n(t)=E_{n,k}(t)/t$. For every $k\ge3$ and $k\le n\le4k-1$, all zeros of $P_n$ and $P_{n+1}$ are simple and negative. They strictly alternate, with both outermost zeros belonging to $P_{n+1}$. At $n=4k-1$ the new row already includes permutations consisting of four cycles of length $k$. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Manuscript, Section 12](paper.pdf) · [LaTeX](paper.tex)

**Formal verification** ⬜ None. The proof combines analytic inequalities with certified polynomial signs. The conjecture for all sizes remains open. Together with earlier results, this theorem restricts any counterexample to $k\ge4$ and $4k\le n<10^{20}$. [Uniform upper cutoff](effective-uniform.md) · [All sizes at minimum length three](fixed-threshold.md)

[Independent agent-assisted review and exact replay scopes](review-complete-band.md)

## Proof

Write $A_j$ for the ordinary Eulerian polynomial. Inserting the largest label in an existing cycle, or on a new cycle of length $k$, gives

$$
P_{n+1}=(1+(n-1)t)P_n+t(1-t)P_n'+L, \qquad
L=\binom{n}{k-1} A_{k-1} E_{n+1-k,k}.
$$

At every root $x$ of $P_n$ we prove $|L(x)|<|x(1-x)P_n'(x)|$. The two polynomials $P_{n+1}$ and $P_{n+1}-2L$ have opposite signs at successive old roots, along with the required signs at zero and negative infinity. Each has exactly one zero in every intervening and outside interval. For $n\le3k-2$ this is the earlier two-cycle theorem. The following three ranges cover the rest. [Two-cycle proof](two-cycle-band.md)

| Old size in $3k-1\le n<4k$ | How the comparison is certified |
|---|---|
| $n\ge2200$ | The expansion uses at most three occupied poles in the old and residual rows. An outer-root estimate meets the middle derivative estimate before the first uncovered root. [Proof](three-cycle-2200.md) · [Independent review](review-three-cycle-2200.md) |
| $192\le n\le2199$ | The middle estimate applies from angular index 20 to its reflected index. Across all 200,800 pairs, certified signs locate 19 old roots on each exterior side. There are 3,815,200 brackets before reflection. [Proof and tail bound](three-cycle-finite-exterior.md) · [Counts and digest files](exterior-records/) |
| $n<192$ | Whole-polynomial signs give dyadic brackets for all 198,819 old roots across 1,595 pairs. Both possible signs of the insertion term pass at every root. [Pair ledger](three-cycle-small-pairs.jsonl.gz) · [Checker](verify_three_cycle_short.py) |

For the small sizes the verifier reconstructs each row by choosing the cycle of label one and verifies the insertion identity. Starting with an Eulerian row, it refines dyadic brackets by certified integer Horner signs. A sign at both ends of a bracket is used together with the full polynomial degree and the signs in neighboring brackets. These counts force the next zeros into the gaps. Independent enumeration by the number of shortest cycles reproduces all 4,785 whole coefficient vectors. [Bracket argument](two-cycle-finite.md) · [Independent whole-vector comparison](verify_three_cycle_short_counts.py)

For intermediate sizes the primary calculation uses the first 48 coefficients. It encloses the omitted terms by a convergent geometric series and compares each entire value interval with that bound. Positive and negative insertion terms are tested at both ends of every exterior bracket. The analytic middle signs join to the last bracket by the same degree count. The [rolling coefficient algorithm](three_cycle_prefix.py) counts two- and three-cycle contributions separately, including the four-cycle contribution in the new row when $n=4k-1$. The two implementations agreed on all 201,485 distinct positive-row prefixes, including all 502 new rows that admit four cycles. [Independent prefix comparison](check-exterior-prefix-agreement.py) · [Replay output](three-cycle-prefix-agreement-output.txt)

A separate integer audit reconstructs the polynomials and checks 3,306 signs at rational dyadic endpoints on 29 stratified pairs. It covers all 19 exterior ranks for each selected pair. [Integer audit and sampling scope](three-cycle-integer-audit.md) · [All 29 sampled pairs](three-cycle-integer-audit-output.txt)

## Reproduction

Run from this directory with Python and python-flint 0.9.0. The intermediate sign computation used Python 3.12.16, python-flint 0.9.0 and FLINT 3.6.0, with 160-bit Arb enclosures. The two commands for the small regime use integer arithmetic and compare with the stored whole-vector and bracket hashes.

~~~sh
python3 -I check-three-cycle-poles.py
python3 -I check-three-cycle-2200.py
python3 -I verify_three_cycle_short.py --workers 2
python3 -I verify_three_cycle_short_counts.py
python3 -I check-exterior-prefix-agreement.py
python3 -I verify-exterior-records.py
python3 -I verify_three_cycle_dyadics.py check-three-cycle-exterior.py
~~~

To reproduce the intermediate bracket digests, use Bash with pipeline error handling. Each successful comparison identifies every dyadic phase bracket and the number of bisections in that shard.

~~~bash
set -euo pipefail
for bounds in '49 240' '241 370' '371 510' '511 733'; do
  read -r first last <<< "$bounds"
  printf -v record 'exterior-records/k%03d-%03d.txt' "$first" "$last"
  python3 -I check-three-cycle-exterior.py --first-k "$first" --last-k "$last" | diff - "$record"
done
~~~
