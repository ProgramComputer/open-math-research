# Strict peaks in Catalan words

The [effective right-edge proof](effective-right-edge.md) gives $C_n(t)>0$ for every size and every real $t\ge-11/16$. It also gives a simple largest real zero for each $n\ge3$, strictly increasing from one size to the next. The analytic cutoffs are $n=9$ for positivity and $n=80$ for the rightmost-root result.

Alexandersson asks for all roots to be real and for complete consecutive interlacing in every size. The existing public proof establishes those claims eventually with an existential cutoff. The right-edge proof closes the finite gap for the largest real zero. An independent agent-assisted review checked the signs of the slit and pole contributions, the phase and derivative estimates, and the transition to the finite check. Direct word enumeration also reproduced the first nine nonempty rows. [Conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjCatalanWordPeaks) · [Prior eventual theorem](https://github.com/1337isnot1337/solved-conjectures/issues/59#issuecomment-7134751818) · [Research issue](https://github.com/ProgramComputer/open-math-research/issues/3)

**⬜ None.** The analytic proof has no Lean or Rocq check. The [finite verifier](code/effective_right_edge.py) reconstructs the [coefficient vectors](results/family-rows.jsonl) through row 80 in two ways and certifies 80 strict consecutive pairs and 9 positive translates. Run from the repository root.

~~~sh
python -m pip install python-flint==0.9.0
python -I -O topics/catalan-word-peaks/code/effective_right_edge.py
~~~
