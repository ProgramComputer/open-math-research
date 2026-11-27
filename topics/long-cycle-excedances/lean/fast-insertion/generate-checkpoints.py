"""Generate deterministic exact Lean row checkpoints for cutoff 13, sizes 0–252.

The generated Lean module checks every recurrence step. Generator output is
witness data and is not used as a proof.
"""
from math import comb

k = 13
width = 61
m = k - 1
a = [sum((-1)**v * comb(m+1,v) * (i+1-v)**m for v in range(i+1)) if i<m else 0 for i in range(width)]
p = [[1] + [0]*(width-1)]
for n in range(252):
    lag = p[max(0,n+1-k)]
    p.append([0]+[
        (i+1)*p[n][i+1] + (n-i)*p[n][i] + comb(n,k-1)*sum(a[j]*lag[i-j] for j in range(min(m,i+1)))
        for i in range(width-1)
    ])

def literal(values):
    return '['+', '.join(map(str,values))+']'

def generate(start,end):
    print('''import InsertionTable
namespace OpenMathResearch.LongCycleExcedances.InsertionTable
set_option maxHeartbeats 0
set_option maxRecDepth 10000
''')
    for n in sorted(set(range(start,end+1)) | {max(0,n+1-k) for n in range(start,end)}):
        print(f'def checkpoint{n} : List ℤ := {literal(p[n])}')
    print(f'def checkpointEulerian : List ℤ := {literal(a)}')
    for n in range(start,end):
        print(f'theorem checkpoint_step{n} : next 61 13 checkpointEulerian {n} checkpoint{n} checkpoint{max(0,n+1-k)} = checkpoint{n+1} := by decide')


generate(0,252)
print('''
open Polynomial

/-- Polynomial facts supplied by the literal permutation recurrence. -/
structure CheckpointModel where
  A : ℝ[X]
  E : ℕ → ℝ[X]
  a_agrees : agrees 61 checkpointEulerian A
  zero_row : E 0 = 1
  successor : ∀ n, E (n+1) =
    C (n : ℝ)*X*E n + X*(1-X)*derivative (E n) +
      C (n.choose 12 : ℝ)*(X*A)*E (n+1-13)

theorem agrees_checkpoint0 (model : CheckpointModel) : agrees 61 checkpoint0 (model.E 0) := by
  have hstart : start 61 = checkpoint0 := by decide
  intro i hi
  rw [← hstart, start, entry_rowOf _ _ _ hi, model.zero_row, coeff_one]
  split <;> norm_num
''')
for n in range(252):
    m=max(0,n-12)
    print(f'''theorem agrees_checkpoint{n+1} (model : CheckpointModel) :
    agrees 61 checkpoint{n+1} (model.E {n+1}) := by
  rw [← checkpoint_step{n}]
  exact next_agrees 61 13 {n} _ _ _ model.A _ _ _ model.a_agrees
    (agrees_checkpoint{n} model) (agrees_checkpoint{m} model) (model.successor {n})
''')
print('''
theorem checkpoint_first_pair (model : CheckpointModel) :
    agrees 61 checkpoint251 (model.E 251) ∧ agrees 61 checkpoint252 (model.E 252) :=
  ⟨agrees_checkpoint251 model, agrees_checkpoint252 model⟩

#print axioms checkpoint_step0
#print axioms checkpoint_step251
#print axioms checkpoint_first_pair
end OpenMathResearch.LongCycleExcedances.InsertionTable
''')
