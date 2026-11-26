"""Print the exact dyadic sign mesh used by the finite Lean proof."""
from math import comb

SCALE = 2**20
GRID = sorted(set(m * 2**p for p in range(30) for m in range(16, 32)))


def inclusion_exclusion(n, k):
    return sum((-1)**j * comb(k, j) * comb(n-j, k-j)**2 for j in range(k+1))


for original in (False, True):
    for n in range(20):
        degree = (2 * n) // 3
        row = [inclusion_exclusion(n, k) * (comb(n, k) if original else 1)
               for k in range(degree + 1)]
        mesh = [0]
        for numerator in GRID:
            scaled_value = sum(c * (-numerator)**k * SCALE**(degree-k)
                               for k, c in enumerate(row))
            if (-1)**len(mesh) * scaled_value > 0:
                mesh.append(numerator)
            if len(mesh) == degree + 1:
                break
        if len(mesh) != degree + 1:
            raise ValueError((original, n, mesh))
        print(f"  | {str(original).lower()}, {n} => {mesh}")
