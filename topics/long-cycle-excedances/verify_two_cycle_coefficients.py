"""Check every finite two-cycle coefficient digest via successive insertions."""
import gzip
import hashlib
import json
from math import comb
from pathlib import Path

from flint import fmpz_poly

T = fmpz_poly([0, 1])
ARCHIVE = Path(__file__).with_name("two-cycle-pairs.jsonl.gz")


def eulerian(m):
    values = fmpz_poly([(i + 1)**m for i in range(m)])
    return ((1-T)**(m+1) * values).truncate(m)


def digest(poly):
    data = json.dumps(list(map(int, poly.coeffs())), separators=(",", ":"))
    return hashlib.sha256(data.encode("ascii")).hexdigest()


def verify():
    single = [fmpz_poly([1])] + [eulerian(m) for m in range(1,192)]
    count = 0
    with gzip.open(ARCHIVE, "rt", encoding="ascii") as raw:
        for k in range(3, 96):
            row = single[2*k-2]
            for n in range(2*k-1, min(191, 3*k-2)+1):
                base = (1+(n-1)*T)*row + T*(1-T)*row.derivative()
                term = comb(n,k-1)*T*single[k-1]*single[n-k]
                if n >= 2*k:
                    item = json.loads(next(raw))
                    if (item["n"],item["k"]) != (n,k):
                        raise ArithmeticError("Wrong archive ordering")
                    for key, poly in (("old", row), ("positive_pencil", base+term),
                                      ("negative_pencil", base-term)):
                        if digest(poly) != item[key+"_coefficients_sha256"]:
                            raise ArithmeticError(f"Coefficient mismatch in {key} at {(n,k)}")
                    count += 1
                row = base+term
        if raw.read(1) or count != 3007:
            raise ArithmeticError("Incomplete or oversized finite index")
    print(f"Reconstructed all three coefficient vectors for {count} transitions.")


if __name__ == "__main__":
    verify()
