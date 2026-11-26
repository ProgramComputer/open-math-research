"""Independently certify every stored coefficient vector by integer evaluations."""
import gzip
import json
from pathlib import Path


def sign_at_negative_power_of_two(coefficients, exponent):
    degree = len(coefficients) - 1
    # At -1/s evaluate the reversed polynomial at -s, then multiply
    # its sign by (-1)^degree to recover the sign of the original.
    terms = coefficients if exponent < 0 else reversed(coefficients)
    point = -(1 << abs(exponent))
    value = 0
    for coefficient in terms:
        value = value * point + coefficient
    if exponent < 0 and degree % 2:
        value = -value
    return (value > 0) - (value < 0)


def main():
    archive = Path(__file__).with_name("records.jsonl.gz")
    rows = roots = 0
    with gzip.open(archive, "rt") as source:
        for line in source:
            row = json.loads(line)
            if "coefficients" not in row:
                continue
            coefficients = row["coefficients"]
            degree = row["n"] * row["r"] // row["d"]
            if len(coefficients) != degree + 1 or min(coefficients) <= 0:
                raise ArithmeticError("Invalid degree or coefficient")
            signs = [1]
            for exponent in range(-64, 52):
                sign = sign_at_negative_power_of_two(coefficients, exponent)
                if sign:
                    signs.append(sign)
            signs.append((-1)**degree)
            changes = sum(a != b for a, b in zip(signs, signs[1:]))
            if changes != degree:
                raise ArithmeticError(f"Missing sign changes at {(row['n'], row['r'], row['d'])}")
            rows += 1
            roots += changes
    if rows != 171:
        raise ArithmeticError(f"Expected 171 stored coefficient vectors, found {rows}")
    print(f"Certified {roots} simple negative zeros in {rows} polynomials by dyadic sign changes.")


if __name__ == "__main__":
    main()
