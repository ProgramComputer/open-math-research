#!/usr/bin/env python3
"""Exact finite checks for the effective angular argument.

The cyclic Fourier tests are modular identities on small inputs. The
rational cutoff checks use the elementary inequalities named in their
comments. The proofs of the analytic estimates are in the companion notes.
"""

import json
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import comb, isqrt


def check(condition, context):
    if not condition:
        raise AssertionError(context)


def check_covariance_identity():
    tilts = [Fraction(1, 5), Fraction(2, 3), Fraction(1),
             Fraction(3, 2), Fraction(5)]
    cases = 0
    for d in range(2, 13):
        for r in range(1, d + 1):
            for w in tilts:
                weights = [comb(d, j) * w**j for j in range(r + 1)]
                total = sum(weights)

                def mean(values):
                    return sum(weight * value for weight, value in
                               zip(weights, values)) / total

                mu = mean(range(r + 1))
                x = mu / d
                variance = mean((j - mu)**2 for j in range(r + 1))
                third = mean((j - mu)**3 for j in range(r + 1))
                size_precision = [
                    Fraction(j * (d - j), d * (d - 1))
                    for j in range(r + 1)
                ]
                precision = mean(size_precision)
                covariance = mean(size_precision[j] * (j - mu)
                                  for j in range(r + 1))
                denominator = d**2 * x * (1 - x) - variance
                check(precision == denominator / (d * (d - 1)),
                      ("precision", d, r, w))
                drift = variance * (1 - 2*x) / (d*x*(1 - x))
                correction = third/denominator - (
                    variance**2 * (1 - 2*x) /
                    (d*x*(1 - x)*denominator)
                )
                check(drift - covariance / precision == correction,
                      ("phase cancellation", d, r, w))
                cases += 1
    return cases


def directly_count_columns(n, d, r, quota):
    """Choose labeled columns independently, subject to the running caps."""
    choices = tuple(combinations(range(n), quota))

    @lru_cache(maxsize=None)
    def count(remaining, row_sizes):
        if remaining == 0:
            return 1
        result = 0
        for rows in choices:
            if all(row_sizes[row] < r for row in rows):
                sizes = list(row_sizes)
                for row in rows:
                    sizes[row] += 1
                result += count(remaining - 1, tuple(sizes))
        return result

    return count(d, (0,) * n)


def cyclic_root(prime, order):
    check(all(prime % j for j in range(2, 1 + isqrt(prime))),
          ("prime", prime))
    for z in range(2, prime):
        if pow(z, order, prime) == 1 and all(
                pow(z, j, prime) != 1 for j in range(1, order)):
            return z
    raise AssertionError(("root of unity", prime, order))


def check_fourier_projection(records):
    # Exponents in each column are at most n < 2d. Hence equality
    # modulo 2d, as detected by these characters, is exact equality.
    tuples = [(2, 13), (2, 17), (3, 13), (3, 31),
              (4, 17), (4, 41), (5, 31), (5, 41)]
    arrays = evaluations = character_points = 0
    for d, prime in tuples:
        order = 2*d
        zeta = cyclic_root(prime, order)
        roots = [pow(zeta, j, prime) for j in range(order)]
        check(roots[d] == prime - 1, ("negative product", d, prime))
        number_of_points = order**(d - 1)
        inverse_count = pow(number_of_points, -1, prime)
        arguments = {}
        for v in range(2, prime):
            residue = (-v**d) % prime
            if residue not in (0, 1, prime - 1):
                arguments.setdefault(residue, v)
        tilts = tuple(arguments.values())[:2]
        check(len(tilts) == 2, ("distinct test arguments", d, prime))
        for r in range(1, d + 1):
            vectors = [
                tuple(directly_count_columns(n, d, r, k)
                      for k in range(n*r//d + 1))
                for n in range(1, 4)
            ]
            arrays += len(vectors)
            for v in tilts:
                argument = -v**d
                check(argument % prime not in (0, 1, prime - 1),
                      ("test argument", d, prime, v))
                sums = [0] * len(vectors)
                for exponents in product(range(order), repeat=d - 1):
                    # The final exponent enforces product -1.
                    last = (d - sum(exponents)) % order
                    z = [v * roots[j] % prime for j in (*exponents, last)]
                    # Elementary symmetric recurrence for the row tilt
                    # before normalization. The n-th power counts n rows.
                    row = [1] + [0] * r
                    for value in z:
                        for j in range(r, 0, -1):
                            row[j] = (row[j] + value * row[j - 1]) % prime
                    row_factor = sum(row) % prime
                    for index in range(len(vectors)):
                        sums[index] += pow(row_factor, index + 1, prime)
                    character_points += 1
                for n, (coefficients, fourier_sum) in enumerate(
                        zip(vectors, sums), start=1):
                    direct = sum(c * argument**k
                                 for k, c in enumerate(coefficients))
                    check(fourier_sum * inverse_count % prime == direct % prime,
                          ("modular Fourier projection", n, d, r, prime, v))
                    records.append(dict(n=n, d=d, r=r, modulus=prime, tilt=v,
                                        coefficients=coefficients, value=direct % prime))
                    evaluations += 1
    return arrays, evaluations, character_points


def check_endpoint_inequalities():
    u = 10**60
    root_u = 10**30
    # For u at and above the endpoint, the quadratic Taylor term gives
    # n^(.2) = exp(u/5) >= u^2/50. Here sqrt(401) < 21.
    principal_norm = (Fraction(42, root_u) + Fraction(4000*401, u)
                      + Fraction(400*50, u**2))
    # For u at and above the endpoint, exp(.97u) and exp(.99u)
    # exceed u^2/3 by their quadratic Taylor terms.
    small_ball_loss = Fraction(81, u**2) + Fraction(1200, u)
    # Remote-chart volume: log u <= sqrt(u).
    remote_volume = Fraction(110*(2 + root_u), u)
    # For odd j>=3, j/(j^2-1)<=3/8 and pi>3. The two-sided
    # tail uses exp(-72L/5) <= 1/(1+72L/5) and exp(2)<8.
    L = 2500
    tail_ratio = 1 / (1 + Fraction(72*L, 5))
    # The residual phase error after division by n^(-1/10)
    # uses exp(-c u) <= 1/(c u) for the remaining positive c.
    phase_margin = (
        Fraction(4*200, 3*u) + Fraction(10**16*100, 37*u)
        + Fraction(10**17*100, 36*u) + Fraction(2*10**10*100, 37*u)
        + Fraction(400, 89*u)
    )
    cases = [
        (principal_norm < Fraction(1, 10**4), "principal Gaussian norm"),
        (Fraction(u, 401*10**8) > 100, "smallest chart Gaussian tail"),
        (small_ball_loss < Fraction(5, 10**9), "off-ball prefactor budget"),
        (remote_volume < Fraction(1, 10**27), "remote-chart volume"),
        (20*Fraction(3, 8) <= Fraction(3*L, 20), "near-chart radial budget"),
        (64*tail_ratio/(1-tail_ratio) < Fraction(1, 100), "odd-label sum"),
        (phase_margin < 1, "phase error"),
        (2*Fraction(1, 10) + 3*Fraction(1, 100) < Fraction(1, 4),
         "total angular remainder"),
    ]
    for valid, context in cases:
        check(valid, context)
    return len(cases)


def check_lower_cutoff():
    f = Fraction
    u = 10**6
    spent = (f(11,10)*f(7,24) + f(55,100)*f(28,100))/f(999,1000)
    # log(4/(4/3))=log(3)>1, and e^(1/100) < 1.02.
    inner_norm = f(42,100)*f(11,1000)+f(54,10)*f(112,u)+f(1,10**6)
    checks = [
        spent < f(1,2),
        f(168,100)*f(9,8)**3 < f(24,10),
        f(24,10)*f(401,1000)**2 < f(2,5),
        f(1,100) + f(408*222,u) < 1,
        f(112,u) < f(11,1000)**2,
        inner_norm < f(6,1000),
        f(6,1000)**2*5 < f(14,1000)**2,
        f(15,1000)*f(1001,1000)+f(1,1000) < f(2,100),
        f(2*2+3,100) < f(19,10),
    ]
    for i, valid in enumerate(checks):
        check(valid, ("large-radius cutoff", i))
    return len(checks)


def polynomial_at_rational(coefficients, argument):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*argument+coefficient
    return value


def check_square_examples():
    examples = []
    for d in (5, 6):
        n, r, k = 4*d*d, d-1, d*d
        # Inclusion-exclusion over all-one rows leaves unrestricted columns.
        counts = [
            sum((-1)**i * comb(n,i) * comb(n-i,j-i)**d for i in range(j+1))
            for j in range(n*r//d+1)
        ]
        t_squared = Fraction(counts[k-1], counts[k+1])
        even = polynomial_at_rational(counts[::2], t_squared)
        odd = polynomial_at_rational(counts[1::2], t_squared)
        # Both parts are strictly positive, so squaring preserves their order.
        delta = even**2-t_squared*odd**2
        sign = (-1)**k * ((delta>0)-(delta<0))
        check(sign == -1, ("wrong geometric sign", n,d,r,k))
        examples.append(dict(n=n,d=d,r=r,k=k,coefficients=counts,signed_value_sign=sign))
    return examples


def main():
    covariance_cases = check_covariance_identity()
    records = []
    arrays, evaluations, points = check_fourier_projection(records)
    squares = check_square_examples()
    replay = json.loads(json.dumps(dict(cyclic_projections=records, quadratic_signs=squares)))
    ledger = Path(__file__).with_name("angular-replay.json")
    check(replay == json.loads(ledger.read_text()), "stored exact examples")
    cutoff_cases = check_endpoint_inequalities()+check_lower_cutoff()
    print(f"Exact rational covariance identities: {covariance_cases}")
    print(f"Direct labeled-array coefficient vectors (with field choices): {arrays}")
    print(f"Modular Fourier projection comparisons: {evaluations}")
    print(f"Cyclic torus points summed (shared across heights): {points}")
    print(f"Exact geometric sign reversals checked: {len(squares)}")
    print(f"Exact rational endpoint inequalities: {cutoff_cases}")


if __name__ == "__main__":
    main()
