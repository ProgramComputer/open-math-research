"""Check the derivative and the interval bound with integer polynomials."""

from fractions import Fraction


def add(left, right):
    result = [0] * max(len(left), len(right))
    for coefficients in (left, right):
        for degree, coefficient in enumerate(coefficients):
            result[degree] += coefficient
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def scale(polynomial, factor):
    return [factor * coefficient for coefficient in polynomial]


def multiply(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for left_degree, left_coefficient in enumerate(left):
        for right_degree, right_coefficient in enumerate(right):
            result[left_degree + right_degree] += (
                left_coefficient * right_coefficient
            )
    return result


def derivative(polynomial):
    return [degree * polynomial[degree] for degree in range(1, len(polynomial))]


def evaluate(polynomial, value):
    result = 0
    for coefficient in reversed(polynomial):
        result = result * value + coefficient
    return result


def main():
    b = [126, 84, 36, 9, 1]
    a = [35, 21, 7, 1]
    b_prime = derivative(b)
    v_b_prime = [0] + b_prime
    q = add(
        multiply(derivative(v_b_prime), b),
        scale(multiply(v_b_prime, b_prime), -1),
    )
    assert q == [10584, 18144, 13230, 5040, 1080, 144, 9]

    b_squared = multiply(b, b)
    aq = multiply(a, q)
    a_prime_q = multiply(derivative(a), q)
    a_q_prime = multiply(a, derivative(q))
    numerator = multiply(b_squared, b_squared)
    for order in range(8):
        denominator_term = add(
            scale(a_prime_q, order + 4), scale(a_q_prime, 2 * order)
        )
        numerator = multiply(
            b_squared,
            add(
                multiply(aq, derivative(numerator)),
                scale(multiply(denominator_term, numerator), -1),
            ),
        )

    factor = Fraction(5, 18) ** 4
    at_zero = factor * Fraction(numerator[0], a[0] ** 12 * q[0] ** 16)
    assert at_zero == Fraction(-8846065132029, 58824500000)

    upper_v = Fraction(1, 100)
    polynomial_majorant = [numerator[0]] + [
        max(0, coefficient) for coefficient in numerator[1:]
    ]
    upper_numerator = evaluate(polynomial_majorant, upper_v)
    upper_denominator = evaluate(a, upper_v) ** 12 * evaluate(q, upper_v) ** 16
    assert factor * upper_numerator < -60 * upper_denominator

    upper_x = upper_v * evaluate(b_prime, upper_v) / evaluate(b, upper_v)
    h = Fraction(1, 1500)
    assert 9 * h < upper_x

    print(f"g^(8)(0) = {at_zero}")
    print(f"x(1/100) = {upper_x} > 9h for h = {h}")
    print("g^(8)(x) < -60 on 0 <= x <= x(1/100)")


if __name__ == "__main__":
    main()
