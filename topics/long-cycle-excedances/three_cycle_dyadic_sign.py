from functools import lru_cache


@lru_cache(maxsize=10000)
def first_omitted_powers(n, width):
    return (width + 1) ** n, (width + 2) ** n


def sign_at_negative_dyadic(coefficients, n, width, numerator, denominator_bits):
    """Certify the sign from a width-term prefix; return zero if inconclusive."""
    if numerator <= 0 or denominator_bits < 0 or width < 1:
        raise ValueError("Expected a strictly negative dyadic and nonempty prefix")
    value = int(coefficients[width - 1])
    for i in range(width - 2, -1, -1):
        value = -numerator * value + (
            int(coefficients[i]) << (denominator_bits * (width - 1 - i))
        )
    if not value:
        return 0
    if width >= n-1:  # Q_n has degree n-2.
        return 1 if value > 0 else -1
    first, following = first_omitted_powers(n, width)
    gap = (first << denominator_bits) - numerator * following
    if gap > 0 and abs(value) * gap > first**2 * numerator**width:
        return 1 if value > 0 else -1
    return 0
