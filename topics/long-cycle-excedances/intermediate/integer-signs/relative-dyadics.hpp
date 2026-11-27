// Upper and lower dyadic enclosures for the condition-number check.
// Each nonzero value is m * 2^e with a 60-bit normalized significand.
#pragma once
#include "row-storage.hpp"
#include <array>
#include <cstdint>
#include <gmpxx.h>
#include <stdexcept>
#include <utility>
#if defined(__SIZEOF_INT128__)
namespace directed {
using U128 = unsigned __int128;
constexpr unsigned precision = 60;
static_assert(std::numeric_limits<unsigned long>::digits >= precision + 1,
              "GMP conversion needs room for an upward-rounded significand");
struct Dyadic {
    std::uint64_t significand = 0;
    int exponent = 0;
};
inline int bit_length(U128 x) {
    auto hi = static_cast<std::uint64_t>(x >> 64);
    if (hi != 0)
        return 128 - __builtin_clzll(hi);
    auto lo = static_cast<std::uint64_t>(x);
    return lo == 0 ? 0 : 64 - __builtin_clzll(lo);
}
inline U128 rounded_right_shift(U128 x, unsigned shift, bool upper) {
    if (shift >= 128)
        return upper && x != 0;
    if (!shift)
        return x;
    return (x >> shift) + (upper && (x & ((U128(1) << shift) - 1)) != 0);
}
inline Dyadic normalize(U128 x, int e, bool upper) {
    if (!x)
        return {};
    int adjustment = bit_length(x) - static_cast<int>(precision);
    U128 m = adjustment >= 0 ? rounded_right_shift(x, adjustment, upper) : x << -adjustment;
    if (m == (U128(1) << precision)) {
        m >>= 1;
        ++adjustment;
    }
    return {static_cast<std::uint64_t>(m), e + adjustment};
}
inline Dyadic from_integer(const mpz_class &x, int e, bool upper) {
    if (x < 0)
        throw std::runtime_error("negative dyadic input");
    if (x == 0)
        return {};
    unsigned bits = mpz_sizeinbase(x.get_mpz_t(), 2);
    unsigned shift = bits > precision ? bits - precision : 0;
    mpz_class top;
    mpz_fdiv_q_2exp(top.get_mpz_t(), x.get_mpz_t(), shift);
    auto m = top.get_ui() + (upper && mpz_divisible_2exp_p(x.get_mpz_t(), shift) == 0);
    return normalize(m, e + static_cast<int>(shift), upper);
}
inline int compare(Dyadic a, Dyadic b) {
    if (!a.significand || !b.significand)
        return int(a.significand != 0) - int(b.significand != 0);
    if (a.exponent != b.exponent)
        return a.exponent > b.exponent ? 1 : -1;
    return int(a.significand > b.significand) - int(a.significand < b.significand);
}
inline Dyadic add(Dyadic a, Dyadic b, bool up) {
    if (!a.significand)
        return b;
    if (!b.significand)
        return a;
    if (a.exponent < b.exponent)
        std::swap(a, b);
    return normalize(U128(a.significand) +
                         rounded_right_shift(b.significand, a.exponent - b.exponent, up),
                     a.exponent, up);
}
inline Dyadic multiply(Dyadic a, Dyadic b, bool up) {
    return normalize(U128(a.significand) * b.significand, a.exponent + b.exponent, up);
}
// A positive result bounds a-b from below. Zero also represents an inconclusive subtraction.
inline Dyadic positive_difference_lower(Dyadic a, Dyadic b) {
    if (compare(a, b) <= 0)
        return {};
    if (!b.significand)
        return a;
    return normalize(U128(a.significand) -
                         rounded_right_shift(b.significand, a.exponent - b.exponent, true),
                     a.exponent, false);
}
inline Dyadic power(Dyadic x, unsigned n, bool up) {
    Dyadic result = normalize(1, 0, up);
    while (n) {
        if (n & 1)
            result = multiply(result, x, up);
        n >>= 1;
        if (n)
            x = multiply(x, x, up);
    }
    return result;
}
struct FixedRow {
    std::array<Dyadic, width> lo, hi;
};
inline FixedRow fixed_row(const Row &row) {
    const Dyadic relative = normalize((U128(1) << 36) + 1, -36, true);
    FixedRow out;
    for (unsigned i = 0; i < width; ++i) {
        out.lo[i] = from_integer(row[i], 0, false);
        out.hi[i] = multiply(from_integer(row[i], 0, true), relative, true);
    }
    return out;
}
struct FixedPowers {
    Dyadic ulo, uhi, vhi;
};
inline FixedPowers fixed_powers(unsigned n) {
    Dyadic u = normalize(width + 1, 0, false), v = normalize(width + 2, 0, false);
    return {power(u, n, false), power(u, n, true), power(v, n, true)};
}
inline bool relative_margin_32(const FixedRow &r, const FixedPowers &g, const Z &p, unsigned bits,
                               int sign) {
    const Dyadic ylo = from_integer(p, -int(bits), false), yhi = from_integer(p, -int(bits), true);
    Dyadic pos, neg, absolute;
    for (int i = width - 1; i >= 0; --i) {
        absolute = add(multiply(absolute, yhi, true), r.hi[i], true);
        pos = multiply(pos, ylo, false);
        neg = multiply(neg, yhi, true);
        if ((i % 2 == 0) == (sign > 0))
            pos = add(pos, r.lo[i], false);
        else
            neg = add(neg, r.hi[i], true);
    }
    // The two parity classes have opposite signs. pos is a lower bound; neg and
    // absolute are upper bounds. A positive comparison therefore survives every rounding.
    // Remove 2^-32 times the whole positive prefix before testing the tail.
    Dyadic positive_allowance = {absolute.significand, absolute.exponent - 32};
    Dyadic delta =
        positive_difference_lower(positive_difference_lower(pos, neg), positive_allowance);
    if (!delta.significand)
        return false;
    const Dyadic tail = multiply(multiply(g.uhi, g.uhi, true), power(yhi, width, true), true);
    const Dyadic scaled_tail = add(tail, {tail.significand, tail.exponent - 32}, true);
    const Dyadic left = multiply(delta, g.ulo, false);
    const Dyadic right = add(scaled_tail, multiply(delta, multiply(yhi, g.vhi, true), true), true);
    return compare(left, right) > 0;
}
} // namespace directed
#endif
