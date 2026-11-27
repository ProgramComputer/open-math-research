// Exercise the directed operations against exact rational arithmetic.
#include "../integer-signs/relative-dyadics.hpp"
#include <iostream>
#include <random>

using directed::Dyadic;

mpq_class value(Dyadic x) {
    mpq_class q(static_cast<unsigned long>(x.significand));
    if (x.exponent < 0)
        mpq_div_2exp(q.get_mpq_t(), q.get_mpq_t(), -x.exponent);
    else
        mpq_mul_2exp(q.get_mpq_t(), q.get_mpq_t(), x.exponent);
    return q;
}

void contains(Dyadic lower, const mpq_class &exact, Dyadic upper) {
    if (value(lower) > exact || exact > value(upper))
        throw std::runtime_error("dyadic enclosure lost the exact rational value");
}

void check(Dyadic a, Dyadic b) {
    using namespace directed;
    auto x = value(a), y = value(b);
    contains(add(a, b, false), x + y, add(a, b, true));
    contains(multiply(a, b, false), x * y, multiply(a, b, true));
    if (value(positive_difference_lower(a, b)) > (x > y ? mpq_class(x - y) : mpq_class(0)))
        throw std::runtime_error("invalid positive difference lower bound");
    if (compare(a, b) != ((x > y) - (x < y)))
        throw std::runtime_error("incorrect dyadic order");
}

int main() {
    using namespace directed;
    std::mt19937_64 rng(20261126);
    auto random_dyadic = [&] {
        return normalize(rng(), static_cast<int>(rng() % 4000) - 2000, false);
    };
    for (int i = 0; i < 2000; ++i) {
        auto a = random_dyadic(), b = random_dyadic();
        check(a, b);
        check(a, {});
        check(a, a);
        check(a, normalize((U128{1} << 60) - 1, a.exponent - 128, true));
        auto x = (U128{rng()} << 64) | rng();
        const mpz_class exact =
            mpz_class(static_cast<unsigned long>(x >> 64)) * (mpz_class(1) << 64) +
            static_cast<unsigned long>(x);
        mpz_class integer = exact;
        contains(from_integer(integer, 0, false), mpq_class(integer),
                 from_integer(integer, 0, true));
    }
    std::cout
        << "PASS: 8000 comparisons with exact rational arithmetic and 2000 integer conversions\n";
}
