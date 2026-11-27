// Coefficient storage policies for the minimum-cycle insertion recurrence.
#pragma once
#include <array>
#include <cstdint>
#include <gmpxx.h>
#include <limits>
#include <stdexcept>

using Z = mpz_class;
constexpr unsigned width = 60;
using Row = std::array<Z, width>;

struct ExactStorage {
    using Stored = Row;

    static void store(Stored &target, Row &row) { target.swap(row); }
    static const Row &read(const Stored &row) { return row; }
    static Z prefix_error(const Row &, const Z &, unsigned) { return 0; }
};

// The positive insertion operator propagates one relative rounding error per
// row. At sizes at most 1001, the true-minus-stored error is at most 2^-36
// times the stored coefficient. Positive ceil Horner bounds its evaluation.
struct PackedStorage {
    static constexpr unsigned precision = 48;
    static constexpr std::uint64_t mask = (std::uint64_t{1} << precision) - 1;
    using Stored = std::array<std::uint64_t, width>;
    static_assert(std::numeric_limits<unsigned long>::digits >= precision,
                  "GMP significands require an unsigned long of at least 48 bits");

    static void store(Stored &target, const Row &row) {
        Z top;
        for (size_t i = 0; i < width; ++i) {
            const Z &x = row[i];
            if (x < 0) throw std::runtime_error("negative insertion coefficient");
            const size_t bits = mpz_sizeinbase(x.get_mpz_t(), 2);
            const size_t shift = bits > precision ? bits - precision : 0;
            if (shift > 65535) throw std::runtime_error("coefficient shift overflow");
            mpz_fdiv_q_2exp(top.get_mpz_t(), x.get_mpz_t(), shift);
            target[i] = (static_cast<std::uint64_t>(shift) << precision) | top.get_ui();
        }
    }

    static Row read(const Stored &stored) {
        Row row;
        for (size_t i = 0; i < width; ++i) {
            row[i] = static_cast<unsigned long>(stored[i] & mask);
            row[i] <<= stored[i] >> precision;
        }
        return row;
    }

    static Z prefix_error(const Row &row, const Z &p, unsigned bits) {
        Z positive = row.back();
        for (int i = width - 2; i >= 0; --i) {
            positive *= p;
            mpz_cdiv_q_2exp(positive.get_mpz_t(), positive.get_mpz_t(), bits);
            positive += row[i];
        }
        mpz_cdiv_q_2exp(positive.get_mpz_t(), positive.get_mpz_t(), 36);
        return positive;
    }
};
