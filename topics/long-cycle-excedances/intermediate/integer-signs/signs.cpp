// Integer replay of dyadic signs for the reduced minimum-cycle excedance rows.
#include <algorithm>
#include "row-storage.hpp"
#include <charconv>
#include <iostream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <tuple>
#include <vector>

Row single_cycle(unsigned k) {
    Row p{};
    p[0] = 1;
    for (unsigned m = 1; m < k; ++m) {
        for (unsigned i = std::min(m, width - 1); i > 0; --i) {
            p[i] = (i + 1) * p[i] + (m - i) * p[i - 1];
        }
    }
    return p;
}

template <typename Storage>
struct Rows {
    unsigned k, n;
    Row cycle;
    std::vector<typename Storage::Stored> ring;
    Rows(unsigned cutoff) : k(cutoff), n(k), cycle(single_cycle(k)), ring(k) {
        Row seed = cycle;
        Storage::store(ring[0], seed);
    }
    decltype(auto) at(unsigned m) const { return Storage::read(ring[m % k]); }
    void advance(unsigned target) {
        while (n < target) {
            const Row &p = at(n);
            const unsigned m = n + 1 - k;
            const Row &lag = at(m);
            Row next{};
            Z choices, acc;
            mpz_bin_uiui(choices.get_mpz_t(), n, k - 1);
            next[0] = p[0];
            for (unsigned i = 1; i < width; ++i) {
                mpz_mul_ui(next[i].get_mpz_t(), p[i].get_mpz_t(), i + 1);
                if (n > i)
                    mpz_addmul_ui(next[i].get_mpz_t(), p[i - 1].get_mpz_t(), n - i);
                if (m < k)
                    continue;
                acc = 0;
                unsigned from = i > m - 1 ? i - (m - 1) : 0;
                unsigned to = std::min(i - 1, k - 2);
                for (unsigned a = from; a <= to; ++a)
                    mpz_addmul(acc.get_mpz_t(), cycle[a].get_mpz_t(), lag[i - 1 - a].get_mpz_t());
                mpz_addmul(next[i].get_mpz_t(), choices.get_mpz_t(), acc.get_mpz_t());
            }
            ++n;
            Storage::store(ring[n % k], next);
        }
    }
};

struct Powers {
    Z u, v;
};
struct Stats {
    unsigned long checks = 0, sharp_tail = 0, exact_prefix = 0;
};
Z pow_ui(const Z &a, unsigned n) {
    Z out;
    mpz_pow_ui(out.get_mpz_t(), a.get_mpz_t(), n);
    return out;
}
Powers powers(unsigned n) { return {pow_ui(Z(width + 1), n), pow_ui(Z(width + 2), n)}; }

template <typename Storage>
void check(const Row &row, const Powers &g, const Z &p, unsigned bits, int sign, Stats &stats) {
    Z D = Z(1) << bits;
    if (p <= 0 || 2 * p >= D)
        throw std::runtime_error("endpoint outside (0,1/2)");
    Z rounded = row.back();
    for (int i = width - 2; i >= 0; --i) {
        rounded *= p;
        mpz_fdiv_q_2exp(rounded.get_mpz_t(), rounded.get_mpz_t(), bits);
        rounded = row[i] - rounded;
    }
    // Repeated floor errors, with sign reversal, have absolute sum < 2.
    const Z uncertainty = Storage::prefix_error(row, p, bits);
    const Z lower = sign * rounded - 2 - uncertainty;
    const unsigned shift = bits - static_cast<unsigned>(mpz_sizeinbase(p.get_mpz_t(), 2));
    ++stats.checks;
    if (lower > 0 && (g.u << shift) >= 2 * g.v && (lower << (shift * width)) > 2 * g.u)
        return;
    ++stats.sharp_tail;
    const Z denominator = (g.u << bits) - p * g.v;
    if (denominator <= 0)
        throw std::runtime_error("geometric bound diverges");
    const Z tail_numerator = g.u * g.u * pow_ui(p, width);
    if (lower > 0 && ((lower * denominator) << (bits * (width - 1))) > tail_numerator)
        return;
    ++stats.exact_prefix;
    Z homogeneous = row.back();
    for (int i = width - 2; i >= 0; --i)
        homogeneous = (row[i] << (bits * (width - 1 - i))) - p * homogeneous;
    const Z signed_prefix = sign * homogeneous - (uncertainty << (bits * (width - 1)));
    if (signed_prefix * denominator <= tail_numerator)
        throw std::runtime_error("uncertified sign");
}

struct Point {
    Z p;
    unsigned bits;
};
struct Key {
    unsigned n, k, r;
    Point a, b;
};

bool canonical_decimal(std::string_view value) {
    return !value.empty() && (value.size() == 1 || value.front() != '0') &&
           std::all_of(value.begin(), value.end(), [](char c) { return c >= '0' && c <= '9'; });
}

unsigned small_unsigned(std::string_view value) {
    unsigned result;
    const auto parsed = std::from_chars(value.data(), value.data() + value.size(), result);
    if (parsed.ec != std::errc{} || parsed.ptr != value.data() + value.size())
        throw std::runtime_error("small integer out of range");
    return result;
}

Key parse(std::string_view line) {
    if (line.size() > 400)
        throw std::runtime_error("record is too long");
    std::array<std::string_view, 7> fields;
    for (size_t i = 0; i < fields.size(); ++i) {
        const auto comma = line.find(',');
        if ((comma == std::string_view::npos) != (i + 1 == fields.size()))
            throw std::runtime_error("wrong field count");
        fields[i] = line.substr(0, comma);
        if (!canonical_decimal(fields[i]))
            throw std::runtime_error("noncanonical decimal field");
        if (comma != std::string_view::npos)
            line.remove_prefix(comma + 1);
    }
    const auto a_bits = small_unsigned(fields[4]);
    const auto b_bits = small_unsigned(fields[6]);
    if (a_bits == 0 || a_bits > 512 || b_bits == 0 || b_bits > 512)
        throw std::runtime_error("dyadic exponent out of range");
    Point a{Z(std::string(fields[3]), 10), a_bits};
    Point b{Z(std::string(fields[5]), 10), b_bits};
    if (mpz_even_p(a.p.get_mpz_t()) || mpz_even_p(b.p.get_mpz_t()))
        throw std::runtime_error("noncanonical dyadic");
    return {small_unsigned(fields[0]), small_unsigned(fields[1]), small_unsigned(fields[2]), a, b};
}

void print_first_pair() {
    Rows<ExactStorage> rows(13);
    rows.advance(252);
    for (unsigned n : {251, 252}) {
        std::cout << '[';
        const Row &row = rows.at(n);
        for (unsigned i = 0; i < width; ++i)
            std::cout << (i == 0 ? "" : ",") << row[i];
        std::cout << "]\n";
    }
}

template <typename Storage>
int replay() {
    try {
        std::string line;
        Key prev{};
        Stats stats;
        unsigned pairs = 0, gaps = 0;
        std::vector<Powers> bounds(1002);
        for (unsigned n = 251; n <= 1001; n++)
            bounds[n] = powers(n);
        Rows<Storage> rows(7);
        Row old, upper;
        while (std::getline(std::cin, line)) {
            auto v = parse(line);
            if (v.k < 7 || v.k > 250 || v.n < 251 || v.n > 1000 || v.n < 4 * v.k ||
                v.n >= 20 * v.k || v.r == 0)
                throw std::runtime_error("invalid parameter range");
            if (std::tie(v.k, v.n, v.r) <= std::tie(prev.k, prev.n, prev.r))
                throw std::runtime_error("order");
            if ((v.a.p << v.b.bits) >= (v.b.p << v.a.bits))
                throw std::runtime_error("bracket order");
            if (v.k != prev.k || v.n != prev.n)
                ++pairs;
            else if (v.r != prev.r + 1 || (prev.b.p << v.a.bits) >= (v.a.p << prev.b.bits))
                throw std::runtime_error("neighboring brackets");
            if (rows.k != v.k)
                rows = Rows<Storage>(v.k);
            if (v.k != prev.k || v.n != prev.n) {
                rows.advance(v.n + 1);
                old = rows.at(v.n);
                upper = rows.at(v.n + 1);
            }
            int direction = v.r % 2 == 1 ? 1 : -1;
            try {
                for (auto p : {&v.a, &v.b}) {
                    check<Storage>(old, bounds[v.n], p->p, p->bits,
                          p == &v.a ? direction : -direction, stats);
                    check<Storage>(upper, bounds[v.n + 1], p->p, p->bits, -direction, stats);
                }
            } catch (const std::exception &e) {
                std::cerr << v.n << ' ' << v.k << ' ' << v.r << ' ' << e.what() << '\n';
                return 1;
            }
            ++gaps;
            prev = v;
        }
        std::cout << "pairs=" << pairs << " gaps=" << gaps << " exact_signs=" << stats.checks
                  << " sharp_tail=" << stats.sharp_tail << " exact_prefix=" << stats.exact_prefix
                  << '\n';
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 1) return replay<ExactStorage>();
    if (argc == 2 && std::string_view(argv[1]) == "--packed") return replay<PackedStorage>();
    if (argc == 2 && std::string_view(argv[1]) == "--first-pair-prefixes") {
        print_first_pair();
        return 0;
    }
    std::cerr << "usage: signs [--packed | --first-pair-prefixes]\n";
    return 2;
}
