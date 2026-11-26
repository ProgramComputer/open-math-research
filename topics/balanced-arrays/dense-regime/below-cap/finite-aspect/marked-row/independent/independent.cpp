// Independent directed integer replay for the million-row example.
// Build: c++ -std=c++17 -O3 independent.cpp -o independent
// Run:   ./independent > independent.csv 2> independent-summary.txt
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <utility>

using U = __uint128_t;
using I = __int128_t;
using Word = std::uint64_t;
constexpr int rows = 1000000;
constexpr int columns = 250000;
constexpr int cap = 127000;
constexpr int depth = 5;
constexpr Word z_grid = Word(1) << 44;
constexpr Word prob_grid = Word(1) << 56;
constexpr Word unit = Word(1) << 48;

U mul(U a, U b) {
    U result;
    if (__builtin_mul_overflow(a, b, &result))
        throw std::overflow_error("fixed-point multiplication");
    return result;
}

U add(U a, U b) {
    U result;
    if (__builtin_add_overflow(a, b, &result))
        throw std::overflow_error("fixed-point addition");
    return result;
}

U ceil_div(U a, U b) {
    if (!b) throw std::logic_error("zero denominator");
    return a/b + (a%b != 0);
}

Word word(U value) {
    if (value > std::numeric_limits<Word>::max())
        throw std::overflow_error("not a word");
    return Word(value);
}

struct Interval { Word lo, hi; };

// Relative binomial weights centered at the cap, not the mode.
// A weight interval [wlo,whi] has units 2^-48.
Interval top_atom(Word z) {
    if (!(0 < z && z < z_grid)) throw std::logic_error("invalid tilt");
    U lo = unit, hi = unit;
    U sum_lo = unit, sum_hi = unit;
    const Word v = z_grid-z;
    for (int j = cap; j > 0; --j) {
        const U a = mul(j, v);
        const U b = mul(columns-j+1, z);
        if (hi <= (Word(1)<<16) && a < b) {
            // Successive exact ratios only decrease. Bound the entire
            // remaining sum by the geometric tail after the current atom.
            sum_hi = add(sum_hi, ceil_div(mul(hi, a), b-a));
            break;
        }
        lo = mul(lo, a)/b;
        hi = ceil_div(mul(hi, a), b);
        sum_lo = add(sum_lo, lo);
        sum_hi = add(sum_hi, hi);
    }
    const U numerator = mul(prob_grid, unit);
    return {word(numerator/sum_hi), word(ceil_div(numerator, sum_lo))};
}

Word alpha_times(int n, int k, Word atom, bool upward) {
    const U numerator = mul(mul(columns-cap, n), atom);
    const U denominator = mul(columns, n-k);
    return word(upward ? ceil_div(numerator, denominator)
                       : numerator/denominator);
}

Word lower_loss(int k) {
    Word current = 0;
    // At depth 5 use only e >= 0. There are five recursion evaluations.
    for (int level = depth-1; level >= 0; --level) {
        const int n_level = rows-level;
        const int k_level = k-level;
        const U den = mul(n_level, prob_grid)-mul(n_level-k_level, current);
        const U num = mul(mul(k_level, prob_grid), z_grid);
        const Word test_z = word(num/den);
        current = alpha_times(n_level,k_level,top_atom(test_z).lo,false);
    }
    return current;
}

bool mean_at_least_target(int k, Word tilt, Word atom_hi) {
    const U incoming = mul(tilt, rows);
    const U target = mul(k, z_grid);
    if (incoming < target) return false;
    const U left = mul(mul(columns, incoming-target), prob_grid);
    const U right = mul(mul(mul(tilt, columns-cap), atom_hi),rows);
    return left >= right;
}

std::pair<Word,Word> upper_loss(int k) {
    const Word origin = word(mul(k, z_grid)/rows);
    Word left = origin;
    Word step = z_grid >> 16;
    Word right = origin+step;
    Word atom_hi = top_atom(right).hi;
    while (!mean_at_least_target(k,right,atom_hi)) {
        step *= 2;
        right = origin+step;
        if (right >= z_grid) throw std::logic_error("no upper mean point");
        atom_hi = top_atom(right).hi;
    }
    while (right-left > 1) {
        const Word mid = left+(right-left)/2;
        const Word mid_hi = top_atom(mid).hi;
        if (mean_at_least_target(k,mid,mid_hi)) {
            right = mid;
            atom_hi = mid_hi;
        } else {
            left = mid;
        }
    }
    // Only the verified right endpoint is used as a proof witness.
    if (!mean_at_least_target(k,right,atom_hi))
        throw std::logic_error("unverified upper mean point");
    return {alpha_times(rows,k,atom_hi,true), right};
}


Interval product(Interval a, Interval b) {
    return {word(mul(a.lo,b.lo)/unit),
            word(ceil_div(mul(a.hi,b.hi),unit))};
}

Interval rational_scaled(U numerator, U denominator) {
    const U scaled = mul(unit,numerator);
    return {word(scaled/denominator),word(ceil_div(scaled,denominator))};
}

Interval power(Interval a, int exponent) {
    Interval answer{unit,unit};
    while (exponent > 0) {
        if (exponent % 2) answer = product(answer,a);
        exponent /= 2;
        if (exponent) a = product(a,a);
    }
    return answer;
}

// b_j = B_j^(d/2) in the original unrestricted geometric normalization.
Interval binomial_term_base(int k, int offset) {
    Interval answer{unit,unit};
    for (int j = 1; j <= offset; ++j) {
        const U num = mul(mul(rows-k-j+1,rows-k-j+1),mul(k,k+1));
        const U den = mul(mul(k+j,k+j),mul(rows-k,rows-k+1));
        answer = product(answer,rational_scaled(num,den));
    }
    return answer;
}

I signed_block_margin(int k, Word low, Word high) {
    static_assert(columns % 4 == 0);
    const Word b_one_hi = power(binomial_term_base(k,1),columns/2).hi;
    const Word b_two_geomean_lo = power(
        product(binomial_term_base(k,2), binomial_term_base(rows-k,2)),
        columns/4).lo;
    const Word b_three_hi = power(binomial_term_base(k,3),columns/2).hi;
    const Word b_minus_three_hi = power(binomial_term_base(rows-k,3),columns/2).hi;
    // exp(-L/2) with L = d*log((1-e_low)/(1-e_high)).
    const Interval correction = power(
        rational_scaled(prob_grid-high,prob_grid-low),columns/2);
    const Word b_even_lo = product(
        {b_two_geomean_lo,b_two_geomean_lo},correction).lo;
    return I(unit) - 2*I(b_one_hi) + 2*I(b_even_lo)
        - I(b_three_hi) - I(b_minus_three_hi);
}

long long small_int(I x) {
    if (x < std::numeric_limits<long long>::min() ||
        x > std::numeric_limits<long long>::max())
        throw std::overflow_error("margin does not fit signed word");
    return static_cast<long long>(x);
}

int main() {
    constexpr int first = 504159;
    constexpr int last = 505610;
    constexpr int exploration_limit = 505662;
    I minimum_standard = prob_grid;
    I minimum_signed = unit;
    int standard_count = 0, last_signed = first-1, first_failure = 0;
    std::cout << "k,lo_loss,hi_loss,upper_z,standard_margin,signed_margin\n";
    for (int k = first; k <= exploration_limit; ++k) {
        const Word low = lower_loss(k-2);
        const auto high_and_z = upper_loss(k+2);
        const Word high = high_and_z.first;
        if (!(low <= high && high < prob_grid))
            throw std::logic_error("invalid loss interval");
        const I standard = I(prob_grid)-I(4*columns+1)*high+I(4*columns)*low;
        const I sharpened = signed_block_margin(k,low,high);
        std::cout << k << ',' << low << ',' << high << ',' << high_and_z.second
                  << ',' << small_int(standard) << ',' << small_int(sharpened) << '\n';
        if (k <= last) {
            if (standard <= 0) throw std::logic_error("standard criterion failed");
            ++standard_count;
            minimum_standard = std::min(minimum_standard,standard);
        }
        if (sharpened <= 0) {
            first_failure = k;
            break;
        }
        last_signed = k;
        minimum_signed = std::min(minimum_signed,sharpened);
    }
    if (standard_count != last-first+1)
        throw std::logic_error("incomplete standard replay");
    std::cerr << "Standard verified [" << first << ',' << last << "], count "
              << standard_count << ", minimum margin " << small_int(minimum_standard)
              << "/" << prob_grid << "\n";
    std::cerr << "Signed verified [" << first << ',' << last_signed << "], count "
              << last_signed-first+1 << ", minimum margin " << small_int(minimum_signed)
              << "/" << unit << ", first noncertification " << first_failure << "\n";
}
