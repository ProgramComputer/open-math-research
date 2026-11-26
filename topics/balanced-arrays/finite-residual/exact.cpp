#include <algorithm>
#include <array>
#include <cstdint>
#include <gmpxx.h>
#include <iostream>
#include <unordered_map>

using Integer = mpz_class;
using Key = unsigned __int128;
struct KeyHash {
    std::size_t operator()(Key key) const {
        auto low = static_cast<std::uint64_t>(key);
        auto high = static_cast<std::uint64_t>(key >> 64);
        return std::hash<std::uint64_t>{}(low ^ (high * 0x9e3779b97f4a7c15ULL));
    }
};
using Layer = std::unordered_map<Key, Integer, KeyHash>;
std::array<std::array<unsigned long, 63>, 63> choose;

struct Transition {
    Layer &next;
    const Integer &ways;
    std::array<int, 18> sizes{}, suffix{};
    int top, minimum_top;
    bool clipped;

    void add(int bucket, int remaining, Key target, unsigned long multiplicity) {
        if (bucket == top) {
            if (minimum_top <= remaining && remaining <= sizes[bucket]) {
                if (!clipped) {
                    const Key difference = (Key(1) << (6 * bucket)) - (Key(1) << (6 * (bucket - 1)));
                    target -= remaining * difference;
                }
                multiplicity *= choose[sizes[bucket]][remaining];
                mpz_addmul_ui(next[target].get_mpz_t(), ways.get_mpz_t(), multiplicity);
            }
            return;
        }
        if (sizes[bucket] == 0) {
            add(bucket + 1, remaining, target, multiplicity);
            return;
        }
        const Key difference = (Key(1) << (6 * bucket)) - (Key(1) << (6 * (bucket - 1)));
        const int lo = std::max(0, remaining - suffix[bucket + 1]);
        const int hi = std::min(remaining, sizes[bucket]);
        for (int take = lo; take <= hi; ++take) {
            add(bucket + 1, remaining - take, target - take * difference,
                multiplicity * choose[sizes[bucket]][take]);
        }
    }
};

Integer count(int rows, int cap, int dimension, int quota) {
    if (quota == 0) return 1;
    Layer layer;
    layer.emplace(Key(rows) << (6 * cap), 1);
    for (int columns = dimension; columns >= 2; --columns) {
        const int top = std::min(cap, columns);
        Layer next;
        for (const auto &[key, ways] : layer) {
            Transition tr{next, ways, {}, {}, top, 0, top == columns};
            int capacity = 0;
            for (int j = 1; j <= top; ++j) {
                tr.sizes[j] = int((key >> (6 * j)) & 63);
                capacity += j * tr.sizes[j];
            }
            for (int j = top; j >= 1; --j)
                tr.suffix[j] = tr.suffix[j + 1] + tr.sizes[j];
            if (tr.suffix[1] < quota) continue;
            Key target = key;
            if (top == columns) {
                capacity -= tr.sizes[top];
                target -= tr.sizes[top] * ((Key(1) << (6 * top)) - (Key(1) << (6 * (top - 1))));
            }
            if (tr.clipped) {
                // Selecting clipped top rows does not lower the capacity,
                // while choosing any other row lowers it by one.
                tr.minimum_top = std::max(0, columns * quota - capacity);
                if (tr.minimum_top > tr.sizes[top]) continue;
            } else if (capacity < columns * quota) {
                continue;
            }
            tr.add(1, quota, target, 1);
        }
        layer.swap(next);
    }
    Integer result = 0;
    for (const auto &[key, ways] : layer) {
        int available = rows - int(key & 63);
        if (available >= quota)
            mpz_addmul_ui(result.get_mpz_t(), ways.get_mpz_t(), choose[available][quota]);
    }
    return result;
}

int main() {
    for (int i = 0; i < 63; ++i) {
        choose[i][0] = choose[i][i] = 1;
        for (int j = 1; j < i; ++j) choose[i][j] = choose[i-1][j-1] + choose[i-1][j];
    }
    int n, r, d, k;
    while (std::cin >> n >> r >> d >> k) {
        if (n < 1 || n > 62 || r < 1 || r > 15 || d <= r || k < 0 || k > n*r/d)
            return 2;
        std::cout << count(n,r,d,k) << '\n' << std::flush;
    }
}
