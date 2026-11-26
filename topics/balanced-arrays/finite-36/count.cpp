// Exact labeled column DP. Process each pre-column row-load bucket from high to low.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <unordered_map>

#include <gmpxx.h>

using Key = uint64_t;
using Layer = std::unordered_map<Key, mpz_class>;
constexpr int bits = 6;
constexpr Key mask = 63;
constexpr int picked_shift = 48;
constexpr Key loads_mask = (Key(1) << picked_shift) - 1;

unsigned long choose[64][64];

int population(Key key, int load) {
    return (key >> (bits * load)) & mask;
}

bool viable(Key loads, int cap, int remaining, int k) {
    int positions = 0;
    for (int load = 0; load < cap; ++load) {
        positions += population(loads, load) * std::min(cap-load, remaining);
    }
    return positions >= remaining*k;
}

mpz_class count(int n, int d, int r, int k, bool report) {
    if (k == 0) return 1;
    Layer layer{{Key(n), mpz_class(1)}};
    for (int column = 0; column < d; ++column) {
        int top = std::min(column, r-1);
        for (int load = top; load >= 0; --load) {
            Layer next;
            next.reserve(layer.size());
            for (const auto& [key, ways] : layer) {
                int picked = key >> picked_shift;
                int available_below = 0;
                for (int i = 0; i < load; ++i) available_below += population(key, i);
                int bucket = population(key, load);
                int lo = std::max(0, k - picked - available_below);
                int hi = std::min(bucket, k - picked);
                for (int take = lo; take <= hi; ++take) {
                    Key loads = (key & loads_mask) + (Key(take) << (bits*(load+1)))
                              - (Key(take) << (bits*load));
                    if (load == 0 && !viable(loads, r, d-column-1, k)) continue;
                    Key target = loads;
                    if (load != 0) target |= Key(picked+take) << picked_shift;
                    auto [it, inserted] = next.try_emplace(target, 0);
                    mpz_addmul_ui(it->second.get_mpz_t(), ways.get_mpz_t(), choose[bucket][take]);
                }
            }
            layer = std::move(next);
            if (report) {
                std::cerr << "quota=" << k << " column=" << column+1
                          << " bucket=" << load << " states=" << layer.size() << '\n';
            }
        }
    }
    mpz_class total = 0;
    for (const auto& [key, weight] : layer) total += weight;
    return total;
}

mpz_class count_clipped(int n, int d, int r, int k, bool report) {
    if (k == 0) return 1;
    Layer layer{{Key(n) << (bits*r), mpz_class(1)}};
    for (int columns = d; columns >= 1; --columns) {
        int top = std::min(r, columns);
        for (int cap = 1; cap <= top; ++cap) {
            Layer next;
            next.reserve(layer.size());
            for (const auto& [key, ways] : layer) {
                int picked = key >> picked_shift;
                int available_above = 0;
                for (int i = cap+1; i <= top; ++i) available_above += population(key, i);
                int bucket = population(key, cap);
                int lo = std::max(0, k-picked-available_above);
                int hi = std::min(bucket, k-picked);
                for (int take = lo; take <= hi; ++take) {
                    // The largest remaining capacity clips regardless of selection
                    // when it equals the number of columns left.
                    int moved = cap == columns ? bucket : take;
                    Key loads = (key & loads_mask) + (Key(moved) << (bits*(cap-1)))
                              - (Key(moved) << (bits*cap));
                    Key target = loads;
                    if (cap == top) {
                        int capacity = 0;
                        for (int j = 1; j <= top; ++j) capacity += j * population(loads, j);
                        if (capacity < (columns-1)*k) continue;
                    } else {
                        target |= Key(picked+take) << picked_shift;
                    }
                    auto [it, inserted] = next.try_emplace(target, 0);
                    mpz_addmul_ui(it->second.get_mpz_t(), ways.get_mpz_t(), choose[bucket][take]);
                }
            }
            layer = std::move(next);
            if (report) {
                std::cerr << "quota=" << k << " remaining=" << columns
                          << " capacity=" << cap << " states=" << layer.size() << '\n';
            }
        }
    }
    mpz_class result = 0;
    for (const auto& [key, ways] : layer) result += ways;
    return result;
}

int main(int argc, char** argv) {
    if (argc < 4 || argc > 7) return 2;
    int n = std::atoi(argv[1]), d = std::atoi(argv[2]), r = std::atoi(argv[3]);
    if (n < 0 || n > 63 || d < 1 || r < 1 || r > std::min(d,7)) return 2;
    int first = argc >= 5 ? std::atoi(argv[4]) : 0;
    int last = argc >= 6 ? std::atoi(argv[5]) : n*r/d;
    bool report = argc == 7;
    if (first < 0 || first > last || last > n*r/d) return 2;
    for (int i = 0; i <= n; ++i) {
        choose[i][0] = choose[i][i] = 1;
        for (int j = 1; j < i; ++j) choose[i][j] = choose[i-1][j-1] + choose[i-1][j];
    }
    for (int k = first; k <= last; ++k) {
        auto start = std::chrono::steady_clock::now();
#ifdef CLIPPED
        auto result = count_clipped(n,d,r,k,report);
#else
        auto result = count(n,d,r,k,report);
#endif
        auto elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now()-start);
        std::cout << "{\"n\":" << n << ",\"d\":" << d << ",\"r\":" << r
                  << ",\"k\":" << k << ",\"coefficient\":" << result
                  << ",\"seconds\":" << elapsed.count() << "}" << std::endl;
    }
}
