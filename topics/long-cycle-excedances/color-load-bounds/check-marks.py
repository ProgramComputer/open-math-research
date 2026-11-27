"""Compare literal color-orbit counts, including fixed colors, with binomial first moments."""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import comb, factorial


def color_cycles(perm):
    left = set(range(len(perm)))
    while left:
        color = min(left)
        members = []
        while color in left:
            left.remove(color)
            members.append(color)
            color = perm[color]
        yield members


def main():
    cases = cells = total = 0
    for n in range(7):
        for p in range(1, 5):
            mass = Counter()
            minima = Counter()
            denominator = factorial(p)*p**n
            for perm in permutations(range(p)):
                cycles = list(color_cycles(perm))
                sizes = [len(c) for c in cycles]
                owner = {v: i for i,c in enumerate(cycles) for v in c}
                for word in product(range(p), repeat=n):
                    load = [0]*len(cycles)
                    for color in word:
                        load[owner[color]] += 1
                    mass.update(zip(sizes, load))
                    minima[min(sizes), min(load)] += 1
            assert sum(minima.values()) == denominator
            total += denominator
            for j in range(1,p+1):
                for i in range(n+1):
                    probability = (Fraction(1,j)*comb(n,i)*
                                   Fraction(j,p)**i*Fraction(p-j,p)**(n-i))
                    assert probability == Fraction(mass[j,i],denominator)
                    cells += 1
            for k in range(1,7):
                for b in range(1,p+2):
                    baseline = sum(v for (s,_),v in minima.items() if s >= b)
                    accepted = sum(v for (_,a),v in minima.items() if a >= k)
                    lower_loss = sum(v for (j,i),v in mass.items() if j>=b and i<k)
                    upper_loss = sum(v for (j,i),v in mass.items() if j<b and i>=k)
                    assert baseline-lower_loss <= accepted <= baseline+upper_loss
                    cases += 1
    print(f"{total} literal word-permutation pairs, {cells} exact marked-load masses.")
    print(f"Both comparison inequalities passed for {cases} parameter quadruples.")
    print("0 <= n <= 6, 1 <= p <= 4, 1 <= k <= 6, 1 <= b <= p+1.")


if __name__ == "__main__":
    main()
