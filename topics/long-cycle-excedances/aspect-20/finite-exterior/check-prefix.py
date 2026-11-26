"""Cross-check the rolling cycle prefixes against the insertion recurrence."""
from math import comb, isqrt
from time import perf_counter

from flint import fmpz_poly

from check import eulerian, update

last=1001
width=isqrt(49*(last-1))//20+4
cycle=eulerian(last-1,width)
rolling={n:cycle[n-1] for n in range(last//2+1,last+1)}
thresholds={4,5,9,10,19,22,23,31,49,64,99,100,124,125,166,249,250}
t=fmpz_poly([0,1])
one=fmpz_poly([1])
count=0
start=perf_counter()
for k in range(last//2,min(thresholds)-1,-1):
    update(rolling,cycle,last,k,width)
    if k not in thresholds:
        continue
    rebuilt={k:cycle[k-1]}
    assert rebuilt[k]==rolling[k]
    for n in range(k,last):
        current=rebuilt[n]
        following=(one+(n-1)*t)*current+t*(one-t)*current.derivative()
        m=n+1-k
        if m>=k:
            following+=comb(n,k-1)*t*cycle[k-1].mul_low(rebuilt[m],width-1)
        rebuilt[n+1]=following.truncate(width)
        if rebuilt[n+1]!=rolling[n+1]:
            raise ArithmeticError((k,n+1))
        count+=1
    count+=1
print(f"Independent insertion recurrence matched {count} width-{width} prefixes "
      f"through row {last} at {len(thresholds)} thresholds in {perf_counter()-start:.2f}s.")
