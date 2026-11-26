"""Check the finite prefix of the uniform extreme-root argument, using integers."""
from argparse import ArgumentParser
from gzip import GzipFile
import json
from math import comb, gcd
from pathlib import Path

ARCHIVE = Path(__file__).with_name('prefix.jsonl.gz')
LIMIT = 32


def primitive(poly):
    while poly and poly[-1] == 0:
        poly.pop()
    content = 0
    for c in poly:
        content = gcd(content, c)
    return [c // content for c in poly]


def negative_remainder(left, right):
    """A positive multiple of minus the Euclidean remainder."""
    result = left[:]
    lead = abs(right[-1])
    sign = 1 if right[-1] > 0 else -1
    while len(result) >= len(right):
        offset = len(result) - len(right)
        q = sign * result[-1]
        result = [lead * c for c in result]
        for i, c in enumerate(right):
            result[i + offset] -= q * c
        result = primitive(result)
    return [-c for c in result]


def interlacing_chain(new, old):
    """Positive leading terms with successive degrees give strict alternation."""
    p, q = primitive(new[:]), primitive(old[:])
    degrees = [len(p)-1]
    while q:
        if len(q) + 1 != len(p) or min(p[-1], q[-1]) <= 0:
            raise ArithmeticError('Strict signed remainder chain failed')
        degrees.append(len(q)-1)
        p, q = q, negative_remainder(p, q)
    if degrees[-1] != 0:
        raise ArithmeticError('Common factor')
    return degrees


def eulerian_rows():
    rows = [[1]]
    for n in range(1, LIMIT + 1):
        old = rows[-1]
        rows.append([(i+1)*(old[i] if i < len(old) else 0)
                     + (n-i)*(old[i-1] if i > 0 else 0) for i in range(n)])
    return rows


def add_product(dest, a, b, multiplier):
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            dest[i+j+1] += multiplier*x*y


def rows(k, eulerian):
    """Distinguished cycle decomposition and independently, deletion of the maximum."""
    decomposition = [[1]] + [[] for _ in range(k-1)]
    insertion = [[1]] + [[] for _ in range(k-1)]
    for n in range(k, LIMIT + 1):
        a, b = [0]*n, [0]*n
        for length in range(k, n+1):
            add_product(a, eulerian[length-1], decomposition[n-length], comb(n-1,length-1))
        for i, x in enumerate(insertion[n-1]):
            b[i] += i*x
            b[i+1] += (n-1-i)*x
        add_product(b, eulerian[k-1], insertion[n-k], comb(n-1,k-1))
        if a != b or a[0] != 0 or a[1] != 1 or a[1:] != a[:0:-1]:
            raise ArithmeticError((n,k,'coefficient construction'))
        two = 2**(n-1)-n + sum(comb(n,l) for l in range(k,n-k+1))//2
        if a[2] != two or any(x > i**n for i,x in enumerate(a[1:],1)):
            raise ArithmeticError((n,k,'run bounds'))
        decomposition.append(a)
        insertion.append(b)
    return decomposition


def records():
    eulerian = eulerian_rows()
    for k in range(3,LIMIT+1):
        computed = rows(k,eulerian)
        for n in range(k,LIMIT+1):
            a = computed[n]
            p = a[1:]
            derivative = [i*p[i] for i in range(1,len(p))]
            yield dict(n=n,k=k,coefficients=a,sturm_degrees=interlacing_chain(p,derivative),
                       consecutive_degrees=interlacing_chain(p,computed[n-1][1:]) if n>k else None)


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    count=pairs=0
    if args.write:
        with ARCHIVE.open('xb') as raw, GzipFile(filename='', mode='wb', fileobj=raw,mtime=0) as dest:
            for item in records():
                dest.write((json.dumps(item,separators=(',',':'))+'\n').encode())
                count+=1
                pairs+=item['consecutive_degrees'] is not None
    else:
        with GzipFile(ARCHIVE,'rb') as src:
            for line,item in zip(src,records(),strict=True):
                if json.loads(line)!=item:
                    raise ArithmeticError('Archive mismatch')
                count+=1
                pairs+=item['consecutive_degrees'] is not None
    print(f'Certified {count} rows and {pairs} consecutive pairs.')


if __name__=='__main__':
    main()
