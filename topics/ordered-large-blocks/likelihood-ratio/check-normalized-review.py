from math import comb


def rows(j, weight, nmax):
    output = [[1]]
    for n in range(1, nmax+1):
        row = [0]*(n//j+1)
        for size in range(1, n+1):
            multiplier = weight*comb(n,size)
            mark = int(size>=j)
            for i, value in enumerate(output[n-size]):
                row[i+mark] += multiplier*value
        output.append(row)
    return output


def check():
    minors = slopes = 0
    for weight in (1,2,3):
        for j in range(2,13):
            table = rows(j,weight,80)
            for n, row in enumerate(table):
                for k in range(1,len(row)-1):
                    assert (k+1)*(n-(k-1)*j)*row[k+1]*row[k-1] < k*(n-k*j)*row[k]**2
                    minors += 1
                if n==0:
                    continue
                previous = table[n-1]
                for k in range(1,min(len(previous),len(row))):
                    offset = (k-1)*j
                    assert row[k]*previous[k-1]*(n-1-offset) >= previous[k]*row[k-1]*(n-offset)
                    slopes += 1
    print(f'{minors} strict falling-binomial minors and {slopes} nondecreasing slope comparisons passed.')


if __name__ == '__main__':
    check()
