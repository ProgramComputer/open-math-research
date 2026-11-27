"""Additional exact tests of each supplying release's first analytic pair."""
import gzip
from pathlib import Path
from runpy import run_path

ROOT = Path(__file__).resolve().parent


def four():
    finite = run_path(str(ROOT/'4/certificates/k4/verify.py'))
    old,new=511,512
    rows={n:finite['extract_gamma'](row) for n,row in finite['original_rows'](new) if n>=old}
    data={}
    with gzip.open(ROOT/'4/certificates/k4/certificate.txt.gz','rt',encoding='ascii') as f:
        assert f.readline().strip()==finite['HEADER']
        for n in range(4,new+1):
            line=f.readline()
            if n>=old:
                vals=list(map(int,line.split()))
                data[n]=vals
    boxes={}
    ordered=finite['negative_less']
    for n in (old,new):
        g=rows[n]
        d=len(g)-1
        vals=data[n]
        assert vals[:2]==[n,d] and len(vals)==2+4*d
        boxes[n]=[]
        for index in range(d):
            i=2+4*index
            a=finite['dyadic'](*vals[i:i+2])
            b=finite['dyadic'](*vals[i+2:i+4])
            assert ordered(a,b)
            if boxes[n]:
                assert ordered(boxes[n][-1][1],a)
            expect=(-1)**(d-index)
            assert finite['endpoint_sign'](g,a)==expect
            assert finite['endpoint_sign'](g,b)==-expect
            boxes[n].append((a,b))
    assert len(boxes[new])==len(boxes[old])+1
    alternated=boxes[new][:1]
    for a,b in zip(boxes[old],boxes[new][1:]):
        alternated.extend((a,b))
    assert all(ordered(a[1],b[0]) for a,b in zip(alternated,alternated[1:]))
    print(f'k=4 first analytic pair ({old},{new}): {len(alternated)} exact gamma brackets, strict order.')


def higher(k,path):
    finite=run_path(str(path))
    old,new=48,49
    E=finite['rows'](new,k)
    assert E[old][:2]==E[new][:2]==[0,1]
    a=finite['primitive'](E[new][1:])
    b=finite['primitive'](E[old][1:])
    assert len(a)==new-1 and len(b)==old-1
    assert all(c>0 for c in a+b)
    count=0
    while len(b)>1:
        c=finite['primitive'](finite['signed_remainder'](a,b))
        assert len(b)==len(a)-1 and len(c)==len(b)-1 and c[-1]>0
        a,b=b,c
        count+=1
    assert len(a)==2 and len(b)==1 and b[0]>0
    print(f'k={k} first analytic pair ({old},{new}): {count} exact positive signed remainder drops.')


if __name__=='__main__':
    assert __debug__
    four()
    higher(5,ROOT/'5/cutoff-five/certificates/finite.py')
    higher(6,ROOT/'6/cutoff-six/numerics/fixed-five-effective/finite.py')
