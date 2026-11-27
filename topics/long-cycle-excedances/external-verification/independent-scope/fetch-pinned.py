from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen

repo = 'AlexZander-666/long-cycle-excedance-interlacing'
root = Path(__file__).resolve().parent
pins = {
    4: ('v1.0.0','f8fef864286a1bbc59f96484074f28d77b1a027f'),
    5: ('v1.1.0','70cad373bce521d78d6de9bcff3d29d07fc7fe9f'),
    6: ('v1.2.0','46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554'),
}
files = {
    4: ('README.md','paper/main.tex','certificates/k4/verify.py','certificates/k4/certificate.txt.gz',
        'verification/README.md','paper/four.tex','paper/finite.tex','LongCycles/Statement.lean','FixedFourAllAudit.lean',
        'LongCycleBounds/FixedFourAllSizes.lean','LongCycleBounds/FixedFourVerified.lean',
        'LongCycleBounds/BandFormula.lean','LongCycleBounds/GeneralCycleQuotient.lean',
        'LongCycleFinite/K4FiniteOriginal0511.lean','LongCycleFinite/Interlacing.lean'),
    5: tuple('cutoff-five/'+p for p in (
        'README.md','paper/main.tex','paper/five.tex','certificates/finite.py','certificates/check.py',
        'certificates/compact/cells.tsv','certificates/compact/verify.py',
        'certificates/middle/constants.json','certificates/middle/verify.py','verification/README.md',
        'formal/LongCycles/Statement.lean','formal/CutoffFiveFinalAudit.lean',
        'formal/LongCycleBounds/FiveCutoffVerified.lean',
        'formal/LongCycleBounds/CycleProfileIndependentReadout.lean',
        'formal/LongCycleBounds/GeneralCycleQuotient.lean','formal/LongCycleFinite/K5Prefix/All.lean',
        'formal/LongCycleFinite/K5Prefix/Base.lean','formal/LongCycleFinite/Interlacing.lean')),
    6: tuple('cutoff-six/'+p for p in (
        'README.md','paper/main.tex','paper/six.tex','cutoff-six-scalar-check.py',
        'numerics/fixed-six-effective/cells.tsv','numerics/fixed-six-effective/check.py',
        'numerics/fixed-five-effective/check.py','numerics/fixed-five-effective/finite.py',
        'verification/STATEMENT-MAP.md','verification/FORMAL-STATUS.md',
        'verification/ERRATA.md','verification/arithmetic.log')),
}


def read(url):
    with urlopen(url,timeout=30) as f:
        return f.read()


def get_release(item):
    n,(tag,commit)=item
    api=f'https://api.github.com/repos/{repo}'
    actual=json.loads(read(f'{api}/commits/{tag}'))['sha']
    assert actual==commit,(tag,actual)
    tree=json.loads(read(f'{api}/git/trees/{commit}?recursive=1'))
    assert not tree['truncated']
    entries={r['path']:r for r in tree['tree'] if r['type']=='blob'}
    records=[]
    for name in files[n]:
        if name not in entries:
            raise RuntimeError((n,'path unavailable',name))
        info=entries[name]
        url=f'https://raw.githubusercontent.com/{repo}/{commit}/{name}'
        target=root/str(n)/name
        data=target.read_bytes() if target.is_file() else read(url)
        assert len(data)==info['size']
        sha=hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()
        assert sha==info['sha']
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(data)
        records.append(f'{n}\t{tag}\t{commit}\t{sha}\t{len(data)}\t{name}')
    return records

if __name__ == '__main__':
    with ThreadPoolExecutor(3) as pool:
        table=list(pool.map(get_release,pins.items()))
    out=root/'pinned-sources.tsv'
    out.write_text('k\ttag\tcommit\tblob\tbytes\tpath\n'+'\n'.join(x for row in table for x in row)+'\n')
    for n,rows in zip(pins,table):
        print(f'k={n}: {len(rows)} pinned files verified.')
