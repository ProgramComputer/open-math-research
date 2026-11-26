#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Wide = __uint128_t;
constexpr int bits = 48;
constexpr Word half = Word(1) << (bits-1);
constexpr Word full = Word(1) << bits;

struct Binary {
    Word m;
    int e;
    explicit Binary(Word x=0) : m(x),e(0) {
        if (x) {
            while(m < half) { m <<= 1; --e; }
        }
    }
    Binary(Word x, int exponent) : m(x),e(exponent) {}
};
bool operator<(Binary x, Binary y) {
    if (!x.m || !y.m) return x.m < y.m;
    return x.e < y.e || (x.e==y.e && x.m<y.m);
}
Binary pack(Wide x, int e, bool hi) {
    if (!x) return Binary();
    while (x >= full) {
        const int shift = x >= (Wide(full)<<bits) ? bits : 1;
        x = (x + (hi ? (Wide(1)<<shift)-1 : 0)) >> shift;
        e += shift;
    }
    while (x < half) { x <<= 1; --e; }
    return Binary(Word(x),e);
}
Word aligned(Word m, int delta, bool hi) {
    if (delta>=bits) return hi && m ? 1 : 0;
    return (m+(hi ? (Word(1)<<delta)-1 : 0)) >> delta;
}
Binary add(Binary a, Binary b, bool hi) {
    if (!a.m) return b;
    if (!b.m) return a;
    if (a.e < b.e) std::swap(a,b);
    return pack(a.m+aligned(b.m,a.e-b.e,hi),a.e,hi);
}
Binary subtract_clamped(Binary a, Binary b, bool hi) {
    if (a<b) return Binary();
    if (!b.m) return a;
    return pack(a.m-aligned(b.m,a.e-b.e,!hi),a.e,hi);
}
Binary multiply(Binary a, Binary b, bool hi) {
    if (!a.m || !b.m) return Binary();
    const Wide p=Wide(a.m)*b.m;
    return pack((p+(hi ? half-1 : 0))>>(bits-1),a.e+b.e+bits-1,hi);
}
Binary divide(Binary a, Binary b, bool hi) {
    if (!a.m) return Binary();
    if (!b.m) std::exit(2);
    const Wide numerator=Wide(a.m)<<bits;
    return pack((numerator+(hi ? b.m-1 : 0))/b.m,a.e-b.e-bits,hi);
}
Binary ratio(Word a, Word b, bool hi) { return divide(Binary(a),Binary(b),hi); }
Binary power(Binary base, int e, bool hi) {
    Binary x(1);
    while (e) {
        if (e%2) x=multiply(x,base,hi);
        e/=2;
        if (e) base=multiply(base,base,hi);
    }
    return x;
}
struct Band { Binary low, high; };
Binary prob_lower(int n, int d, int r, int k, Binary choose) {
    const Binary one(1);
    if (!k || r==d) return one;
    const int s=r+1;
    const auto p=ratio(k,n,true), q=ratio(n-k,n,true);
    const auto odds=ratio(k,n-k,true);
    auto term=multiply(multiply(choose,power(p,s,true),true),power(q,d-s,true),true);
    auto tail=term;
    for (int j=s;j<d;++j) {
        term=multiply(term,multiply(ratio(d-j,j+1,true),odds,true),true);
        tail=add(tail,term,true);
    }
    return subtract_clamped(one,multiply(Binary(n),tail,true),false);
}

int main(int argc,char** argv) {
    const int first=argc>1 ? std::stoi(argv[1]) : 36;
    const int last=argc>2 ? std::stoi(argv[2]) : 1023;
    const int num=argc>3 ? std::stoi(argv[3]) : 9;
    const int den=argc>4 ? std::stoi(argv[4]) : 10;
    const int offset=argc>5 ? std::stoi(argv[5]) : 0;
    if (argc>6 || first<36 || last>1023 || first>last ||
        !((num==9 && den==10 && (offset==0 || offset==1)) ||
          (num==19 && den==20 && offset==0))) {
        std::cerr<<"Unsupported finite sweep parameters\n";
        return 2;
    }
    const Binary one(1),four(4),wide_center=ratio(9,4,false),tau=ratio(2,3,true);
    long long tuples=0,covered=0,failures=0,active=0;
    for (int n=first;n<=last;++n) {
        std::vector<Band> base(n);
        for (int k=1;k<n;++k) {
            const auto x=(k+1)*(n-k+1),y=k*(n-k);
            base[k]={ratio(x,y,false),ratio(x,y,true)};
        }
        for (int d=(n+3)/4;d<n;++d) {
            const int r=(num*d+den-1)/den+offset;
            if (r>=d-1) continue;
            if (four<power(base[n/2].low,d,false)) break;
            const int D=n*r/d;
            if (D<n/2 || !(four<power(base[D].low,d,false))) {
                std::cerr<<"Extra quota cutoff failed\n";return 2;
            }
            ++tuples;
            Binary choose(1);
            for (int j=1;j<=d-r-1;++j)
                choose=divide(multiply(choose,Binary(d-j+1),true),Binary(j),true);
            std::vector<Band> g(n);
            std::vector<Binary> prob(n);
            std::vector<bool> evaluated(n,false);
            auto curvature=[&](int k) {
                if (!g[k].low.m)
                    g[k]={power(base[k].low,d,false),power(base[k].high,d,true)};
                return g[k];
            };
            auto lower=[&](int k) {
                if (!evaluated[k]) {
                    prob[k]=prob_lower(n,d,r,k,choose);
                    evaluated[k]=true;
                }
                return prob[k];
            };
            int failed=0,start=0,end=0;
            for (int k=1;k<D;++k) {
                const auto center=curvature(k).low;
                if (four<center) continue;
                ++active;
                if (k<3 || k+3>D || center<wide_center) {
                    std::cerr<<"Unsupported active quota\n";return 2;
                }
                Binary correction;
                for (int e : {-1,1}) {
                    const auto neighbor=curvature(k+e);
                    const auto other=curvature(k+2*e).low;
                    const auto factor=subtract_clamped(one,
                        divide(tau,multiply(neighbor.low,other,false),true),false);
                    const auto weighted=multiply(multiply(factor,lower(k),false),lower(k+2*e),false);
                    correction=add(correction,divide(weighted,neighbor.high,false),false);
                }
                const auto total=add(center,std::min(correction,one),false);
                if (!(multiply(four,center,true)<multiply(total,total,false))) {
                    if (!failed) start=k;
                    end=k; ++failed;
                }
            }
            if (failed) {
                ++failures;
                std::cout<<n<<' '<<d<<' '<<r<<' '<<failed<<' '<<start<<' '<<end<<'\n';
            } else ++covered;
        }
    }
    std::cerr<<"nontrivial tuples "<<tuples<<", covered "<<covered
             <<", incomplete "<<failures<<", active quotas "<<active<<'\n';
}
