#include <algorithm>
#include <cmath>
#include <cfenv>
#include <iostream>
#include <limits>
#include <vector>

static_assert(std::numeric_limits<double>::is_iec559, "IEEE binary64 required");
constexpr double inf = std::numeric_limits<double>::infinity();
double dn(double x) { return std::nextafter(x, -inf); }
double up(double x) { return std::nextafter(x, inf); }
double pw(double x, int e, double (*round)(double)) {
    double y = 1;
    while (e) {
        if (e%2) y = round(y*x);
        e /= 2;
        if (e) x = round(x*x);
    }
    return y;
}
struct Band { double lo, hi; };
Band base(int n, int k) {
    const double b = double((k+1)*(n-k+1))/(k*(n-k));
    return {dn(b), up(b)};
}
double prob_lower(int n, int d, int r, int k, double choose) {
    if (k == 0 || r == d) return 1;
    const int s = r+1;
    const double p = up(double(k)/n), q = up(double(n-k)/n);
    const double qlo = dn(double(n-k)/n);
    double term = up(up(choose*pw(p,s,up))*pw(q,d-s,up));
    double tail = term;
    const double odds = up(p/qlo);
    for (int j=s; j<d; ++j) {
        term = up(term*up(up(double(d-j)/(j+1))*odds));
        tail = up(tail+term);
    }
    return std::max(0.,dn(1-up(n*tail)));
}
int main(int argc, char** argv) {
    if (std::fegetround() != FE_TONEAREST) return 2;
    const int minimum = argc>1 ? std::stoi(argv[1]) : 36;
    const int maximum = argc>2 ? std::stoi(argv[2]) : 1023;
    const int num = argc>3 ? std::stoi(argv[3]) : 9;
    const int den = argc>4 ? std::stoi(argv[4]) : 10;
    const int offset = argc>5 ? std::stoi(argv[5]) : 0;
    long long tuples=0, failures=0, covered=0, active=0;
    for (int n=minimum; n<=maximum; ++n) {
        std::vector<Band> b(n);
        for (int k=1;k<n;++k) b[k]=base(n,k);
        for (int d=(n+3)/4; d<n; ++d) {
            const int r=(num*d+den-1)/den+offset;
            if (r>=d-1) continue;  // endpoint theorem
            if (pw(b[n/2].lo,d,dn)>4) break;  // all future d also separated
            const int D=n*r/d;
            ++tuples;
            double choose=1;
            for (int j=1;j<=d-r-1;++j)
                choose=up(up(choose*(d-j+1))/j);  // choose(d,r+1)
            std::vector<Band> g(n, {-1.,-1.});
            std::vector<double> prob(n+1,-1.);
            auto curvature=[&](int k) {
                if (g[k].lo<0) g[k]={pw(b[k].lo,d,dn),pw(b[k].hi,d,up)};
                return g[k];
            };
            auto p_lower=[&](int k) {
                if (prob[k]<0) prob[k]=prob_lower(n,d,r,k,choose);
                return prob[k];
            };
            int failed=0, first=0, last=0;
            for (int k=1;k<D;++k) {
                const double center=curvature(k).lo;
                if (center>4) continue;
                ++active;
                if (k<3 || k+3>D) { std::cerr<<"Active boundary quota\n"; return 2; }
                double correction=0;
                for (int e : {-1,1}) {
                    if (k+2*e<0 || k+2*e>D) continue;
                    const auto neighbor=curvature(k+e);
                    double factor=1;
                    if (0<=k+3*e && k+3*e<=D) {
                        const double other=curvature(k+2*e).lo;
                        if (center<2.25) { std::cerr<<"Unsupported low center\n"; return 2; }
                        factor=dn(1-up(up(2./3)/dn(neighbor.lo*other)));
                    }
                    correction=dn(correction+dn(dn(dn(factor*p_lower(k))*p_lower(k+2*e))/neighbor.hi));
                }
                const double total=dn(center+std::min(std::max(correction,0.),1.));
                if (dn(total*total)<=up(4*center)) {
                    if (!failed) first=k;
                    last=k; ++failed;
                }
            }
            if (failed) {
                ++failures;
                std::cout << n << ' ' << d << ' ' << r << ' ' << failed << ' ' << first << ' ' << last << '\n';
            } else ++covered;
        }
    }
    std::cerr << "nontrivial tuples " << tuples << ", covered " << covered
              << ", incomplete " << failures << ", active quotas " << active << '\n';
}
