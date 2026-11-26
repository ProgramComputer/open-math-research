#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>
#include <mpfr.h>

typedef struct {
    mpfr_t lo, hi;
} interval;

typedef struct {
    interval real, imag;
} complex_interval;

static mpfr_prec_t precision;

static void fail(const char *message)
{
    fputs(message, stderr);
    fputc('\n', stderr);
    exit(EXIT_FAILURE);
}

static void init(interval *a)
{
    mpfr_inits2(precision, a->lo, a->hi, (mpfr_ptr) 0);
}

static void clear(interval *a)
{
    mpfr_clears(a->lo, a->hi, (mpfr_ptr) 0);
}

static void set_zero(interval *a)
{
    mpfr_set_zero(a->lo, 1);
    mpfr_set_zero(a->hi, 1);
}

static void read_integer(mpz_t z)
{
    if (mpz_inp_str(z, stdin, 16) == 0 || mpz_sgn(z) < 0) {
        fail("Invalid nonnegative hexadecimal integer");
    }
}

static int strict_sign(const interval *a)
{
    if (mpfr_sgn(a->lo) > 0) {
        return 1;
    }
    if (mpfr_sgn(a->hi) < 0) {
        return -1;
    }
    return 0;
}

static complex_interval *make_terms(const interval *pi, unsigned long d,
                                   unsigned long top, unsigned long degree)
{
    complex_interval *terms = calloc(degree + 1, sizeof(*terms));
    if (!terms) {
        fail("Cannot allocate row coefficients");
    }
    interval angle;
    init(&angle);
    mpz_t coefficient;
    mpz_init(coefficient);
    for (unsigned long j = 0; j <= degree; ++j) {
        interval *real = &terms[j].real, *imag = &terms[j].imag;
        init(real);
        init(imag);
        if (j == 0) {
            mpfr_set_ui(real->lo, 1, MPFR_RNDN);
            mpfr_set_ui(real->hi, 1, MPFR_RNDN);
            set_zero(imag);
            continue;
        }

        mpfr_mul_ui(angle.lo, pi->lo, j, MPFR_RNDD);
        mpfr_mul_ui(angle.hi, pi->hi, j, MPFR_RNDU);
        mpfr_div_ui(angle.lo, angle.lo, d, MPFR_RNDD);
        mpfr_div_ui(angle.hi, angle.hi, d, MPFR_RNDU);
        if (mpfr_sgn(angle.lo) <= 0 || mpfr_cmp(angle.hi, pi->lo) >= 0) {
            fail("Angle interval exceeds the cosine monotonicity range");
        }
        mpfr_div_2ui(real->lo, pi->lo, 1, MPFR_RNDN);
        mpfr_div_2ui(real->hi, pi->hi, 1, MPFR_RNDN);
        if (2 * j < d) {
            if (mpfr_cmp(angle.hi, real->lo) >= 0) {
                fail("Angle interval exceeds the increasing-sine range");
            }
            mpfr_sin(imag->lo, angle.lo, MPFR_RNDD);
            mpfr_sin(imag->hi, angle.hi, MPFR_RNDU);
        } else if (2 * j > d) {
            if (mpfr_cmp(angle.lo, real->hi) <= 0) {
                fail("Angle interval exceeds the decreasing-sine range");
            }
            mpfr_sin(imag->lo, angle.hi, MPFR_RNDD);
            mpfr_sin(imag->hi, angle.lo, MPFR_RNDU);
        } else {
            mpfr_set_ui(imag->lo, 1, MPFR_RNDN);
            mpfr_set_ui(imag->hi, 1, MPFR_RNDN);
        }
        mpfr_cos(real->lo, angle.hi, MPFR_RNDD);
        mpfr_cos(real->hi, angle.lo, MPFR_RNDU);

        mpz_bin_uiui(coefficient, top, j);
        mpfr_mul_z(real->lo, real->lo, coefficient, MPFR_RNDD);
        mpfr_mul_z(real->hi, real->hi, coefficient, MPFR_RNDU);
        mpfr_mul_z(imag->lo, imag->lo, coefficient, MPFR_RNDD);
        mpfr_mul_z(imag->hi, imag->hi, coefficient, MPFR_RNDU);
    }
    mpz_clear(coefficient);
    clear(&angle);
    return terms;
}

static void free_terms(complex_interval *terms, unsigned long degree)
{
    for (unsigned long j = 0; j <= degree; ++j) {
        clear(&terms[j].real);
        clear(&terms[j].imag);
    }
    free(terms);
}

static void horner_point(interval *v, const interval *coefficient, mpfr_srcptr w)
{
    mpfr_mul(v->lo, v->lo, w, MPFR_RNDD);
    mpfr_mul(v->hi, v->hi, w, MPFR_RNDU);
    mpfr_add(v->lo, v->lo, coefficient->lo, MPFR_RNDD);
    mpfr_add(v->hi, v->hi, coefficient->hi, MPFR_RNDU);
}

static void row_arg(interval *arg, const complex_interval *terms,
                    unsigned long degree, mpfr_srcptr w)
{
    if (!degree) {
        set_zero(arg);
        return;
    }
    interval x, y;
    init(&x);
    init(&y);
    set_zero(&x);
    set_zero(&y);
    for (unsigned long j = degree + 1; j > 0; --j) {
        horner_point(&x, &terms[j - 1].real, w);
        horner_point(&y, &terms[j - 1].imag, w);
    }
    if (mpfr_sgn(y.lo) <= 0) {
        fail("Unable to establish that the argument stays in the upper half-plane");
    }

    /* On y>0, atan2(y,x) decreases in x. Its derivative in y has the sign of x. */
    mpfr_atan2(arg->lo, mpfr_sgn(x.hi) >= 0 ? y.lo : y.hi, x.hi, MPFR_RNDD);
    mpfr_atan2(arg->hi, mpfr_sgn(x.lo) >= 0 ? y.hi : y.lo, x.lo, MPFR_RNDU);
    clear(&x);
    clear(&y);
}

static int phase_sign(mpfr_srcptr w, unsigned long n, unsigned long d,
                      unsigned long r, unsigned long k, const interval *theta,
                      const complex_interval *h, const complex_interval *b)
{
    interval a, c, difference;
    init(&a);
    init(&c);
    init(&difference);
    row_arg(&a, h, r, w);
    row_arg(&c, b, r - 1, w);
    mpfr_mul_ui(a.lo, a.lo, 2 * n + d - 1, MPFR_RNDD);
    mpfr_mul_ui(a.hi, a.hi, 2 * n + d - 1, MPFR_RNDU);
    mpfr_mul_ui(c.lo, c.lo, d - 1, MPFR_RNDD);
    mpfr_mul_ui(c.hi, c.hi, d - 1, MPFR_RNDU);
    mpfr_sub(difference.lo, a.lo, c.hi, MPFR_RNDD);
    mpfr_sub(difference.hi, a.hi, c.lo, MPFR_RNDU);
    mpfr_mul_ui(a.lo, theta->lo, 2 * k * d + d - 1, MPFR_RNDD);
    mpfr_mul_ui(a.hi, theta->hi, 2 * k * d + d - 1, MPFR_RNDU);
    mpfr_sub(difference.lo, difference.lo, a.hi, MPFR_RNDD);
    mpfr_sub(difference.hi, difference.hi, a.lo, MPFR_RNDU);
    int sign = strict_sign(&difference);
    clear(&a);
    clear(&c);
    clear(&difference);
    return sign;
}

static int polynomial_sign(interval *value, const interval *bracket, unsigned long d,
                           const interval *coefficients, unsigned long degree)
{
    interval x;
    init(&x);
    mpfr_pow_ui(x.lo, bracket->lo, d, MPFR_RNDD);
    mpfr_pow_ui(x.hi, bracket->hi, d, MPFR_RNDU);
    set_zero(value);
    for (unsigned long j = degree + 1; j > 0; --j) {
        /* Enclose x times value, then reverse endpoints for multiplication by -1. */
        mpfr_mul(value->lo, value->lo, mpfr_sgn(value->lo) < 0 ? x.hi : x.lo, MPFR_RNDD);
        mpfr_mul(value->hi, value->hi, mpfr_sgn(value->hi) > 0 ? x.hi : x.lo, MPFR_RNDU);
        mpfr_swap(value->lo, value->hi);
        mpfr_sub(value->lo, coefficients[j - 1].lo, value->lo, MPFR_RNDD);
        mpfr_sub(value->hi, coefficients[j - 1].hi, value->hi, MPFR_RNDU);
    }
    clear(&x);
    return strict_sign(value);
}

static void analytic_rank_one_hint(mpfr_t center, unsigned long n, unsigned long d,
                                   unsigned long k, const interval *theta)
{
    mpfr_t phi, complement;
    mpfr_inits2(precision, phi, complement, (mpfr_ptr) 0);
    unsigned long numerator = 2 * k * d + d - 1, denominator = 2 * n + d - 1;
    mpfr_mul_ui(phi, theta->lo, numerator, MPFR_RNDN);
    mpfr_mul_ui(complement, theta->lo, denominator - numerator, MPFR_RNDN);
    mpfr_div_ui(phi, phi, denominator, MPFR_RNDN);
    mpfr_div_ui(complement, complement, denominator, MPFR_RNDN);
    mpfr_sin(phi, phi, MPFR_RNDN);
    mpfr_sin(complement, complement, MPFR_RNDN);
    mpfr_mul_ui(complement, complement, d, MPFR_RNDN);
    mpfr_div(center, phi, complement, MPFR_RNDN);
    mpfr_clears(phi, complement, (mpfr_ptr) 0);
}

static int certify_node(unsigned long n, unsigned long d, unsigned long r,
                        unsigned long k, const interval *theta, const complex_interval *h,
                        const complex_interval *b, const interval *coefficients,
                        unsigned long degree, const mpz_t num, const mpz_t den)
{
    interval bracket, value;
    init(&bracket);
    init(&value);
    mpfr_t center, delta, other;
    mpfr_inits2(precision, center, delta, other, (mpfr_ptr) 0);

    long bits = 0;
    if (mpz_sgn(num) != 0) {
        mpfr_set_z(center, num, MPFR_RNDN);
        mpfr_div_z(center, center, den, MPFR_RNDN);
        bits = 36;
    } else if (r == 1) {
        analytic_rank_one_hint(center, n, d, k, theta);
        bits = precision - 32;
    }

    int bracketed = 0;
    for (; bits > 0; bits -= 8) {
        mpfr_div_2si(delta, center, bits, MPFR_RNDN);
        mpfr_sub(bracket.lo, center, delta, MPFR_RNDD);
        mpfr_add(bracket.hi, center, delta, MPFR_RNDU);
        if (phase_sign(bracket.lo, n, d, r, k, theta, h, b) < 0
            && phase_sign(bracket.hi, n, d, r, k, theta, h, b) > 0) {
            bracketed = 1;
            break;
        }
    }

    if (!bracketed) {
        mpfr_set_ui(bracket.lo, 1, MPFR_RNDN);
        mpfr_set_ui(bracket.hi, 1, MPFR_RNDN);
        for (unsigned long j = 0; j < 4096; ++j) {
            int lo = phase_sign(bracket.lo, n, d, r, k, theta, h, b);
            int hi = phase_sign(bracket.hi, n, d, r, k, theta, h, b);
            if (lo < 0 && hi > 0) {
                bracketed = 1;
                break;
            }
            if (lo >= 0) {
                mpfr_div_2ui(bracket.lo, bracket.lo, 1, MPFR_RNDN);
            }
            if (hi <= 0) {
                mpfr_mul_2ui(bracket.hi, bracket.hi, 1, MPFR_RNDN);
            }
        }
    }

    int sign = 0;
    unsigned long step = 0;
    if (bracketed) {
        for (; step <= (unsigned long) precision; ++step) {
            if (step % 8 == 0) {
                sign = polynomial_sign(&value, &bracket, d, coefficients, degree);
                if (sign) {
                    break;
                }
            }
            mpfr_add(center, bracket.lo, bracket.hi, MPFR_RNDN);
            mpfr_div_2ui(center, center, 1, MPFR_RNDN);
            if (mpfr_cmp(center, bracket.lo) <= 0 || mpfr_cmp(center, bracket.hi) >= 0) {
                break;
            }
            int mid = phase_sign(center, n, d, r, k, theta, h, b);
            if (mid < 0) {
                mpfr_set(bracket.lo, center, MPFR_RNDN);
            } else if (mid > 0) {
                mpfr_set(bracket.hi, center, MPFR_RNDN);
            } else {
                /* A zero-containing interval is common at the numerical midpoint. */
                mpfr_add(other, center, bracket.lo, MPFR_RNDN);
                mpfr_div_2ui(other, other, 1, MPFR_RNDN);
                int left = phase_sign(other, n, d, r, k, theta, h, b);
                if (left < 0 && mpfr_cmp(other, bracket.lo) > 0) {
                    mpfr_set(bracket.lo, other, MPFR_RNDN);
                }
                mpfr_add(other, center, bracket.hi, MPFR_RNDN);
                mpfr_div_2ui(other, other, 1, MPFR_RNDN);
                int right = phase_sign(other, n, d, r, k, theta, h, b);
                if (right > 0 && mpfr_cmp(other, bracket.hi) < 0) {
                    mpfr_set(bracket.hi, other, MPFR_RNDN);
                }
                if (left >= 0 && right <= 0) {
                    break;
                }
            }
        }
        sign = polynomial_sign(&value, &bracket, d, coefficients, degree);
    }

    if (mpfr_nanflag_p() || mpfr_overflow_p() || mpfr_underflow_p()
        || mpfr_divby0_p() || mpfr_erangeflag_p()) {
        fail("Unexpected MPFR range or domain exception");
    }
    if (sign) {
        mpfr_printf("%lu,%lu,%lu,%lu,%d,%lu,%Ra,%Ra,%Ra\n",
                    n, d, r, k, sign, step, bracket.lo, bracket.hi,
                    sign > 0 ? value.lo : value.hi);
    } else {
        fprintf(stderr, "Uncertified n=%lu d=%lu r=%lu k=%lu, phase bracket=%d\n",
                n, d, r, k, bracketed);
    }
    clear(&bracket);
    clear(&value);
    mpfr_clears(center, delta, other, (mpfr_ptr) 0);
    return sign;
}

int main(int argc, char **argv)
{
    precision = argc == 2 ? strtol(argv[1], NULL, 10) : 128;
    if (precision < 96 || precision > 16384) {
        fail("Precision must be between 96 and 16384 bits");
    }
    unsigned long n, d, r, degree, nodes;
    unsigned long vectors = 0, certified = 0, reversed = 0, unresolved = 0;
    printf("n,d,r,k,sign,steps,lo,hi,signed_endpoint\n");
    int scanned;
    while ((scanned = scanf("%lu %lu %lu %lu %lu", &n, &d, &r, &degree, &nodes)) == 5) {
        if (n < d || n > 100000 || d < 2 || r < 1 || r >= d || degree != n * r / d
            || nodes >= degree) {
            fail("Invalid vector dimensions or degree");
        }
        mpfr_clear_flags();
        ++vectors;
        mpz_t integer, num, den;
        mpz_inits(integer, num, den, (mpz_ptr) 0);
        interval *coefficients = calloc(degree + 1, sizeof(*coefficients));
        if (!coefficients) {
            fail("Cannot allocate target coefficients");
        }
        for (unsigned long j = 0; j <= degree; ++j) {
            init(&coefficients[j]);
            read_integer(integer);
            if (mpz_sgn(integer) <= 0 || (j == 0 && mpz_cmp_ui(integer, 1) != 0)) {
                fail("Invalid balanced-array coefficient");
            }
            mpfr_set_z(coefficients[j].lo, integer, MPFR_RNDD);
            mpfr_set_z(coefficients[j].hi, integer, MPFR_RNDU);
        }
        interval pi, theta;
        init(&pi);
        init(&theta);
        mpfr_const_pi(pi.lo, MPFR_RNDD);
        mpfr_const_pi(pi.hi, MPFR_RNDU);
        mpfr_div_ui(theta.lo, pi.lo, d, MPFR_RNDD);
        mpfr_div_ui(theta.hi, pi.hi, d, MPFR_RNDU);
        complex_interval *h = make_terms(&pi, d, d, r);
        complex_interval *b = make_terms(&pi, d, d - 2, r - 1);
        unsigned long last = 0;
        for (unsigned long j = 0; j < nodes; ++j) {
            unsigned long k;
            if (scanf("%lu", &k) != 1 || k <= last || k >= degree) {
                fail("Invalid angular node quota");
            }
            last = k;
            read_integer(num);
            read_integer(den);
            if (mpz_sgn(den) <= 0 || mpz_popcount(den) != 1) {
                fail("Expected a positive power of two as the dyadic denominator");
            }
            int sign = certify_node(n, d, r, k, &theta, h, b, coefficients, degree, num, den);
            if (!sign) {
                ++unresolved;
            } else {
                ++certified;
                if (sign != (k % 2 ? -1 : 1)) {
                    ++reversed;
                    fprintf(stderr, "REVERSED n=%lu d=%lu r=%lu k=%lu\n", n, d, r, k);
                    fflush(stdout);
                }
            }
        }
        free_terms(h, r);
        free_terms(b, r - 1);
        clear(&pi);
        clear(&theta);
        for (unsigned long j = 0; j <= degree; ++j) {
            clear(&coefficients[j]);
        }
        free(coefficients);
        mpz_clears(integer, num, den, (mpz_ptr) 0);
    }
    if (scanned != EOF) {
        fail("Unparsed input after final vector");
    }
    fprintf(stderr,
            "MPFR %s, GMP %s, %ld bits: %lu vectors, %lu certified, %lu reversed, %lu unresolved\n",
            mpfr_get_version(), gmp_version, precision, vectors, certified, reversed, unresolved);
    return unresolved ? EXIT_FAILURE : EXIT_SUCCESS;
}
