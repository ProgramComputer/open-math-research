/* Independent directed-rounding certificate for two finite sign ranges. */
#include <gmp.h>
#include <mpfr.h>
#include <stdio.h>
#include <stdlib.h>

enum { PRECISION = 1024, TERM_LIMIT = 4096 };

static unsigned long certify_sign(unsigned long d, unsigned long k)
{
    mpfr_t x_lo, x_hi, u_lo, u_hi, ratio_lo, ratio_hi;
    mpfr_t term_lo, term_hi, even_lo, even_hi, odd_lo, odd_hi, signed_lo;
    mpfr_inits2(PRECISION, x_lo, x_hi, u_lo, u_hi, ratio_lo, ratio_hi,
                term_lo, term_hi, even_lo, even_hi, odd_lo, odd_hi,
                signed_lo, (mpfr_ptr) 0);
    mpfr_clear_flags();

    mpfr_const_pi(x_lo, MPFR_RNDD);
    mpfr_const_pi(x_hi, MPFR_RNDU);
    mpfr_div_ui(x_lo, x_lo, d, MPFR_RNDD);
    mpfr_div_ui(x_hi, x_hi, d, MPFR_RNDU);
    if (mpfr_sgn(x_lo) <= 0 || mpfr_cmp_d(x_hi, 1.5) >= 0) {
        fputs("Invalid sine interval\n", stderr);
        exit(EXIT_FAILURE);
    }

    /* Monotonicity of sine on [0, 1.5], and positive denominators. */
    mpfr_sin(ratio_lo, x_lo, MPFR_RNDD);
    mpfr_sin(ratio_hi, x_hi, MPFR_RNDU);
    if (mpfr_sgn(ratio_lo) <= 0) {
        fputs("Nonpositive lower bound for the sine\n", stderr);
        exit(EXIT_FAILURE);
    }
    mpfr_div(u_lo, x_lo, ratio_hi, MPFR_RNDD);
    mpfr_div(u_hi, x_hi, ratio_lo, MPFR_RNDU);
    unsigned long numerator = 2 * d * k + d - 1;
    mpfr_mul_ui(u_lo, u_lo, numerator, MPFR_RNDD);
    mpfr_mul_ui(u_hi, u_hi, numerator, MPFR_RNDU);
    mpfr_div_ui(u_lo, u_lo, 2 * d, MPFR_RNDD);
    mpfr_div_ui(u_hi, u_hi, 2 * d, MPFR_RNDU);

    mpfr_set_ui(term_lo, 1, MPFR_RNDN);
    mpfr_set_ui(term_hi, 1, MPFR_RNDN);
    mpfr_set_ui(even_lo, 1, MPFR_RNDN);
    mpfr_set_ui(even_hi, 1, MPFR_RNDN);
    mpfr_set_zero(odd_lo, 1);
    mpfr_set_zero(odd_hi, 1);

    unsigned long certified_at = 0;
    for (unsigned long m = 1; m <= TERM_LIMIT; ++m) {
        mpfr_div_ui(ratio_lo, u_lo, m, MPFR_RNDD);
        mpfr_div_ui(ratio_hi, u_hi, m, MPFR_RNDU);
        mpfr_pow_ui(ratio_lo, ratio_lo, d, MPFR_RNDD);
        mpfr_pow_ui(ratio_hi, ratio_hi, d, MPFR_RNDU);
        mpfr_mul(term_lo, term_lo, ratio_lo, MPFR_RNDD);
        mpfr_mul(term_hi, term_hi, ratio_hi, MPFR_RNDU);

        if (m % 2 == 0) {
            mpfr_add(even_lo, even_lo, term_lo, MPFR_RNDD);
            mpfr_add(even_hi, even_hi, term_hi, MPFR_RNDU);
        } else {
            mpfr_add(odd_lo, odd_lo, term_lo, MPFR_RNDD);
            mpfr_add(odd_hi, odd_hi, term_hi, MPFR_RNDU);
        }

        /* If m >= U, the alternating remainder has sign (-1)^(m+1). */
        if (m % 2 == k % 2 || mpfr_cmp_ui(u_hi, m) > 0) {
            continue;
        }
        if (k % 2 == 0) {
            mpfr_sub(signed_lo, even_lo, odd_hi, MPFR_RNDD);
        } else {
            mpfr_sub(signed_lo, odd_lo, even_hi, MPFR_RNDD);
        }
        if (mpfr_number_p(signed_lo) && mpfr_sgn(signed_lo) > 0) {
            certified_at = m;
            break;
        }
    }

    if (mpfr_nanflag_p() || mpfr_overflow_p() || mpfr_underflow_p()
        || mpfr_divby0_p() || mpfr_erangeflag_p()) {
        fprintf(stderr, "MPFR exception for d=%lu k=%lu\n", d, k);
        certified_at = 0;
    }
    mpfr_clears(x_lo, x_hi, u_lo, u_hi, ratio_lo, ratio_hi, term_lo,
                term_hi, even_lo, even_hi, odd_lo, odd_hi, signed_lo,
                (mpfr_ptr) 0);
    return certified_at;
}

static unsigned long check_range(unsigned long first_d, unsigned long last_d)
{
    unsigned long count = 0, max_m = 0, max_d = 0, max_k = 0;
    for (unsigned long d = first_d; d <= last_d; ++d) {
        unsigned long k_limit = d <= 7 ? 100 * d : 128;
        for (unsigned long k = d / 4 + 1; k < k_limit; ++k) {
            unsigned long m = certify_sign(d, k);
            if (m == 0) {
                fprintf(stderr, "Uncertified sign for d=%lu k=%lu\n", d, k);
                exit(EXIT_FAILURE);
            }
            ++count;
            if (m > max_m) {
                max_m = m;
                max_d = d;
                max_k = k;
            }
        }
    }
    printf("d=%lu..%lu: %lu certified cases; maximum final term index %lu at d=%lu k=%lu\n",
           first_d, last_d, count, max_m, max_d, max_k);
    return count;
}

int main(void)
{
    printf("MPFR %s, GMP %s, %d bits\n", mpfr_get_version(), gmp_version, PRECISION);
    unsigned long count = check_range(3, 7);
    count += check_range(8, 127);
    printf("Total: %lu signs certified\n", count);
    return EXIT_SUCCESS;
}
