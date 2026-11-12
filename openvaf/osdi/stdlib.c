#ifdef NO_STD
// This was used before. Seems wrong. AB
// typedef int int32_t;
// Maybe this is better... AB
typedef unsigned int uint32_t;
typedef int int32_t;
// End of change AB
typedef long long int64_t;
typedef unsigned long long uint64_t;
#define INT32_MAX 2147483647
#define INT32_MIN (-INT32_MAX - 1)
#define UINT32_MAX 4294967295u
typedef unsigned char bool;
typedef __SIZE_TYPE__ size_t;
extern size_t strlen (const char *__s);
extern void *memcpy (void *__restrict __dest, const void *__restrict __src,
		     size_t __n);
extern void *malloc (size_t __size);
extern void *realloc (void *__ptr, size_t __size);
extern double log(double);
extern double sqrt(double);
extern double round(double);
extern double exp(double);
extern double expm1(double);
extern double fabs(double);
extern double floor(double);
extern double lgamma(double);
extern int strcmp(const char*, const char*);
#define NULL ((void*)0)
#else
#include <math.h>
#include <stdio.h>
#include "stdlib.h"
#include "string.h"
#endif

#ifndef OSDI_0_5
#include "header/osdi_0_5.h"
#endif

// no header was included explicitly so just use the newest version
#ifndef OSDI_VERSION_MAJOR_CURR
#include "header/osdi_0_5.h"
#endif


char *concat(const char *s1, const char *s2) {
  const size_t len1 = strlen(s1);
  const size_t len2 = strlen(s2);
  char *result = malloc(len1 + len2 + 1);
  if (result == NULL) {
    return NULL;
  }
  memcpy(result, s1, len1);
  memcpy(result + len1, s2, len2 + 1);
  return result;
}

typedef void (*osdi_log_ptr)(void *handle, char *msg, uint32_t lvl);
extern osdi_log_ptr osdi_log;

#define SCMP(p1, p2, s1, s2, eq) for(p1=s1, p2=s2;*p1 && *p2 && *p1==*p2;p1++, p2++); eq = (*p1==*p2);

double simparam(void *params_, void *handle, uint32_t *flags, char *name) {
  OsdiSimParas *params = params_;
  for (int i = 0; params->names[i]; i++) {
    char *p1, *p2;
    int eq;
    SCMP(p1, p2, params->names[i], name, eq);
    // if (strcmp(params->names[i], name) == 0) {
    if (eq) {
      return params->vals[i];
    }
  }
  *flags |= EVAL_RET_FLAG_FATAL;
  char *msg = concat("unknown $simparam", name);
  if (msg == NULL) {
    osdi_log(handle, "unknown $simparam %s", LOG_LVL_FATAL | LOG_FMT_ERR);
  } else {
    osdi_log(handle, msg, LOG_LVL_FATAL);
  }
  return 0.0;
}

double simparam_opt(void *params_, char *name, double default_val) {
  OsdiSimParas *params = params_;
  for (int i = 0; params->names[i]; i++) {
    char *p1, *p2;
    int eq;
    SCMP(p1, p2, params->names[i], name, eq);
    // if (strcmp(params->names[i], name) == 0) {
    if (eq) {
      return params->vals[i];
    }
  }
  return default_val;
}

extern int strcmp(const char *__s1, const char *__s2);

char *simparam_str(void *params_, void *handle, uint32_t *flags, char *name) {
  OsdiSimParas *params = params_;
  for (int i = 0; params->names[i]; i++) {
    char *p1, *p2;
    int eq;
    SCMP(p1, p2, params->names_str[i], name, eq);
    // if (strcmp(params->names_str[i], name) == 0) {
    if (eq) {
      return params->names_str[i];
    }
  }
  *flags |= EVAL_RET_FLAG_FATAL;

  char *msg = concat("unknown $simparam_str", name);
  if (msg == NULL) {
    osdi_log(handle, "unknown $simparam_str %s", LOG_LVL_FATAL | LOG_FMT_ERR);
  } else {
    osdi_log(handle, msg, LOG_LVL_FATAL);
  }

  return "�";
}

void push_error(OsdiInitError **dst, uint32_t *len, uint32_t *cap,
                OsdiInitError err) {
  if (*dst == NULL) {
    *cap = 8;
    *dst = malloc(8 * sizeof(OsdiInitError));
  } else if (*cap <= *len) {
    *cap = 2 * (*len);
    *dst = realloc(*dst, *cap * sizeof(OsdiInitError));
  }

  (*dst)[*len] = err;
  *len += 1;
}

void push_invalid_param_err(void **dst, uint32_t *len, uint32_t *cap,
                            uint32_t param) {
  OsdiInitError err = (OsdiInitError){
      .code = INIT_ERR_OUT_OF_BOUNDS,
      .payload =
          (OsdiInitErrorPayload){
              .parameter_id = param,
          },
  };

  push_error((OsdiInitError **)dst, len, cap, err);
}

void bound_step(double *dst, double val) { *dst = val; }

// Random number generation ($random, $arandom)

// MurmurHash3 finalizer
static uint32_t vams_fmix32(uint32_t h) {
  h ^= h >> 16;
  h *= 0x85ebca6bu;
  h ^= h >> 13;
  h *= 0xc2b2ae35u;
  h ^= h >> 16;
  return h;
}

// 0x9e3779b9 = 2^32/golden ratio
uint32_t vams_mix32(uint32_t base, uint32_t site_id) {
  return vams_fmix32(base ^ vams_fmix32(site_id + 0x9e3779b9u));
}

// IEEE 1364-2005 compatible generators
// ====================================

// Core generator
static double uniform(int32_t *seed, int32_t start, int32_t end) {
      double d = 0.00000011920928955078125;
      double a, b, c;
      uint32_t oldseed, newseed;

      oldseed = (uint32_t)*seed;
      if (oldseed == 0)
            oldseed = 259341593u;

      if (start >= end) {
            a = 0.0;
            b = 2147483647.0;
      } else {
            a = (double)start;
            b = (double)end;
      }

      /* Original routine used signed arithmetic, and the (frequent)
       * overflows trigger "Undefined Behavior" according to the
       * C standard (both c89 and c99).  Using unsigned arithmetic
       * forces a conforming C implementation to get the result
       * that the IEEE-1364-2001 committee wants.
       */
      newseed = 69069u * oldseed + 1u;

      *seed = (int32_t)newseed;

#if 0
      /* Cadence-donated conversion from unsigned int to double */
      {
            union { float s; unsigned stemp; } u;
            u.stemp = (newseed >> 9) | 0x3f800000;
            c = (double) u.s;
      }
#else
      /* Equivalent conversion without assuming IEEE 32-bit float */
      /* constant is 2^(-23) */
      c = 1.0 + (newseed >> 9) * 0.00000011920928955078125;
#endif

      c = c + (c*d);
      c = ((b - a) * (c - 1.0)) + a;

      return c;
}

static int32_t rtl_dist_uniform(int32_t *seed, int32_t start, int32_t end) {
      double r;
      int32_t i;

      if (start >= end) return start;

      if (end != INT32_MAX) {
            end++;
            r = uniform(seed, start, end);
            if (r >= 0) {
                  i = (int32_t) r;
            } else {
                  i = (int32_t) (r - 1);
            }
            if (i < start) i = start;
            if (i >= end) i = end - 1;
      } else if (start != INT32_MIN) {
            start--;
            r = uniform(seed, start, end) + 1.0;
            if (r >= 0) {
                  i = (int32_t) r;
            } else {
                  i = (int32_t) (r - 1);
            }
            if (i <= start) i = start + 1;
            if (i > end) i = end;
      } else {
            r = (uniform(seed, start, end) + 2147483648.0) / 4294967295.0;
            r = r * 4294967296.0 - 2147483648.0;

            if (r >= 0) {
                  i = (int32_t) r;
            } else {
                  i = (int32_t) (r - 1);
            }
      }

      return i;
}

static double normal(int32_t* seed, int32_t mean, int32_t deviation) {
    double v1,v2,s;
    s = 1.0;
    while((s >= 1.0) || (s == 0.0)) {
        v1 = uniform(seed,-1,1);
        v2 = uniform(seed,-1,1);
        s = v1 * v1 + v2 * v2;
    }
    s = v1 * sqrt(-2.0 * log(s) / s);
    v1 = (double) deviation;
    v2 = (double) mean;
    return(s * v1 + v2);
}

static double exponential(int32_t *seed, int32_t mean) {
      double n;

      n = uniform(seed, 0, 1);
      if (n != 0.0) {
            n = -log(n) * mean;
      }

      return n;
}

static int32_t poisson(int32_t *seed, int32_t mean) {
      int32_t n;
      double p, q;

      n = 0;
      q = -(double) mean;
      p = exp(q);
      q = uniform(seed, 0, 1);
      while (p < q) {
            n++;
            q = uniform(seed, 0, 1) * q;
      }

      return n;
}

static double chi_square(int32_t *seed, int32_t deg_of_free) {
      double x;
      int32_t k;

      if (deg_of_free % 2) {
            x = normal(seed, 0, 1);
            x = x * x;
      } else {
            x = 0.0;
      }
      for (k = 2; k <= deg_of_free; k = k + 2) {
            x = x + 2 * exponential(seed, 1);
      }

      return x;
}

static double t( int32_t *seed, int32_t deg_of_free) {
      double x, chi2, dv, root;

      chi2 = chi_square(seed, deg_of_free);
      dv = chi2 / (double) deg_of_free;
      root = sqrt(dv);
      x = normal(seed, 0, 1) / root;

      return x;
}

static double erlangian(int32_t *seed, int32_t k, int32_t mean) {
      double x, a, b;
      int32_t i;

      x = 1.0;
      for (i = 1; i <= k; i++) {
            x = x * uniform(seed, 0, 1);
      }
      a = (double) mean;
      b = (double) k;
      x = -a * log(x) / b;

      return x;
}

// $random/$arandom
static int32_t rtl_dist_random(int32_t *seed) {
    return rtl_dist_uniform(seed, INT32_MIN, INT32_MAX);
}

// Normally distributed integer
static int32_t rtl_dist_normal(int32_t* seed, int32_t mean, int32_t sd) {
    double r;
    int32_t i;
    r=normal(seed,mean,sd);
    if(r>=0) {
        i=(int32_t)(r+0.5);
    } else {
        r = -r;
        i=(int32_t)(r+0.5);
        i = -i;
    }
    return (i);
}

// Exponentially distributed integer ($dist_exponential)
static int32_t rtl_dist_exponential(int32_t *seed, int32_t mean) {
      double r;
      int32_t i;

      if (mean > 0) {
            r = exponential(seed, mean);
            if (r >= 0) {
                  i = (int32_t) (r + 0.5);
            } else {
                  r = -r;
                  i = (int32_t) (r + 0.5);
                  i = -i;
            }
      } else {
            // WARNING: Exponential distribution must have a positive mean
            i = 0;
      }

      return i;
}

// Poisson distributed integer ($dist_poisson)
static int32_t rtl_dist_poisson(int32_t *seed, int32_t mean) {
      int32_t i;

      if (mean > 0) {
            i = poisson(seed, mean);
      } else {
            // WARNING: Poisson distribution must have a positive mean
            i = 0;
      }

      return i;
}

// Chi square distributed integer ($dist_chi_square)
static int32_t rtl_dist_chi_square(int32_t *seed, int32_t df) {
      double r;
      int32_t i;

      if (df > 0) {
            r = chi_square(seed, df);
            if (r >= 0) {
                  i = (int32_t) (r + 0.5);
            } else {
                  r = -r;
                  i = (int32_t) (r + 0.5);
                  i = -i;
            }
      } else {
            // WARNING: Chi_square distribution must have positive degree of freedom
            i = 0;
      }

      return i;
}

// t distributed integer ($dist_t)
static int32_t rtl_dist_t(int32_t *seed, int32_t df) {
      double r;
      int32_t i;

      if (df > 0) {
            r = t(seed, df);
            if (r >= 0) {
                  i = (int32_t) (r + 0.5);
            } else {
                  r = -r;
                  i = (int32_t) (r + 0.5);
                  i = -i;
            }
      } else {
            // WARNING: t distribution must have positive degree of freedom
            i = 0;
      }

      return i;
}

// Erlangian distributed integer ($dist_erlang)
static int32_t rtl_dist_erlang(int32_t *seed, int32_t k, int32_t mean) {
      double r;
      int32_t i;

      if (k > 0) {
            r = erlangian(seed, k, mean);
            if (r >= 0) {
                  i = (int32_t) (r + 0.5);
            } else {
                  r = -r;
                  i = (int32_t) (r + 0.5);
                  i = -i;
            }
      } else {
            // WARNING: k-stage erlangian distribution must have positive k
            i = 0;
      }

      return i;
}

// Incompatible, but better generators (used for now)
// ==================================================

// Core generator
static int32_t random_alt(int32_t *seed) {
    uint32_t s = (uint32_t)*seed;
    // if (s == 0) s = 259341593;       // same substitution as uniform() in IEEE 1364-2005, so a shared
                                        // seed variable gives the same state sequence
                                        // no substitution needed because vams_fmix32() mixes bits.
    s = 69069u * s + 1u;
    *seed = (int32_t)s;
    return (int32_t)vams_fmix32(s);     // full 32 bits, all bits well mixed
}

static double uniform_alt(int32_t *seed, double a, double b) {
    double u = ((double)(uint32_t)random_alt(seed) + 0.5) * 0x1p-32;   /* (0,1) */
    return a * (1.0 - u) + b * u;
}

static double normal_alt(int32_t* seed, double mean, double deviation) {
    double v1,v2,s;
    s = 1.0;
    while((s >= 1.0) || (s == 0.0)) {
        v1 = uniform_alt(seed,-1,1);
        v2 = uniform_alt(seed,-1,1);
        s = v1 * v1 + v2 * v2;
    }
    s = v1 * sqrt(-2.0 * log(s) / s);
    v1 = (double) deviation;
    v2 = (double) mean;
    return(s * v1 + v2);
}

static double exponential_alt(int32_t *seed, double mean) {
    double n;

    n = uniform_alt(seed, 0, 1);
    if (n != 0.0) { // can never happen, uniform_alt() never returns 0, 1
          n = -log(n) * mean;
    }

    return n;
}

/* Poisson(mean), mean > 0. Saturates at INT32_MAX.
 * mean < 10:  inversion by sequential search, exactly 1 draw, O(mean) arithmetic.
 * mean >= 10: PTRS, transformed rejection with squeeze (W. Hörmann, "The transformed
 *             rejection method for generating Poisson random variables", Insurance:
 *             Mathematics and Economics 12, 1993). 2 draws per try, acceptance ~0.9 or
 *             better, O(1) expected for any mean. Same algorithm and constants as numpy.
 * The IEEE multiplicative method needs mean+1 draws on average and breaks for mean > ~745
 * (exp(-mean) underflows to 0, so the result gets stuck near 744).
 * Note: lgamma() writes the global signgam. Use lgamma_r() if eval runs multithreaded. */
static int32_t poisson_alt(int32_t *seed, double mean) {
    if (mean < 10.0) {
        double u = uniform_alt(seed, 0, 1);
        double p = exp(-mean), F = p;
        int32_t k = 0;
        while (u > F && p > 0.0) {      /* p > 0: stop if F stalls below u by rounding */
            k++;
            p *= mean / k;
            F += p;
        }
        return k;
    }
    double slam = sqrt(mean), loglam = log(mean);
    double b = 0.931 + 2.53 * slam;
    double a = -0.059 + 0.02483 * b;
    double invalpha = 1.1239 + 1.1328 / (b - 3.4);
    double vr = 0.9277 - 3.6224 / (b - 2.0);
    for (;;) {
        double U = uniform_alt(seed, 0, 1) - 0.5;   /* never 0: u is never exactly 0.5 */
        double V = uniform_alt(seed, 0, 1);
        double us = 0.5 - fabs(U);                  /* >= 2^-33, no division by 0 */
        double k = floor((2.0 * a / us + b) * U + mean + 0.43);
        if (us >= 0.07 && V <= vr)                  /* squeeze: ~86% of tries */
            return k >= 2147483647.0 ? INT32_MAX : (int32_t)k;
        if (k < 0.0 || (us < 0.013 && V > us))
            continue;
        if (log(V) + log(invalpha) - log(a / (us * us) + b)
                <= -mean + k * loglam - lgamma(k + 1.0))
            return k >= 2147483647.0 ? INT32_MAX : (int32_t)k;
    }
}

/* Gamma(shape, 1), shape >= 1. Marsaglia & Tsang, "A simple method for generating gamma
 * variables", ACM TOMS 26(3), 2000. Per try: 1 normal + 1 uniform, acceptance >= 0.95
 * (-> 1 as shape grows), O(1) for any shape. The squeeze avoids log() in ~98% of tries.
 * (For shape < 1, use gamma_alt(shape+1) * pow(u, 1/shape). That case is not needed here.) */
static double gamma_alt(int32_t *seed, double shape) {
    double d = shape - 1.0 / 3.0, c = 1.0 / sqrt(9.0 * d);
    for (;;) {
        double x, v;
        do {
            x = normal_alt(seed, 0, 1);
            v = 1.0 + c * x;
        } while (v <= 0.0);
        v = v * v * v;
        double u = uniform_alt(seed, 0, 1);
        double x2 = x * x;
        if (u < 1.0 - 0.0331 * x2 * x2)                         /* squeeze */
            return d * v;
        if (log(u) < 0.5 * x2 + d * (1.0 - v + log(v)))
            return d * v;
    }
}

/* Chi-square(df), df > 0. chi2(df) = 2*Gamma(df/2, 1), O(1) for any df.
 * df == 1 uses z^2 directly: it is exact, cheaper, and avoids Gamma shape < 1.
 * The IEEE version sums df/2 exponentials (+ one z^2), which is O(df) draws. */
static double chi_square_alt(int32_t *seed, int32_t deg_of_free) {
    if (deg_of_free == 1) {
        double z = normal_alt(seed, 0, 1);
        return z * z;
    }
    return 2.0 * gamma_alt(seed, 0.5 * (double)deg_of_free);
}

/* Student t(df), df > 0. Bailey's polar method (R. W. Bailey, "Polar generation of random
 * variates with the t-distribution", Math. Comp. 62(206), 1994): exact for any df.
 * Per try: 2 uniforms, acceptance pi/4. The IEEE route normal/sqrt(chi2/df) costs O(df) draws.
 * W^(-2/df) - 1 is computed as expm1(-2 log(W)/df) to avoid cancellation for large df.
 * U != 0 (2u-1 has an odd numerator), so W > 0 and log(W) is finite. */
static double t_alt(int32_t *seed, int32_t deg_of_free) {
    double n = (double)deg_of_free, U, V, W;
    do {
        U = uniform_alt(seed, -1, 1);
        V = uniform_alt(seed, -1, 1);
        W = U * U + V * V;
    } while (W >= 1.0);
    return U * sqrt(n * expm1(-2.0 * log(W) / n) / W);
}

/* Erlang(k, mean) = Gamma(k, 1) * mean / k, k > 0. Result has the given mean (as IEEE).
 * k <= 3:  product of k uniforms, 1 log (exact, cheaper than gamma_alt for tiny k;
 *          no underflow since each u >= 2^-33).
 * k > 3:   gamma_alt, O(1). The IEEE version multiplies k uniforms, which is O(k) draws
 *          and underflows to 0 for k > ~1000 (log(0) = -inf, result +inf * mean). */
static double erlang_alt(int32_t *seed, int32_t k, double mean) {
    double g;
    if (k <= 3) {
        double x = uniform_alt(seed, 0, 1);
        for (int32_t i = 1; i < k; i++)
            x *= uniform_alt(seed, 0, 1);
        g = -log(x);
    } else {
        g = gamma_alt(seed, (double)k);
    }
    return g * mean / (double)k;
}

// Uniformly distributed integer
static int32_t rtl_dist_uniform_alt(int32_t *seed, int32_t lo, int32_t hi) {
    if (lo >= hi) return lo;
    uint32_t span = (uint32_t)hi - (uint32_t)lo;
    if (span == UINT32_MAX) return random_alt(seed);
    uint32_t n = span + 1u, thresh = (0u - n) % n;
    uint64_t m;
    do m = (uint64_t)(uint32_t)random_alt(seed) * n; while ((uint32_t)m < thresh);
    return (int32_t)((uint32_t)lo + (uint32_t)(m >> 32));
}

// Normally distributed integer
static int32_t rtl_dist_normal_alt(int32_t* seed, int32_t mean, int32_t sd) {
    /* Round in double (half away from zero, as the IEEE code), saturate,
     * then convert. Converting an out-of-range double to int32_t is UB. */
    double d = round(normal_alt(seed, (double)mean, (double)sd));
    if (d >= 2147483647.0)  return INT32_MAX;
    if (d <= -2147483648.0) return INT32_MIN;
    return (int32_t)d;
}

// Exponentially distributed integer ($dist_exponential)
int32_t rtl_dist_exponential_alt(int32_t *seed, int32_t mean) {
    /* mean > 0 => r in (0, 22.87*mean]; r < 0 is impossible because u is in (0,1).
     * Round half away from zero (same as the IEEE (r+0.5) for r >= 0), saturate,
     * then convert. Overflow is possible for mean > ~9.39e7. */
    if (mean <= 0) return 0;
    double d = round(exponential_alt(seed, (double)mean));
    if (d >= 2147483647.0) return INT32_MAX;
    return (int32_t)d;
}

// Poisson distributed integer ($dist_poisson)
int32_t rtl_dist_poisson_alt(int32_t *seed, int32_t mean) {
    /* As IEEE: mean <= 0 returns 0 and does not advance the seed. */
    if (mean <= 0) return 0;
    return poisson_alt(seed, (double)mean);
}

// Chi square distributed integer ($dist_chi_square)
int32_t rtl_dist_chi_square_alt(int32_t *seed, int32_t df) {
    /* As IEEE: df <= 0 returns 0 and does not advance the seed.
     * Round half away from zero, saturate (overflow possible for df near INT32_MAX). */
    if (df <= 0) return 0;
    double d = round(chi_square_alt(seed, df));
    if (d >= 2147483647.0) return INT32_MAX;
    return (int32_t)d;
}

// t distributed integer ($dist_t)
int32_t rtl_dist_t_alt(int32_t *seed, int32_t df) {
    /* As IEEE: df <= 0 returns 0 and does not advance the seed.
     * Round half away from zero, saturate both ways (heavy tails: df = 1 is Cauchy). */
    if (df <= 0) return 0;
    double d = round(t_alt(seed, df));
    if (d >= 2147483647.0)  return INT32_MAX;
    if (d <= -2147483648.0) return INT32_MIN;
    return (int32_t)d;
}

// Erlangian distributed integer ($dist_erlang)
int32_t rtl_dist_erlang_alt(int32_t *seed, int32_t k, int32_t mean) {
    /* As IEEE: k <= 0 returns 0 and does not advance the seed. mean is not checked
     * (mean < 0 gives values <= 0, mean == 0 gives 0, as IEEE).
     * Round half away from zero, saturate both ways. */
    if (k <= 0) return 0;
    double d = round(erlang_alt(seed, k, (double)mean));
    if (d >= 2147483647.0)  return INT32_MAX;
    if (d <= -2147483648.0) return INT32_MIN;
    return (int32_t)d;
}

// MIR has no pointers. A generator gen(int32_t *seed, ...) is split into two
// pure functions of the old seed, called by the compiled code:
//   prefix_next(seed, ...)   the new seed
//   prefix_value(seed, ...)  the generated value
// params are the declarations of the arguments after the seed, args their
// names. Both lists start with a comma, () if there are none, e.g.
//   VAMS_RANDOM_PAIR(vams_uniform_int, int32_t, rtl_dist_uniform_alt,
//                    (, int32_t lo, int32_t hi), (, lo, hi))
#define VAMS_UNPAREN(...) __VA_ARGS__
#define VAMS_RANDOM_PAIR(prefix, ret_t, gen, params, args)                     \
  int32_t prefix##_next(int32_t seed VAMS_UNPAREN params) {                    \
    gen(&seed VAMS_UNPAREN args);                                              \
    return seed;                                                               \
  }                                                                            \
  ret_t prefix##_value(int32_t seed VAMS_UNPAREN params) {                     \
    return gen(&seed VAMS_UNPAREN args);                                       \
  }

// Alternative generator wrappers
// $random/$arandom
VAMS_RANDOM_PAIR(vams_random, int32_t, random_alt, (), ())
// Uniformly distributed integer on [lo, hi]
VAMS_RANDOM_PAIR(vams_uniform_int, int32_t, rtl_dist_uniform_alt,
                 (, int32_t lo, int32_t hi), (, lo, hi))
// Normally distributed integer
VAMS_RANDOM_PAIR(vams_normal_int, int32_t, rtl_dist_normal_alt,
                 (, int32_t mean, int32_t sd), (, mean, sd))
// Exponentially distributed integer
VAMS_RANDOM_PAIR(vams_exponential_int, int32_t, rtl_dist_exponential_alt,
                 (, int32_t mean), (, mean))
// Poisson distributed integer
VAMS_RANDOM_PAIR(vams_poisson_int, int32_t, rtl_dist_poisson_alt,
                 (, int32_t mean), (, mean))
// Chi square distributed integer
VAMS_RANDOM_PAIR(vams_chi_square_int, int32_t, rtl_dist_chi_square_alt,
                 (, int32_t df), (, df))
// t distributed integer
VAMS_RANDOM_PAIR(vams_t_int, int32_t, rtl_dist_t_alt, (, int32_t df), (, df))
// Erlangian distributed integer
VAMS_RANDOM_PAIR(vams_erlang_int, int32_t, rtl_dist_erlang_alt,
                 (, int32_t k, int32_t mean), (, k, mean))

// IEEE 1364-2005 generator wrappers
// $random/$arandom
VAMS_RANDOM_PAIR(vams_random_ieee, int32_t, rtl_dist_random, (), ())
// Uniformly distributed integer on [start, end]
VAMS_RANDOM_PAIR(vams_uniform_int_ieee, int32_t, rtl_dist_uniform,
                 (, int32_t start, int32_t end), (, start, end))
// Normally distributed integer
VAMS_RANDOM_PAIR(vams_normal_int_ieee, int32_t, rtl_dist_normal,
                 (, int32_t mean, int32_t sd), (, mean, sd))
// Exponentially distributed integer
VAMS_RANDOM_PAIR(vams_exponential_int_ieee, int32_t, rtl_dist_exponential,
                 (, int32_t mean), (, mean))
// Poisson distributed integer
VAMS_RANDOM_PAIR(vams_poisson_int_ieee, int32_t, rtl_dist_poisson,
                 (, int32_t mean), (, mean))
// Chi square distributed integer
VAMS_RANDOM_PAIR(vams_chi_square_int_ieee, int32_t, rtl_dist_chi_square,
                 (, int32_t df), (, df))
// t distributed integer
VAMS_RANDOM_PAIR(vams_t_int_ieee, int32_t, rtl_dist_t, (, int32_t df), (, df))
// Erlangian distributed integer
VAMS_RANDOM_PAIR(vams_erlang_int_ieee, int32_t, rtl_dist_erlang,
                 (, int32_t k, int32_t mean), (, k, mean))

// Initial state of the random number generator with site id site_id that is
// seeded by the simulator. Reads entity_seed only if INIT_HIDDEN_STATE is set
// (older simulators pass a shorter OsdiInitInfo).
int32_t vams_site_seed(OsdiInitInfo *info, uint32_t site_id) {
  if (!(info->flags & INIT_HIDDEN_STATE))
    return 0;
  return (int32_t)vams_mix32(info->entity_seed, site_id);
}

#define FMT_OFF 6
#define NUM_FMT 11
const char FMT_CHARS[NUM_FMT] = {'a', 'f', 'p', 'n', 'u', 'm',
                                 ' ', 'k', 'M', 'G', 'T'};
const double EXP[NUM_FMT] = {1e18, 1e15, 1e12, 1e9,  1e6,  1e3,
                             1,    1e-3, 1e-6, 1e-9, 1e-12};
int fmt_char_idx(double val) {
  int exp = ((int)log(val)) / 3;
  int pos = exp + NUM_FMT;

  if (pos < 0) {
    return 0;
  }
  if (pos >= NUM_FMT) {
    return NUM_FMT - 1;
  }
  return pos;
}

char *fmt_binary(int val) {
  int len = 32 - __builtin_clz(val);
  char *res = malloc(len + 1);
  res[len] = '\0';
  if (len == 0) {
    return res;
  }
  for (int i = 1; i < len + 1; i++) {
    if (val & 1) {
      res[len - i] = '1';
    } else {
      res[len - i] = '0';
    }
    val >>= 1;
  }

  return res;
}

// $discontinuity(degree): -1 inside a $limit function sets the limiting flag,
// other negative degrees are ignored, a nonnegative degree updates the slot
// (smallest nonnegative degree, -1 if none). slot is NULL if the module has none.
void discontinuity(int *flags, int *slot, int in_limit, int degree) {
  if (degree < 0) {
    if (degree == -1 && in_limit) {
      *flags |= EVAL_RET_FLAG_LIM;
    }
  } else if (slot && (*slot < 0 || degree < *slot)) {
    *slot = degree;
  }
}

void set_ret_flag_fatal(int *flags) { *flags |= EVAL_RET_FLAG_FATAL; }

void set_ret_flag_finish(int *flags) { *flags |= EVAL_RET_FLAG_FINISH; }

void set_ret_flag_stop(int *flags) { *flags |= EVAL_RET_FLAG_STOP; }

double store_lim(void *sim_info_, int idx, double val) {
  OsdiSimInfo *sim_info = (OsdiSimInfo *)sim_info_;
  sim_info->next_state[idx] = val;
  return val;
}

int analysis(void *sim_info_, char *name) {
  OsdiSimInfo *sim_info = (OsdiSimInfo *)sim_info_;
  uint32_t flags = sim_info->flags;
  // AB: fixed bug, missing ! in front of strcmp()
  return ((flags & ANALYSIS_AC) && !strcmp(name, "ac")) ||
         ((flags & ANALYSIS_DC) && !strcmp(name, "dc")) ||
         ((flags & ANALYSIS_NOISE) && !strcmp(name, "noise")) ||
         ((flags & ANALYSIS_TRAN) && !strcmp(name, "tran")) ||
         ((flags & ANALYSIS_IC) && !strcmp(name, "ic")) ||
         ((flags & ANALYSIS_STATIC) && !strcmp(name, "static")) ||
         ((flags & ANALYSIS_NODESET) && !strcmp(name, "nodeset"));
}

double store_delay(void *sim_info_, double *dst, double val) {
  OsdiSimInfo *sim_info = (OsdiSimInfo *)sim_info_;
  if (sim_info->flags & ANALYSIS_IC) {
    *dst = val;
    return val;
  }

  return *dst;
}
