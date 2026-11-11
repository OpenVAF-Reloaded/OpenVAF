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

/* Uniformly distributed integer.
 * i is 64-bit, as 'long' is in the IEEE 1364-2005 reference on LP64
 * (Icarus on 64-bit Linux/macOS). Before the clamps r can exceed
 * INT32_MAX by up to ~512, and converting that to a 32-bit type is
 * undefined behaviour (x86 gives INT32_MIN, ARM saturates). The result
 * is truncated to 32 bits, as when it is stored in a Verilog integer.
 */
static int32_t rtl_dist_uniform(int32_t *seed, int32_t start, int32_t end) {
      double r;
      int64_t i, s, e;

      if (start >= end) return start;

      if (end != INT32_MAX) {
            e = (int64_t)end + 1;
            r = uniform(seed, start, (int32_t)e);
            if (r >= 0) {
                  i = (int64_t) r;
            } else {
                  i = (int64_t) (r - 1);
            }
            if (i < start) i = start;
            if (i >= e) i = e - 1;
      } else if (start != INT32_MIN) {
            s = (int64_t)start - 1;
            r = uniform(seed, (int32_t)s, end) + 1.0;
            if (r >= 0) {
                  i = (int64_t) r;
            } else {
                  i = (int64_t) (r - 1);
            }
            if (i <= s) i = s + 1;
            if (i > end) i = end;
      } else {
            r = (uniform(seed, start, end) + 2147483648.0) / 4294967295.0;
            r = r * 4294967296.0 - 2147483648.0;

            if (r >= 0) {
                  i = (int64_t) r;
            } else {
                  i = (int64_t) (r - 1);
            }
      }

      return (int32_t)(uint32_t)(uint64_t)i;   /* keep low 32 bits */
}

// $random/$arandom
static int32_t rtl_dist_random(int32_t *seed) {
    return rtl_dist_uniform(seed, INT32_MIN, INT32_MAX);
}

// Incompatible, but better generators (used for now)
// ==================================================

// Core generator
static int32_t random_alt(int32_t *seed) {
    uint32_t s = (uint32_t)*seed;
    // if (s == 0) s = 259341593;       // same substitution as uniform() in IEEE 1364-2005, so a shared
                                        // seed variable gives the same state sequence
                                        // no substitution needed because vams_fmix() mixes bits.
    s = 69069u * s + 1u;
    *seed = (int32_t)s;
    return (int32_t)vams_fmix32(s);     // full 32 bits, all bits well mixed
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

// MIR has no pointers. A generator gen(int32_t *seed, ...) is split into two
// pure functions of the old seed, called by the compiled code:
//   prefix_next(seed, ...)   the new seed
//   prefix_value(seed, ...)  the generated value
// params are the declarations of the arguments after the seed, args their
// names. Both lists start with a comma, () if there are none, e.g.
//   VAMS_RANDOM_PAIR(vams_uniform, int32_t, rtl_dist_uniform_alt,
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

// IEEE 1364-2005 generator wrappers
// $random/$arandom
VAMS_RANDOM_PAIR(vams_random_ieee, int32_t, rtl_dist_random, (), ())

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
