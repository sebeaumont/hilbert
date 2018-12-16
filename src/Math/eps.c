#include "eps.h"

typedef union {
  long long i64;
  double d64;
} dbl_64;

double machine_eps (double value) {
    dbl_64 s;
    s.d64 = value;
    s.i64++;
    return s.d64 - value;
}
