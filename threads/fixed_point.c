#include "threads/fixed_point.h"
#include <stdint.h>

int f = 16384;
int f_div_2 = 8192;

int int_to_fixed_p(int n) {
    return (n * f);
}

int fixed_p_to_int_down(int x) {
    return (x / f);
}

int fixed_p_to_int_nearest(int x) {
    if (x >= 0) return ((x + f_div_2) / f);
    else return ((x - f_div_2) / f);
}

int fixed_p_add_fixed_p(int x, int y) {
    return (x + y);
}

int fixed_p_sub_fixed_p(int x, int y) {
    return (x - y);
}

int fixed_p_add_int(int x, int n) {
    return (x + n * f);
}

int fixed_p_sub_int(int x, int n) {
    return (x - n * f);
}

int fixed_p_mul_fixed_p(int x, int y) {
    return (int)(((int64_t) x) * y / f);
}

int fixed_p_mul_int(int x, int n) {
    return (x * n);
}

int fixed_p_div_fixed_p(int x, int y) {
    return (int)(((int64_t) x) * f / y);
}

int fixed_p_div_int(int x, int n) {
    return (x / n);
}