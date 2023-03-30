#ifndef FIXED_POINT_H
#define FIXED_POINT_H
int int_to_fixed_p(int n);
int fixed_p_to_int(int x);
int fixed_p_to_int_nearest(int x);
int fixed_p_add_fixed_p(int x, int y);
int fixed_p_sub_fixed_p(int x, int y);
int fixed_p_add_int(int x, int n);
int fixed_p_sub_int(int x, int n);
int fixed_p_mul_fixed_p(int x, int y);
int fixed_p_mul_int(int x, int n);
int fixed_p_div_fixed_p(int x, int y);
int fixed_p_div_int(int x, int n);
#endif /* threads/fixed_point.h */