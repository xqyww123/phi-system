#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct {int den; int num; } T1;

T1 rat_add(T1 v0, T1 v1) {
int v2 = v0.num;
int v3 = v1.den;
int v4 = v2 * v3;
int v5 = v1.num;
int v6 = v0.den;
int v7 = v5 * v6;
int v8 = v4 + v7;
int v9 = v0.den;
int v10 = v1.den;
int v11 = v9 * v10;
T1 v12 = {v11,v8};
return v12;
}

T1 rat_div(T1 v0, T1 v1) {
int v2 = v0.num;
int v3 = v1.den;
int v4 = v2 * v3;
int v5 = v0.den;
int v6 = v1.num;
int v7 = v5 * v6;
T1 v8 = {v7,v4};
return v8;
}

T1 rat_mul(T1 v0, T1 v1) {
int v2 = v0.num;
int v3 = v1.num;
int v4 = v2 * v3;
int v5 = v0.den;
int v6 = v1.den;
int v7 = v5 * v6;
T1 v8 = {v7,v4};
return v8;
}

T1 rat_sub(T1 v0, T1 v1) {
int v2 = v0.num;
int v3 = v1.den;
int v4 = v2 * v3;
int v5 = v1.num;
int v6 = v0.den;
int v7 = v5 * v6;
int v8 = v4 - v7;
int v9 = v0.den;
int v10 = v1.den;
int v11 = v9 * v10;
T1 v12 = {v11,v8};
return v12;
}

