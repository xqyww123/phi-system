#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

int GCD(int v0, int v1) {
int v2 = v1 < v0;
if (v2) {
int v3 = GCD(v1,v0);
return v3;
} {
int v4 = v1 % v0;
bool v5 = v4 == 0;
if (v5) {
return v0;
} {
int v6 = GCD(v4,v0);
return v6;
}
}
}

bool test_prime(int v0) {
int v1 = v0 <= 1;
if (v1) {
return false;
} {
int v2;
v2 = 2;
bool v3 = v2 == v0;
bool v4 = !v3;
while (v4) {
int v5 = v0 % v2;
bool v6 = v5 == 0;
if (v6) {
return false;
} {
int v7 = v2 + 1;
v2 = v7;
}
bool v8 = v2 == v0;
bool v9 = !v8;
v4 = v9;
}
return true;
}
}

bool test_prime2(int v0) {
int v1 = v0 <= 1;
if (v1) {
return false;
} {
int v2;
v2 = 2;
int v3 = v2 * v2;
int v4 = v3 <= v0;
while (v4) {
int v5 = v0 % v2;
bool v6 = v5 == 0;
if (v6) {
return false;
} {
int v7 = v2 + 1;
v2 = v7;
}
int v8 = v2 * v2;
int v9 = v8 <= v0;
v4 = v9;
}
return true;
}
}

