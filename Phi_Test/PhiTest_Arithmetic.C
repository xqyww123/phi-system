#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

bool test_prime(int _v0) {
bool _v1 = _v0 <= 1;
if (_v1) {
return false;
} else {
int _v2;
_v2 = 2;
bool _v3 = _v2 == _v0;
bool _v4 = !_v3;
while (_v4) {
int _v5 = _v0 % _v2;
bool _v6 = _v5 == 0;
if (_v6) {
return false;
} else {
int _v7 = _v2 + 1;
_v2 = _v7;
}
bool _v8 = _v2 == _v0;
bool _v9 = !_v8;
_v4 = _v9;
}
return true;
}
}

bool test_prime2(int _v0) {
bool _v1 = _v0 <= 1;
if (_v1) {
return false;
} else {
int _v2;
_v2 = 2;
int _v3 = _v2 * _v2;
bool _v4 = _v3 <= _v0;
while (_v4) {
int _v5 = _v0 % _v2;
bool _v6 = _v5 == 0;
if (_v6) {
return false;
} else {
int _v7 = _v2 + 1;
_v2 = _v7;
}
int _v8 = _v2 * _v2;
bool _v9 = _v8 <= _v0;
_v4 = _v9;
}
return true;
}
}

int GCD(int _v0, int _v1) {
bool _v2 = _v1 < _v0;
int _v3;
if (_v2) {
int _v4 = GCD(_v1,_v0);
_v3 = _v4;
} else {
int _v5 = _v1 % _v0;
bool _v6 = _v5 == 0;
int _v7;
if (_v6) {
_v7 = _v0;
} else {
int _v8 = GCD(_v5,_v0);
_v7 = _v8;
}
_v3 = _v7;
}
return _v3;
}

int gcd(int _v0, int _v1) {
return GCD(_v0, _v1);
}

