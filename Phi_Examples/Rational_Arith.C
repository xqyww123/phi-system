#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {int den; int num; } T__1;

T__1 rat_add(T__1 _v0, T__1 _v1) {
int _v2 = _v0.num;
int _v3 = _v1.den;
int _v4 = _v2 * _v3;
int _v5 = _v1.num;
int _v6 = _v0.den;
int _v7 = _v5 * _v6;
int _v8 = _v4 + _v7;
int _v9 = _v0.den;
int _v10 = _v1.den;
int _v11 = _v9 * _v10;
T__1 _v12 = {_v11,_v8};
return _v12;
}

T__1 rat_sub(T__1 _v0, T__1 _v1) {
int _v2 = _v0.num;
int _v3 = _v1.den;
int _v4 = _v2 * _v3;
int _v5 = _v1.num;
int _v6 = _v0.den;
int _v7 = _v5 * _v6;
int _v8 = _v4 - _v7;
int _v9 = _v0.den;
int _v10 = _v1.den;
int _v11 = _v9 * _v10;
T__1 _v12 = {_v11,_v8};
return _v12;
}

T__1 rat_mul(T__1 _v0, T__1 _v1) {
int _v2 = _v0.num;
int _v3 = _v1.num;
int _v4 = _v2 * _v3;
int _v5 = _v0.den;
int _v6 = _v1.den;
int _v7 = _v5 * _v6;
T__1 _v8 = {_v7,_v4};
return _v8;
}

T__1 rat_div(T__1 _v0, T__1 _v1) {
int _v2 = _v0.num;
int _v3 = _v1.den;
int _v4 = _v2 * _v3;
int _v5 = _v0.den;
int _v6 = _v1.num;
int _v7 = _v5 * _v6;
T__1 _v8 = {_v7,_v4};
return _v8;
}

bool rat_lt(T__1 _v0, T__1 _v1) {
int _v2 = _v0.num;
int _v3 = _v1.den;
int _v4 = _v2 * _v3;
int _v5 = _v0.den;
int _v6 = _v1.num;
int _v7 = _v5 * _v6;
int _v8 = _v0.den;
bool _v9 = 0 < _v8;
int _v10 = _v1.den;
bool _v11 = 0 < _v10;
bool _v12 = _v9 ^ _v11;
bool _v13 = _v7 < _v4;
bool _v14 = _v4 < _v7;
bool _v15 = _v12 ? _v13 : _v14;
return _v15;
}

bool rat_le(T__1 _v0, T__1 _v1) {
int _v2 = _v0.num;
int _v3 = _v1.den;
int _v4 = _v2 * _v3;
int _v5 = _v0.den;
int _v6 = _v1.num;
int _v7 = _v5 * _v6;
int _v8 = _v0.den;
bool _v9 = 0 < _v8;
int _v10 = _v1.den;
bool _v11 = 0 < _v10;
bool _v12 = _v9 ^ _v11;
bool _v13 = _v7 <= _v4;
bool _v14 = _v4 <= _v7;
bool _v15 = _v12 ? _v13 : _v14;
return _v15;
}

bool rat_gt(T__1 _v0, T__1 _v1) {
bool _v2 = rat_lt(_v1,_v0);
return _v2;
}

bool rat_ge(T__1 _v0, T__1 _v1) {
bool _v2 = rat_le(_v1,_v0);
return _v2;
}

