#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned T__7[4];

void zero_mat(void* _v0, uintptr_t _v1, uintptr_t _v2, uintptr_t _v3, uintptr_t _v4) {
uintptr_t _v5;
_v5 = 0;
bool _v6 = (bool)((uintptr_t)_v5 < (uintptr_t)_v3);
while (_v6) {
uintptr_t _v7;
_v7 = 0;
bool _v8 = (bool)((uintptr_t)_v7 < (uintptr_t)_v4);
while (_v8) {
uintptr_t _v9 = (uintptr_t)((uintptr_t)_v1 + (uintptr_t)_v5);
uintptr_t _v10 = (uintptr_t)((uintptr_t)_v2 + (uintptr_t)_v7);
void* _v11 = (void*)&(((T__7*)_v0)[_v9][_v10]);
*(unsigned*)_v11=0;
uintptr_t _v12 = (uintptr_t)((uintptr_t)_v7 + (uintptr_t)1);
_v7 = _v12;
bool _v13 = (bool)((uintptr_t)_v7 < (uintptr_t)_v4);
_v8 = _v13;
}
uintptr_t _v14 = (uintptr_t)((uintptr_t)_v5 + (uintptr_t)1);
_v5 = _v14;
bool _v15 = (bool)((uintptr_t)_v5 < (uintptr_t)_v3);
_v6 = _v15;
}
}

typedef T__7 T__8[4];

void* new_mat() {
void* _v0 = calloc(1, sizeof(T__8));
return _v0;
}

void del_mat(void* _v0) {
free(_v0);
}

void copy_mat(void* _v0, uintptr_t _v1, uintptr_t _v2, void* _v3, uintptr_t _v4, uintptr_t _v5, uintptr_t _v6, uintptr_t _v7) {
uintptr_t _v8;
_v8 = 0;
bool _v9 = (bool)((uintptr_t)_v8 < (uintptr_t)_v6);
while (_v9) {
uintptr_t _v10;
_v10 = 0;
bool _v11 = (bool)((uintptr_t)_v10 < (uintptr_t)_v7);
while (_v11) {
uintptr_t _v12 = (uintptr_t)((uintptr_t)_v1 + (uintptr_t)_v8);
uintptr_t _v13 = (uintptr_t)((uintptr_t)_v2 + (uintptr_t)_v10);
uintptr_t _v14 = (uintptr_t)((uintptr_t)_v4 + (uintptr_t)_v8);
uintptr_t _v15 = (uintptr_t)((uintptr_t)_v5 + (uintptr_t)_v10);
void* _v16 = (void*)&(((T__7*)_v3)[_v14][_v15]);
unsigned _v17 = *(unsigned*)_v16;
void* _v18 = (void*)&(((T__7*)_v0)[_v12][_v13]);
*(unsigned*)_v18=_v17;
uintptr_t _v19 = (uintptr_t)((uintptr_t)_v10 + (uintptr_t)1);
_v10 = _v19;
bool _v20 = (bool)((uintptr_t)_v10 < (uintptr_t)_v7);
_v11 = _v20;
}
uintptr_t _v21 = (uintptr_t)((uintptr_t)_v8 + (uintptr_t)1);
_v8 = _v21;
bool _v22 = (bool)((uintptr_t)_v8 < (uintptr_t)_v6);
_v9 = _v22;
}
}

void add_mat(void* _v0, uintptr_t _v1, uintptr_t _v2, void* _v3, uintptr_t _v4, uintptr_t _v5, uintptr_t _v6, uintptr_t _v7) {
uintptr_t _v8;
_v8 = 0;
bool _v9 = (bool)((uintptr_t)_v8 < (uintptr_t)_v6);
while (_v9) {
uintptr_t _v10;
_v10 = 0;
bool _v11 = (bool)((uintptr_t)_v10 < (uintptr_t)_v7);
while (_v11) {
uintptr_t _v12 = (uintptr_t)((uintptr_t)_v1 + (uintptr_t)_v8);
uintptr_t _v13 = (uintptr_t)((uintptr_t)_v2 + (uintptr_t)_v10);
uintptr_t _v14 = (uintptr_t)((uintptr_t)_v1 + (uintptr_t)_v8);
uintptr_t _v15 = (uintptr_t)((uintptr_t)_v2 + (uintptr_t)_v10);
void* _v16 = (void*)&(((T__7*)_v0)[_v14][_v15]);
unsigned _v17 = *(unsigned*)_v16;
uintptr_t _v18 = (uintptr_t)((uintptr_t)_v4 + (uintptr_t)_v8);
uintptr_t _v19 = (uintptr_t)((uintptr_t)_v5 + (uintptr_t)_v10);
void* _v20 = (void*)&(((T__7*)_v3)[_v18][_v19]);
unsigned _v21 = *(unsigned*)_v20;
unsigned _v22 = (unsigned)((unsigned)_v17 + (unsigned)_v21);
void* _v23 = (void*)&(((T__7*)_v0)[_v12][_v13]);
*(unsigned*)_v23=_v22;
uintptr_t _v24 = (uintptr_t)((uintptr_t)_v10 + (uintptr_t)1);
_v10 = _v24;
bool _v25 = (bool)((uintptr_t)_v10 < (uintptr_t)_v7);
_v11 = _v25;
}
uintptr_t _v26 = (uintptr_t)((uintptr_t)_v8 + (uintptr_t)1);
_v8 = _v26;
bool _v27 = (bool)((uintptr_t)_v8 < (uintptr_t)_v6);
_v9 = _v27;
}
}

void sub_mat(void* _v0, uintptr_t _v1, uintptr_t _v2, void* _v3, uintptr_t _v4, uintptr_t _v5, uintptr_t _v6, uintptr_t _v7) {
uintptr_t _v8;
_v8 = 0;
bool _v9 = (bool)((uintptr_t)_v8 < (uintptr_t)_v6);
while (_v9) {
uintptr_t _v10;
_v10 = 0;
bool _v11 = (bool)((uintptr_t)_v10 < (uintptr_t)_v7);
while (_v11) {
uintptr_t _v12 = (uintptr_t)((uintptr_t)_v1 + (uintptr_t)_v8);
uintptr_t _v13 = (uintptr_t)((uintptr_t)_v2 + (uintptr_t)_v10);
uintptr_t _v14 = (uintptr_t)((uintptr_t)_v1 + (uintptr_t)_v8);
uintptr_t _v15 = (uintptr_t)((uintptr_t)_v2 + (uintptr_t)_v10);
void* _v16 = (void*)&(((T__7*)_v0)[_v14][_v15]);
unsigned _v17 = *(unsigned*)_v16;
uintptr_t _v18 = (uintptr_t)((uintptr_t)_v4 + (uintptr_t)_v8);
uintptr_t _v19 = (uintptr_t)((uintptr_t)_v5 + (uintptr_t)_v10);
void* _v20 = (void*)&(((T__7*)_v3)[_v18][_v19]);
unsigned _v21 = *(unsigned*)_v20;
unsigned _v22 = (unsigned)((unsigned)_v17 - (unsigned)_v21);
void* _v23 = (void*)&(((T__7*)_v0)[_v12][_v13]);
*(unsigned*)_v23=_v22;
uintptr_t _v24 = (uintptr_t)((uintptr_t)_v10 + (uintptr_t)1);
_v10 = _v24;
bool _v25 = (bool)((uintptr_t)_v10 < (uintptr_t)_v7);
_v11 = _v25;
}
uintptr_t _v26 = (uintptr_t)((uintptr_t)_v8 + (uintptr_t)1);
_v8 = _v26;
bool _v27 = (bool)((uintptr_t)_v8 < (uintptr_t)_v6);
_v9 = _v27;
}
}

void strassen(void* _v0, uintptr_t _v1, uintptr_t _v2, void* _v3, uintptr_t _v4, uintptr_t _v5, void* _v6, uintptr_t _v7, uintptr_t _v8, void* _v9, uintptr_t _v10, uintptr_t _v11, uintptr_t _v12) {
bool _v13 = _v12 == 0;
if (_v13) {
void* _v14 = (void*)&(((T__7*)_v0)[_v1][_v2]);
unsigned _v15 = *(unsigned*)_v14;
void* _v16 = (void*)&(((T__7*)_v3)[_v4][_v5]);
unsigned _v17 = *(unsigned*)_v16;
unsigned _v18 = (unsigned)((unsigned)_v15 * (unsigned)_v17);
void* _v19 = (void*)&(((T__7*)_v0)[_v1][_v2]);
*(unsigned*)_v19=_v18;
} else {
uintptr_t _v20 = (uintptr_t)((uintptr_t)_v12 - (uintptr_t)1);
uintptr_t _v21 = (uintptr_t)((uintptr_t)1 << (uintptr_t)_v20);
uintptr_t _v22 = (uintptr_t)((uintptr_t)_v1 + (uintptr_t)_v21);
uintptr_t _v23 = (uintptr_t)((uintptr_t)_v2 + (uintptr_t)_v21);
uintptr_t _v24 = (uintptr_t)((uintptr_t)_v4 + (uintptr_t)_v21);
uintptr_t _v25 = (uintptr_t)((uintptr_t)_v5 + (uintptr_t)_v21);
uintptr_t _v26 = (uintptr_t)((uintptr_t)_v7 + (uintptr_t)_v21);
uintptr_t _v27 = (uintptr_t)((uintptr_t)_v8 + (uintptr_t)_v21);
uintptr_t _v28 = (uintptr_t)((uintptr_t)_v10 + (uintptr_t)_v21);
uintptr_t _v29 = (uintptr_t)((uintptr_t)_v11 + (uintptr_t)_v21);
copy_mat(_v6,_v7,_v8,_v0,_v1,_v2,_v21,_v21);
add_mat(_v6,_v7,_v8,_v0,_v22,_v23,_v21,_v21);
copy_mat(_v9,_v28,_v29,_v3,_v4,_v5,_v21,_v21);
add_mat(_v9,_v28,_v29,_v3,_v24,_v25,_v21,_v21);
uintptr_t _v30 = (uintptr_t)((uintptr_t)_v12 - (uintptr_t)1);
strassen(_v6,_v7,_v8,_v9,_v28,_v29,_v6,_v7,_v27,_v6,_v26,_v8,_v30);
copy_mat(_v6,_v7,_v27,_v0,_v22,_v2,_v21,_v21);
add_mat(_v6,_v7,_v27,_v0,_v22,_v23,_v21,_v21);
uintptr_t _v31 = (uintptr_t)((uintptr_t)_v12 - (uintptr_t)1);
strassen(_v6,_v7,_v27,_v3,_v4,_v5,_v6,_v26,_v8,_v6,_v26,_v27,_v31);
copy_mat(_v9,_v28,_v29,_v3,_v4,_v25,_v21,_v21);
sub_mat(_v9,_v28,_v29,_v3,_v24,_v25,_v21,_v21);
copy_mat(_v6,_v26,_v8,_v0,_v1,_v2,_v21,_v21);
uintptr_t _v32 = (uintptr_t)((uintptr_t)_v12 - (uintptr_t)1);
strassen(_v6,_v26,_v8,_v9,_v28,_v29,_v6,_v26,_v27,_v9,_v10,_v11,_v32);
copy_mat(_v9,_v28,_v29,_v3,_v24,_v5,_v21,_v21);
sub_mat(_v9,_v28,_v29,_v3,_v4,_v5,_v21,_v21);
copy_mat(_v6,_v26,_v27,_v0,_v22,_v23,_v21,_v21);
uintptr_t _v33 = (uintptr_t)((uintptr_t)_v12 - (uintptr_t)1);
strassen(_v6,_v26,_v27,_v9,_v28,_v29,_v9,_v10,_v11,_v9,_v10,_v29,_v33);
copy_mat(_v9,_v10,_v11,_v0,_v1,_v2,_v21,_v21);
add_mat(_v9,_v10,_v11,_v0,_v1,_v23,_v21,_v21);
uintptr_t _v34 = (uintptr_t)((uintptr_t)_v12 - (uintptr_t)1);
strassen(_v9,_v10,_v11,_v3,_v24,_v25,_v9,_v10,_v29,_v9,_v28,_v11,_v34);
copy_mat(_v9,_v10,_v29,_v0,_v22,_v2,_v21,_v21);
sub_mat(_v9,_v10,_v29,_v0,_v1,_v2,_v21,_v21);
copy_mat(_v9,_v28,_v29,_v3,_v4,_v5,_v21,_v21);
add_mat(_v9,_v28,_v29,_v3,_v4,_v25,_v21,_v21);
uintptr_t _v35 = (uintptr_t)((uintptr_t)_v12 - (uintptr_t)1);
strassen(_v9,_v10,_v29,_v9,_v28,_v29,_v9,_v28,_v11,_v0,_v1,_v2,_v35);
copy_mat(_v9,_v28,_v11,_v0,_v1,_v23,_v21,_v21);
sub_mat(_v9,_v28,_v11,_v0,_v22,_v23,_v21,_v21);
copy_mat(_v9,_v28,_v29,_v3,_v24,_v5,_v21,_v21);
add_mat(_v9,_v28,_v29,_v3,_v24,_v25,_v21,_v21);
uintptr_t _v36 = (uintptr_t)((uintptr_t)_v12 - (uintptr_t)1);
strassen(_v9,_v28,_v11,_v9,_v28,_v29,_v0,_v1,_v2,_v0,_v1,_v23,_v36);
add_mat(_v9,_v28,_v11,_v6,_v7,_v8,_v21,_v21);
add_mat(_v9,_v28,_v11,_v6,_v26,_v27,_v21,_v21);
sub_mat(_v9,_v28,_v11,_v9,_v10,_v11,_v21,_v21);
copy_mat(_v0,_v1,_v2,_v9,_v28,_v11,_v21,_v21);
add_mat(_v9,_v10,_v11,_v6,_v26,_v8,_v21,_v21);
copy_mat(_v0,_v1,_v23,_v9,_v10,_v11,_v21,_v21);
add_mat(_v6,_v26,_v27,_v6,_v7,_v27,_v21,_v21);
copy_mat(_v0,_v22,_v2,_v6,_v26,_v27,_v21,_v21);
add_mat(_v9,_v10,_v29,_v6,_v7,_v8,_v21,_v21);
sub_mat(_v9,_v10,_v29,_v6,_v7,_v27,_v21,_v21);
add_mat(_v9,_v10,_v29,_v6,_v26,_v8,_v21,_v21);
copy_mat(_v0,_v22,_v23,_v9,_v10,_v29,_v21,_v21);
}
}

void strassen_mul(void* _v0, void* _v1) {
uintptr_t _v2 = (uintptr_t)((uintptr_t)1 << (uintptr_t)2);
void* _v3 = new_mat();
void* _v4 = new_mat();
strassen(_v0,0,0,_v1,0,0,_v3,0,0,_v4,0,0,2);
del_mat(_v3);
del_mat(_v4);
}

