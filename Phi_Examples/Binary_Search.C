#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

unsigned binary_search_array(void* _v0, unsigned _v1, unsigned _v2, unsigned _v3) {
void* _v4 = (void*)&(((unsigned*)_v0)[_v1]);
unsigned _v5 = *(unsigned*)_v4;
bool _v6 = (bool)((unsigned)_v5 <= (unsigned)_v3);
if (_v6) {
return _v1;
} else {
unsigned _v7;
_v7 = _v2;
unsigned _v8;
_v8 = _v1;
unsigned _v9 = (unsigned)((unsigned)_v8 + (unsigned)1);
bool _v10 = (bool)((unsigned)_v9 < (unsigned)_v7);
while (_v10) {
unsigned _v11 = (unsigned)((unsigned)_v7 - (unsigned)_v8);
unsigned _v12 = (unsigned)((unsigned)_v11 / (unsigned)2);
unsigned _v13 = (unsigned)((unsigned)_v8 + (unsigned)_v12);
void* _v14 = (void*)&(((unsigned*)_v0)[_v13]);
unsigned _v15 = *(unsigned*)_v14;
bool _v16 = (bool)((unsigned)_v15 <= (unsigned)_v3);
if (_v16) {
_v7 = _v13;
} else {
_v8 = _v13;
}
unsigned _v17 = (unsigned)((unsigned)_v8 + (unsigned)1);
bool _v18 = (bool)((unsigned)_v17 < (unsigned)_v7);
_v10 = _v18;
}
return _v7;
}
}

