#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {uintptr_t cap; void* data; uintptr_t len; } T__3;

uintptr_t len_dynarr(void* _v0) {
void* _v1 = (void*)&((*(T__3*)_v0).len);
uintptr_t _v2 = *(uintptr_t*)_v1;
return _v2;
}

uintptr_t get_dynarr(void* _v0, uintptr_t _v1) {
void* _v2 = (void*)&((*(T__3*)_v0).data);
void* _v3 = *(void**)_v2;
void* _v4 = (void*)&(((uintptr_t*)_v3)[_v1]);
uintptr_t _v5 = *(uintptr_t*)_v4;
return _v5;
}

void set_dynarr(void* _v0, uintptr_t _v1, uintptr_t _v2) {
void* _v3 = (void*)&((*(T__3*)_v0).data);
void* _v4 = *(void**)_v3;
void* _v5 = (void*)&(((uintptr_t*)_v4)[_v1]);
*(uintptr_t*)_v5=_v2;
}

uintptr_t Max(uintptr_t _v0, uintptr_t _v1) {
bool _v2 = (bool)((uintptr_t)_v0 < (uintptr_t)_v1);
uintptr_t _v3;
if (_v2) {
_v3 = _v1;
} else {
_v3 = _v0;
}
return _v3;
}

void push_dynarr(void* _v0, uintptr_t _v1) {
void* _v2 = (void*)&((*(T__3*)_v0).len);
uintptr_t _v3 = *(uintptr_t*)_v2;
void* _v4 = (void*)&((*(T__3*)_v0).cap);
uintptr_t _v5 = *(uintptr_t*)_v4;
bool _v6 = _v5 == _v3;
if (_v6) {
uintptr_t _v7 = (uintptr_t)((uintptr_t)_v5 * (uintptr_t)2);
uintptr_t _v8 = Max(_v7,1);
void* _v9 = calloc(_v8, sizeof(uintptr_t));
void* _v10 = (void*)&((*(T__3*)_v0).data);
void* _v11 = *(void**)_v10;
memcpy(_v9, _v11, _v3 * sizeof(uintptr_t));
void* _v12 = (void*)&((*(T__3*)_v0).data);
void* _v13 = *(void**)_v12;
free(_v13);
void* _v14 = (void*)&((*(T__3*)_v0).data);
*(void**)_v14=_v9;
void* _v15 = (void*)&((*(T__3*)_v0).len);
uintptr_t _v16 = *(uintptr_t*)_v15;
uintptr_t _v17 = (uintptr_t)((uintptr_t)_v16 + (uintptr_t)1);
void* _v18 = (void*)&((*(T__3*)_v0).len);
*(uintptr_t*)_v18=_v17;
void* _v19 = (void*)&((*(T__3*)_v0).cap);
*(uintptr_t*)_v19=_v8;
void* _v20 = (void*)&(((uintptr_t*)_v9)[_v3]);
*(uintptr_t*)_v20=_v1;
} else {
void* _v21 = (void*)&((*(T__3*)_v0).data);
void* _v22 = *(void**)_v21;
void* _v23 = (void*)&(((uintptr_t*)_v22)[_v3]);
*(uintptr_t*)_v23=_v1;
uintptr_t _v24 = (uintptr_t)((uintptr_t)_v3 + (uintptr_t)1);
void* _v25 = (void*)&((*(T__3*)_v0).len);
*(uintptr_t*)_v25=_v24;
}
}

void concat_dynarr(void* _v0, void* _v1) {
uintptr_t _v2 = len_dynarr(_v1);
uintptr_t _v3;
_v3 = 0;
bool _v4 = (bool)((uintptr_t)_v3 < (uintptr_t)_v2);
while (_v4) {
uintptr_t _v5 = get_dynarr(_v1,_v3);
push_dynarr(_v0,_v5);
uintptr_t _v6 = (uintptr_t)((uintptr_t)_v3 + (uintptr_t)1);
_v3 = _v6;
bool _v7 = (bool)((uintptr_t)_v3 < (uintptr_t)_v2);
_v4 = _v7;
}
}

uintptr_t pop_dynarr(void* _v0, uintptr_t _v1) {
void* _v2 = (void*)&((*(T__3*)_v0).len);
uintptr_t _v3 = *(uintptr_t*)_v2;
uintptr_t _v4 = (uintptr_t)((uintptr_t)_v3 - (uintptr_t)1);
void* _v5 = (void*)&((*(T__3*)_v0).cap);
uintptr_t _v6 = *(uintptr_t*)_v5;
uintptr_t _v7 = (uintptr_t)((uintptr_t)_v6 / (uintptr_t)2);
void* _v8 = (void*)&((*(T__3*)_v0).data);
void* _v9 = *(void**)_v8;
void* _v10 = (void*)&(((uintptr_t*)_v9)[_v4]);
uintptr_t _v11 = *(uintptr_t*)_v10;
void* _v12 = (void*)&((*(T__3*)_v0).len);
*(uintptr_t*)_v12=_v4;
bool _v13 = (bool)((uintptr_t)_v4 <= (uintptr_t)_v7);
if (_v13) {
void* _v14 = calloc(_v7, sizeof(uintptr_t));
void* _v15 = (void*)&((*(T__3*)_v0).data);
void* _v16 = *(void**)_v15;
memcpy(_v14, _v16, _v4 * sizeof(uintptr_t));
void* _v17 = (void*)&((*(T__3*)_v0).data);
void* _v18 = *(void**)_v17;
free(_v18);
void* _v19 = (void*)&((*(T__3*)_v0).data);
*(void**)_v19=_v14;
void* _v20 = (void*)&((*(T__3*)_v0).cap);
*(uintptr_t*)_v20=_v7;
} else {
}
return _v11;
}

void* new_dynarr() {
void* _v0 = calloc(1, sizeof(T__3));
void* _v1 = calloc(0, sizeof(uintptr_t));
void* _v2 = (void*)&((*(T__3*)_v0).data);
*(void**)_v2=_v1;
return _v0;
}

void del_dynarr(void* _v0) {
void* _v1 = (void*)&((*(T__3*)_v0).data);
void* _v2 = *(void**)_v1;
free(_v2);
free(_v0);
}

