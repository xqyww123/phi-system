#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

uintptr_t calc_hash(uintptr_t _v0, uintptr_t _v1) {
uintptr_t _v2 = (uintptr_t)((uintptr_t)_v0 % (uintptr_t)_v1);
return _v2;
}

typedef struct {int cap; void* data; int len; } T__2;

typedef struct {uintptr_t k; uintptr_t v; } T__3;

void insert_bucket(void* _v0, uintptr_t _v1, uintptr_t _v2) {
bool _v3;
_v3 = false;
void* _v4 = (void*)&((*(T__2*)_v0).len);
int _v5 = *(int*)_v4;
int _v6;
_v6 = 0;
bool _v7 = _v6 < _v5;
while (_v7) {
void* _v8 = (void*)&((*(T__2*)_v0).data);
void* _v9 = *(void**)_v8;
void* _v10 = (void*)&(((T__3*)_v9)[_v6]);
T__3 _v11 = *(T__3*)_v10;
uintptr_t _v12 = _v11.k;
bool _v13 = _v12 == _v1;
if (_v13) {
T__3 _v14 = {_v1,_v2};
void* _v15 = (void*)&((*(T__2*)_v0).data);
void* _v16 = *(void**)_v15;
void* _v17 = (void*)&(((T__3*)_v16)[_v6]);
*(T__3*)_v17=_v14;
_v3 = true;
} else {
}
int _v18 = _v6 + 1;
_v6 = _v18;
bool _v19 = _v6 < _v5;
_v7 = _v19;
}
bool _v20 = !_v3;
if (_v20) {
T__3 _v21 = {_v1,_v2};
void* _v22 = (void*)&((*(T__2*)_v0).len);
int _v23 = *(int*)_v22;
void* _v24 = (void*)&((*(T__2*)_v0).cap);
int _v25 = *(int*)_v24;
bool _v26 = _v25 == _v23;
if (_v26) {
int _v27 = _v25 * 2;
bool _v28 = _v27 < 1;
int _v29;
if (_v28) {
_v29 = 1;
} else {
_v29 = _v27;
}
void* _v30 = calloc(_v29, sizeof(T__3));
void* _v31 = (void*)&((*(T__2*)_v0).data);
void* _v32 = *(void**)_v31;
memcpy(_v30, _v32, _v23 * sizeof(T__3));
void* _v33 = (void*)&((*(T__2*)_v0).data);
void* _v34 = *(void**)_v33;
free(_v34);
void* _v35 = (void*)&((*(T__2*)_v0).data);
*(void**)_v35=_v30;
void* _v36 = (void*)&((*(T__2*)_v0).len);
int _v37 = *(int*)_v36;
int _v38 = _v37 + 1;
void* _v39 = (void*)&((*(T__2*)_v0).len);
*(int*)_v39=_v38;
void* _v40 = (void*)&((*(T__2*)_v0).cap);
*(int*)_v40=_v29;
void* _v41 = (void*)&(((T__3*)_v30)[_v23]);
*(T__3*)_v41=_v21;
} else {
void* _v42 = (void*)&((*(T__2*)_v0).data);
void* _v43 = *(void**)_v42;
void* _v44 = (void*)&(((T__3*)_v43)[_v23]);
*(T__3*)_v44=_v21;
int _v45 = _v23 + 1;
void* _v46 = (void*)&((*(T__2*)_v0).len);
*(int*)_v46=_v45;
}
} else {
}
}

typedef struct {uintptr_t N; void* tabl; } T__4;

void update_hash(void* _v0, uintptr_t _v1, uintptr_t _v2) {
void* _v3 = (void*)&((*(T__4*)_v0).tabl);
void* _v4 = *(void**)_v3;
void* _v5 = (void*)&((*(T__4*)_v0).N);
uintptr_t _v6 = *(uintptr_t*)_v5;
uintptr_t _v7 = calc_hash(_v1,_v6);
void* _v8 = (void*)&(((void**)_v4)[_v7]);
void* _v9 = *(void**)_v8;
insert_bucket(_v9,_v1,_v2);
}

bool bucket_has_key(void* _v0, uintptr_t _v1) {
bool _v2;
_v2 = false;
void* _v3 = (void*)&((*(T__2*)_v0).len);
int _v4 = *(int*)_v3;
int _v5;
_v5 = 0;
bool _v6 = _v5 < _v4;
while (_v6) {
void* _v7 = (void*)&((*(T__2*)_v0).data);
void* _v8 = *(void**)_v7;
void* _v9 = (void*)&(((T__3*)_v8)[_v5]);
T__3 _v10 = *(T__3*)_v9;
uintptr_t _v11 = _v10.k;
bool _v12 = _v11 == _v1;
bool _v13 = _v2 || _v12;
_v2 = _v13;
int _v14 = _v5 + 1;
_v5 = _v14;
bool _v15 = _v5 < _v4;
_v6 = _v15;
}
return _v2;
}

bool hash_has_key(void* _v0, uintptr_t _v1) {
void* _v2 = (void*)&((*(T__4*)_v0).tabl);
void* _v3 = *(void**)_v2;
void* _v4 = (void*)&((*(T__4*)_v0).N);
uintptr_t _v5 = *(uintptr_t*)_v4;
uintptr_t _v6 = (uintptr_t)((uintptr_t)_v1 % (uintptr_t)_v5);
void* _v7 = (void*)&(((void**)_v3)[_v6]);
void* _v8 = *(void**)_v7;
bool _v9 = bucket_has_key(_v8,_v1);
return _v9;
}

uintptr_t lookup_bucket(void* _v0, uintptr_t _v1) {
uintptr_t _v2;
void* _v3 = (void*)&((*(T__2*)_v0).len);
int _v4 = *(int*)_v3;
int _v5;
_v5 = 0;
bool _v6 = _v5 < _v4;
while (_v6) {
void* _v7 = (void*)&((*(T__2*)_v0).data);
void* _v8 = *(void**)_v7;
void* _v9 = (void*)&(((T__3*)_v8)[_v5]);
T__3 _v10 = *(T__3*)_v9;
uintptr_t _v11 = _v10.k;
bool _v12 = _v11 == _v1;
if (_v12) {
uintptr_t _v13 = _v10.v;
_v2 = _v13;
} else {
}
int _v14 = _v5 + 1;
_v5 = _v14;
bool _v15 = _v5 < _v4;
_v6 = _v15;
}
return _v2;
}

uintptr_t hash_lookup(void* _v0, uintptr_t _v1) {
void* _v2 = (void*)&((*(T__4*)_v0).tabl);
void* _v3 = *(void**)_v2;
void* _v4 = (void*)&((*(T__4*)_v0).N);
uintptr_t _v5 = *(uintptr_t*)_v4;
uintptr_t _v6 = (uintptr_t)((uintptr_t)_v1 % (uintptr_t)_v5);
void* _v7 = (void*)&(((void**)_v3)[_v6]);
void* _v8 = *(void**)_v7;
uintptr_t _v9 = lookup_bucket(_v8,_v1);
return _v9;
}

void* new_hash(uintptr_t _v0) {
void* _v1 = calloc(_v0, sizeof(void*));
uintptr_t _v2;
_v2 = 0;
bool _v3 = (bool)((uintptr_t)_v2 < (uintptr_t)_v0);
while (_v3) {
void* _v4 = calloc(1, sizeof(T__2));
void* _v5 = calloc(0, sizeof(T__3));
void* _v6 = (void*)&((*(T__2*)_v4).data);
*(void**)_v6=_v5;
void* _v7 = (void*)&(((void**)_v1)[_v2]);
*(void**)_v7=_v4;
uintptr_t _v8 = (uintptr_t)((uintptr_t)_v2 + (uintptr_t)1);
_v2 = _v8;
bool _v9 = (bool)((uintptr_t)_v2 < (uintptr_t)_v0);
_v3 = _v9;
}
void* _v10 = calloc(1, sizeof(T__4));
void* _v11 = (void*)&((*(T__4*)_v10).N);
*(uintptr_t*)_v11=_v0;
void* _v12 = (void*)&((*(T__4*)_v10).tabl);
*(void**)_v12=_v1;
return _v10;
}

void del_hash(void* _v0) {
void* _v1 = (void*)&((*(T__4*)_v0).N);
uintptr_t _v2 = *(uintptr_t*)_v1;
void* _v3 = (void*)&((*(T__4*)_v0).tabl);
void* _v4 = *(void**)_v3;
uintptr_t _v5;
_v5 = 0;
bool _v6 = (bool)((uintptr_t)_v5 < (uintptr_t)_v2);
while (_v6) {
void* _v7 = (void*)&(((void**)_v4)[_v5]);
void* _v8 = *(void**)_v7;
void* _v9 = (void*)&((*(T__2*)_v8).data);
void* _v10 = *(void**)_v9;
free(_v10);
free(_v8);
uintptr_t _v11 = (uintptr_t)((uintptr_t)_v5 + (uintptr_t)1);
_v5 = _v11;
bool _v12 = (bool)((uintptr_t)_v5 < (uintptr_t)_v2);
_v6 = _v12;
}
free(_v4);
free(_v0);
}

void* entries_of_hash(void* _v0) {
void* _v1 = calloc(1, sizeof(T__2));
void* _v2 = calloc(0, sizeof(T__3));
void* _v3 = (void*)&((*(T__2*)_v1).data);
*(void**)_v3=_v2;
void* _v4 = (void*)&((*(T__4*)_v0).N);
uintptr_t _v5 = *(uintptr_t*)_v4;
void* _v6 = (void*)&((*(T__4*)_v0).tabl);
void* _v7 = *(void**)_v6;
uintptr_t _v8;
_v8 = 0;
bool _v9 = (bool)((uintptr_t)_v8 < (uintptr_t)_v5);
while (_v9) {
void* _v10 = (void*)&(((void**)_v7)[_v8]);
void* _v11 = *(void**)_v10;
void* _v12 = (void*)&((*(T__2*)_v11).len);
int _v13 = *(int*)_v12;
int _v14;
_v14 = 0;
bool _v15 = _v14 < _v13;
while (_v15) {
void* _v16 = (void*)&((*(T__2*)_v11).data);
void* _v17 = *(void**)_v16;
void* _v18 = (void*)&(((T__3*)_v17)[_v14]);
T__3 _v19 = *(T__3*)_v18;
void* _v20 = (void*)&((*(T__2*)_v1).len);
int _v21 = *(int*)_v20;
void* _v22 = (void*)&((*(T__2*)_v1).cap);
int _v23 = *(int*)_v22;
bool _v24 = _v23 == _v21;
if (_v24) {
int _v25 = _v23 * 2;
bool _v26 = _v25 < 1;
int _v27;
if (_v26) {
_v27 = 1;
} else {
_v27 = _v25;
}
void* _v28 = calloc(_v27, sizeof(T__3));
void* _v29 = (void*)&((*(T__2*)_v1).data);
void* _v30 = *(void**)_v29;
memcpy(_v28, _v30, _v21 * sizeof(T__3));
void* _v31 = (void*)&((*(T__2*)_v1).data);
void* _v32 = *(void**)_v31;
free(_v32);
void* _v33 = (void*)&((*(T__2*)_v1).data);
*(void**)_v33=_v28;
void* _v34 = (void*)&((*(T__2*)_v1).len);
int _v35 = *(int*)_v34;
int _v36 = _v35 + 1;
void* _v37 = (void*)&((*(T__2*)_v1).len);
*(int*)_v37=_v36;
void* _v38 = (void*)&((*(T__2*)_v1).cap);
*(int*)_v38=_v27;
void* _v39 = (void*)&(((T__3*)_v28)[_v21]);
*(T__3*)_v39=_v19;
} else {
void* _v40 = (void*)&((*(T__2*)_v1).data);
void* _v41 = *(void**)_v40;
void* _v42 = (void*)&(((T__3*)_v41)[_v21]);
*(T__3*)_v42=_v19;
int _v43 = _v21 + 1;
void* _v44 = (void*)&((*(T__2*)_v1).len);
*(int*)_v44=_v43;
}
int _v45 = _v14 + 1;
_v14 = _v45;
bool _v46 = _v14 < _v13;
_v15 = _v46;
}
uintptr_t _v47 = (uintptr_t)((uintptr_t)_v8 + (uintptr_t)1);
_v8 = _v47;
bool _v48 = (bool)((uintptr_t)_v8 < (uintptr_t)_v5);
_v9 = _v48;
}
return _v1;
}

void* rehash(void* _v0, uintptr_t _v1) {
void* _v2 = entries_of_hash(_v0);
del_hash(_v0);
void* _v3 = new_hash(_v1);
void* _v4 = (void*)&((*(T__2*)_v2).len);
int _v5 = *(int*)_v4;
int _v6;
_v6 = 0;
bool _v7 = _v6 < _v5;
while (_v7) {
void* _v8 = (void*)&((*(T__2*)_v2).data);
void* _v9 = *(void**)_v8;
void* _v10 = (void*)&(((T__3*)_v9)[_v6]);
T__3 _v11 = *(T__3*)_v10;
uintptr_t _v12 = _v11.k;
uintptr_t _v13 = _v11.v;
update_hash(_v3,_v12,_v13);
int _v14 = _v6 + 1;
_v6 = _v14;
bool _v15 = _v6 < _v5;
_v7 = _v15;
}
void* _v16 = (void*)&((*(T__2*)_v2).data);
void* _v17 = *(void**)_v16;
free(_v17);
free(_v2);
return _v3;
}

