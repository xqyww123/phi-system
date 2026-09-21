#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {unsigned k; unsigned v; } T__7;

typedef struct {T__7 data; void* left; void* right; } T__8;

unsigned lookup_bintree(void* _v0, unsigned _v1) {
void* _v2 = (void*)&((*(T__8*)_v0).data.k);
unsigned _v3 = *(unsigned*)_v2;
bool _v4 = _v3 == _v1;
if (_v4) {
void* _v5 = (void*)&((*(T__8*)_v0).data.v);
unsigned _v6 = *(unsigned*)_v5;
return _v6;
} else {
bool _v7 = (bool)((int)_v1 < (int)_v3);
if (_v7) {
void* _v8 = (void*)&((*(T__8*)_v0).left);
void* _v9 = *(void**)_v8;
unsigned _v10 = lookup_bintree(_v9,_v1);
return _v10;
} else {
void* _v11 = (void*)&((*(T__8*)_v0).right);
void* _v12 = *(void**)_v11;
unsigned _v13 = lookup_bintree(_v12,_v1);
return _v13;
}
}
}

bool defined_bintree(void* _v0, unsigned _v1) {
bool _v2 = _v0 == NULL;
if (_v2) {
return false;
} else {
void* _v3 = (void*)&((*(T__8*)_v0).data.k);
unsigned _v4 = *(unsigned*)_v3;
bool _v5 = _v4 == _v1;
if (_v5) {
return true;
} else {
bool _v6 = (bool)((int)_v1 < (int)_v4);
if (_v6) {
void* _v7 = (void*)&((*(T__8*)_v0).left);
void* _v8 = *(void**)_v7;
bool _v9 = defined_bintree(_v8,_v1);
return _v9;
} else {
void* _v10 = (void*)&((*(T__8*)_v0).right);
void* _v11 = *(void**)_v10;
bool _v12 = defined_bintree(_v11,_v1);
return _v12;
}
}
}
}

void* insert_bintree(void* _v0, unsigned _v1, unsigned _v2) {
bool _v3 = _v0 == NULL;
if (_v3) {
void* _v4 = calloc(1, sizeof(T__8));
void* _v5 = (void*)&((*(T__8*)_v4).data.k);
*(unsigned*)_v5=_v1;
void* _v6 = (void*)&((*(T__8*)_v4).data.v);
*(unsigned*)_v6=_v2;
return _v4;
} else {
void* _v7 = (void*)&((*(T__8*)_v0).data.k);
unsigned _v8 = *(unsigned*)_v7;
bool _v9 = _v8 == _v1;
if (_v9) {
void* _v10 = (void*)&((*(T__8*)_v0).data.v);
*(unsigned*)_v10=_v2;
return _v0;
} else {
bool _v11 = (bool)((int)_v1 < (int)_v8);
if (_v11) {
void* _v12 = (void*)&((*(T__8*)_v0).left);
void* _v13 = *(void**)_v12;
void* _v14 = insert_bintree(_v13,_v1,_v2);
void* _v15 = (void*)&((*(T__8*)_v0).left);
*(void**)_v15=_v14;
return _v0;
} else {
void* _v16 = (void*)&((*(T__8*)_v0).right);
void* _v17 = *(void**)_v16;
void* _v18 = insert_bintree(_v17,_v1,_v2);
void* _v19 = (void*)&((*(T__8*)_v0).right);
*(void**)_v19=_v18;
return _v0;
}
}
}
}

int Max(int _v0, int _v1) {
bool _v2 = _v0 < _v1;
int _v3;
if (_v2) {
_v3 = _v1;
} else {
_v3 = _v0;
}
return _v3;
}

typedef struct {int height; unsigned v; } T__9;

typedef struct {unsigned k; T__9 v; } T__10;

typedef struct {T__10 data; void* left; void* right; } T__11;

int height_of(void* _v0) {
bool _v1 = _v0 == NULL;
if (_v1) {
return 0;
} else {
void* _v2 = (void*)&((*(T__11*)_v0).data.v.height);
int _v3 = *(int*)_v2;
return _v3;
}
}

void* maintain_i(void* _v0) {
void* _v1 = (void*)&((*(T__11*)_v0).left);
void* _v2 = *(void**)_v1;
void* _v3 = (void*)&((*(T__11*)_v0).right);
void* _v4 = *(void**)_v3;
int _v5 = height_of(_v2);
int _v6 = height_of(_v4);
int _v7 = _v6 + 2;
bool _v8 = _v5 == _v7;
if (_v8) {
void* _v9 = (void*)&((*(T__11*)_v2).left);
void* _v10 = *(void**)_v9;
void* _v11 = (void*)&((*(T__11*)_v2).right);
void* _v12 = *(void**)_v11;
int _v13 = height_of(_v10);
int _v14 = height_of(_v12);
bool _v15 = _v14 <= _v13;
if (_v15) {
void* _v16 = (void*)&((*(T__11*)_v0).left);
*(void**)_v16=_v12;
int _v17 = Max(_v14,_v6);
int _v18 = _v17 + 1;
void* _v19 = (void*)&((*(T__11*)_v0).data.v.height);
*(int*)_v19=_v18;
void* _v20 = (void*)&((*(T__11*)_v2).right);
*(void**)_v20=_v0;
int _v21 = Max(_v13,_v18);
int _v22 = _v21 + 1;
void* _v23 = (void*)&((*(T__11*)_v2).data.v.height);
*(int*)_v23=_v22;
return _v2;
} else {
void* _v24 = (void*)&((*(T__11*)_v12).left);
void* _v25 = *(void**)_v24;
void* _v26 = (void*)&((*(T__11*)_v12).right);
void* _v27 = *(void**)_v26;
void* _v28 = (void*)&((*(T__11*)_v2).right);
*(void**)_v28=_v25;
int _v29 = height_of(_v25);
int _v30 = Max(_v13,_v29);
int _v31 = _v30 + 1;
void* _v32 = (void*)&((*(T__11*)_v2).data.v.height);
*(int*)_v32=_v31;
void* _v33 = (void*)&((*(T__11*)_v12).right);
void* _v34 = *(void**)_v33;
void* _v35 = (void*)&((*(T__11*)_v0).left);
*(void**)_v35=_v34;
int _v36 = height_of(_v27);
int _v37 = Max(_v6,_v36);
int _v38 = _v37 + 1;
void* _v39 = (void*)&((*(T__11*)_v0).data.v.height);
*(int*)_v39=_v38;
void* _v40 = (void*)&((*(T__11*)_v12).left);
*(void**)_v40=_v2;
void* _v41 = (void*)&((*(T__11*)_v12).right);
*(void**)_v41=_v0;
int _v42 = Max(_v31,_v38);
int _v43 = _v42 + 1;
void* _v44 = (void*)&((*(T__11*)_v12).data.v.height);
*(int*)_v44=_v43;
return _v12;
}
} else {
int _v45 = _v5 + 2;
bool _v46 = _v6 == _v45;
if (_v46) {
void* _v47 = (void*)&((*(T__11*)_v4).left);
void* _v48 = *(void**)_v47;
void* _v49 = (void*)&((*(T__11*)_v4).right);
void* _v50 = *(void**)_v49;
int _v51 = height_of(_v48);
int _v52 = height_of(_v50);
bool _v53 = _v51 <= _v52;
if (_v53) {
void* _v54 = (void*)&((*(T__11*)_v0).right);
*(void**)_v54=_v48;
int _v55 = Max(_v5,_v51);
int _v56 = _v55 + 1;
void* _v57 = (void*)&((*(T__11*)_v0).data.v.height);
*(int*)_v57=_v56;
void* _v58 = (void*)&((*(T__11*)_v4).left);
*(void**)_v58=_v0;
int _v59 = Max(_v56,_v52);
int _v60 = _v59 + 1;
void* _v61 = (void*)&((*(T__11*)_v4).data.v.height);
*(int*)_v61=_v60;
return _v4;
} else {
void* _v62 = (void*)&((*(T__11*)_v48).left);
void* _v63 = *(void**)_v62;
void* _v64 = (void*)&((*(T__11*)_v48).right);
void* _v65 = *(void**)_v64;
void* _v66 = (void*)&((*(T__11*)_v0).right);
*(void**)_v66=_v63;
int _v67 = height_of(_v63);
int _v68 = Max(_v5,_v67);
int _v69 = _v68 + 1;
void* _v70 = (void*)&((*(T__11*)_v0).data.v.height);
*(int*)_v70=_v69;
void* _v71 = (void*)&((*(T__11*)_v4).left);
*(void**)_v71=_v65;
int _v72 = height_of(_v65);
int _v73 = Max(_v72,_v52);
int _v74 = _v73 + 1;
void* _v75 = (void*)&((*(T__11*)_v4).data.v.height);
*(int*)_v75=_v74;
void* _v76 = (void*)&((*(T__11*)_v48).left);
*(void**)_v76=_v0;
void* _v77 = (void*)&((*(T__11*)_v48).right);
*(void**)_v77=_v4;
int _v78 = Max(_v69,_v74);
int _v79 = _v78 + 1;
void* _v80 = (void*)&((*(T__11*)_v48).data.v.height);
*(int*)_v80=_v79;
return _v48;
}
} else {
void* _v81 = (void*)&((*(T__11*)_v0).left);
void* _v82 = *(void**)_v81;
int _v83 = height_of(_v82);
void* _v84 = (void*)&((*(T__11*)_v0).right);
void* _v85 = *(void**)_v84;
int _v86 = height_of(_v85);
int _v87 = Max(_v83,_v86);
int _v88 = _v87 + 1;
void* _v89 = (void*)&((*(T__11*)_v0).data.v.height);
*(int*)_v89=_v88;
return _v0;
}
}
}

void* insert_avl_i(void* _v0, unsigned _v1, unsigned _v2) {
bool _v3 = _v0 == NULL;
if (_v3) {
void* _v4 = calloc(1, sizeof(T__11));
void* _v5 = (void*)&((*(T__11*)_v4).data.k);
*(unsigned*)_v5=_v1;
void* _v6 = (void*)&((*(T__11*)_v4).data.v.v);
*(unsigned*)_v6=_v2;
void* _v7 = (void*)&((*(T__11*)_v4).data.v.height);
*(int*)_v7=1;
return _v4;
} else {
void* _v8 = (void*)&((*(T__11*)_v0).data.k);
unsigned _v9 = *(unsigned*)_v8;
bool _v10 = _v9 == _v1;
if (_v10) {
void* _v11 = (void*)&((*(T__11*)_v0).data.v.v);
*(unsigned*)_v11=_v2;
return _v0;
} else {
bool _v12 = (bool)((int)_v1 < (int)_v9);
if (_v12) {
void* _v13 = (void*)&((*(T__11*)_v0).left);
void* _v14 = *(void**)_v13;
void* _v15 = insert_avl_i(_v14,_v1,_v2);
void* _v16 = (void*)&((*(T__11*)_v0).left);
*(void**)_v16=_v15;
void* _v17 = maintain_i(_v0);
return _v17;
} else {
void* _v18 = (void*)&((*(T__11*)_v0).right);
void* _v19 = *(void**)_v18;
void* _v20 = insert_avl_i(_v19,_v1,_v2);
void* _v21 = (void*)&((*(T__11*)_v0).right);
*(void**)_v21=_v20;
void* _v22 = maintain_i(_v0);
return _v22;
}
}
}
}

