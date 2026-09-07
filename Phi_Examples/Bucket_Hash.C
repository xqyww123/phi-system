#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {int cap; void* data; int len; } T14;

typedef struct {intptr_t k; intptr_t v; } T15;

typedef struct {intptr_t N; void* tabl; } T16;

void* f13(void* v0) {
void* v1 = calloc(1, sizeof(T14));
void* v2 = calloc(0, sizeof(T15));
void* v3 = (void*)&((*(T14*)v1).data);
*(void**)v3=v2;
void* v4 = (void*)&((*(T16*)v0).N);
intptr_t v5 = *(intptr_t*)v4;
void* v6 = (void*)&((*(T16*)v0).tabl);
void* v7 = *(void**)v6;
intptr_t v8;
v8 = 0;
bool v9 = (bool)((uintptr_t)v8 < (uintptr_t)v5);
while (v9) {
void* v10 = (void*)&(((void**)v7)[v8]);
void* v11 = *(void**)v10;
void* v12 = (void*)&((*(T14*)v11).len);
int v13 = *(int*)v12;
int v14;
v14 = 0;
int v15 = v14 < v13;
while (v15) {
void* v16 = (void*)&((*(T14*)v11).data);
void* v17 = *(void**)v16;
void* v18 = (void*)&(((T15*)v17)[v14]);
T15 v19 = *(T15*)v18;
void* v20 = (void*)&((*(T14*)v1).len);
int v21 = *(int*)v20;
void* v22 = (void*)&((*(T14*)v1).cap);
int v23 = *(int*)v22;
bool v24 = v23 == v21;
if (v24) {
int v25 = v23 * 2;
int v26 = v25 < 1;
int v27;
if (v26) {
v27 = 1;
} else {
v27 = v25;
}
void* v28 = calloc(v27, sizeof(T15));
void* v29 = (void*)&((*(T14*)v1).data);
void* v30 = *(void**)v29;
memcpy(v28, v30, v21 * sizeof(T15));
void* v31 = (void*)&((*(T14*)v1).data);
void* v32 = *(void**)v31;
free(v32);
void* v33 = (void*)&((*(T14*)v1).data);
*(void**)v33=v28;
void* v34 = (void*)&((*(T14*)v1).len);
int v35 = *(int*)v34;
int v36 = v35 + 1;
void* v37 = (void*)&((*(T14*)v1).len);
*(int*)v37=v36;
void* v38 = (void*)&((*(T14*)v1).cap);
*(int*)v38=v27;
void* v39 = (void*)&(((T15*)v28)[v21]);
*(T15*)v39=v19;
} else {
void* v40 = (void*)&((*(T14*)v1).data);
void* v41 = *(void**)v40;
void* v42 = (void*)&(((T15*)v41)[v21]);
*(T15*)v42=v19;
int v43 = v21 + 1;
void* v44 = (void*)&((*(T14*)v1).len);
*(int*)v44=v43;
}
int v45 = v14 + 1;
v14 = v45;
int v46 = v14 < v13;
v15 = v46;
}
intptr_t v47 = (intptr_t)((intptr_t)v8 + (intptr_t)1);
v8 = v47;
bool v48 = (bool)((uintptr_t)v8 < (uintptr_t)v5);
v9 = v48;
}
return v1;
}

void f17(void* v0) {
void* v1 = (void*)&((*(T16*)v0).N);
intptr_t v2 = *(intptr_t*)v1;
void* v3 = (void*)&((*(T16*)v0).tabl);
void* v4 = *(void**)v3;
intptr_t v5;
v5 = 0;
bool v6 = (bool)((uintptr_t)v5 < (uintptr_t)v2);
while (v6) {
void* v7 = (void*)&(((void**)v4)[v5]);
void* v8 = *(void**)v7;
void* v9 = (void*)&((*(T14*)v8).data);
void* v10 = *(void**)v9;
free(v10);
free(v8);
intptr_t v11 = (intptr_t)((intptr_t)v5 + (intptr_t)1);
v5 = v11;
bool v12 = (bool)((uintptr_t)v5 < (uintptr_t)v2);
v6 = v12;
}
free(v4);
free(v0);
}

void* f18(intptr_t v0) {
void* v1 = calloc(v0, sizeof(void*));
intptr_t v2;
v2 = 0;
bool v3 = (bool)((uintptr_t)v2 < (uintptr_t)v0);
while (v3) {
void* v4 = calloc(1, sizeof(T14));
void* v5 = calloc(0, sizeof(T15));
void* v6 = (void*)&((*(T14*)v4).data);
*(void**)v6=v5;
void* v7 = (void*)&(((void**)v1)[v2]);
*(void**)v7=v4;
intptr_t v8 = (intptr_t)((intptr_t)v2 + (intptr_t)1);
v2 = v8;
bool v9 = (bool)((uintptr_t)v2 < (uintptr_t)v0);
v3 = v9;
}
void* v10 = calloc(1, sizeof(T16));
void* v11 = (void*)&((*(T16*)v10).N);
*(intptr_t*)v11=v0;
void* v12 = (void*)&((*(T16*)v10).tabl);
*(void**)v12=v1;
return v10;
}

intptr_t f20(intptr_t v0, intptr_t v1) {
intptr_t v2 = (intptr_t)((uintptr_t)v0 % (uintptr_t)v1);
return v2;
}

void f21(void* v0, intptr_t v1, intptr_t v2) {
bool v3;
v3 = false;
void* v4 = (void*)&((*(T14*)v0).len);
int v5 = *(int*)v4;
int v6;
v6 = 0;
int v7 = v6 < v5;
while (v7) {
void* v8 = (void*)&((*(T14*)v0).data);
void* v9 = *(void**)v8;
void* v10 = (void*)&(((T15*)v9)[v6]);
T15 v11 = *(T15*)v10;
intptr_t v12 = v11.k;
bool v13 = v12 == v1;
if (v13) {
T15 v14 = {v1,v2};
void* v15 = (void*)&((*(T14*)v0).data);
void* v16 = *(void**)v15;
void* v17 = (void*)&(((T15*)v16)[v6]);
*(T15*)v17=v14;
v3 = true;
} else {
}
int v18 = v6 + 1;
v6 = v18;
int v19 = v6 < v5;
v7 = v19;
}
bool v20 = !v3;
if (v20) {
T15 v21 = {v1,v2};
void* v22 = (void*)&((*(T14*)v0).len);
int v23 = *(int*)v22;
void* v24 = (void*)&((*(T14*)v0).cap);
int v25 = *(int*)v24;
bool v26 = v25 == v23;
if (v26) {
int v27 = v25 * 2;
int v28 = v27 < 1;
int v29;
if (v28) {
v29 = 1;
} else {
v29 = v27;
}
void* v30 = calloc(v29, sizeof(T15));
void* v31 = (void*)&((*(T14*)v0).data);
void* v32 = *(void**)v31;
memcpy(v30, v32, v23 * sizeof(T15));
void* v33 = (void*)&((*(T14*)v0).data);
void* v34 = *(void**)v33;
free(v34);
void* v35 = (void*)&((*(T14*)v0).data);
*(void**)v35=v30;
void* v36 = (void*)&((*(T14*)v0).len);
int v37 = *(int*)v36;
int v38 = v37 + 1;
void* v39 = (void*)&((*(T14*)v0).len);
*(int*)v39=v38;
void* v40 = (void*)&((*(T14*)v0).cap);
*(int*)v40=v29;
void* v41 = (void*)&(((T15*)v30)[v23]);
*(T15*)v41=v21;
} else {
void* v42 = (void*)&((*(T14*)v0).data);
void* v43 = *(void**)v42;
void* v44 = (void*)&(((T15*)v43)[v23]);
*(T15*)v44=v21;
int v45 = v23 + 1;
void* v46 = (void*)&((*(T14*)v0).len);
*(int*)v46=v45;
}
} else {
}
}

void f19(void* v0, intptr_t v1, intptr_t v2) {
void* v3 = (void*)&((*(T16*)v0).tabl);
void* v4 = *(void**)v3;
void* v5 = (void*)&((*(T16*)v0).N);
intptr_t v6 = *(intptr_t*)v5;
intptr_t v7 = f20(v1,v6);
void* v8 = (void*)&(((void**)v4)[v7]);
void* v9 = *(void**)v8;
f21(v9,v1,v2);
}

void* rehash(void* v0, intptr_t v1) {
void* v2 = f13(v0);
f17(v0);
void* v3 = f18(v1);
void* v4 = (void*)&((*(T14*)v2).len);
int v5 = *(int*)v4;
int v6;
v6 = 0;
int v7 = v6 < v5;
while (v7) {
void* v8 = (void*)&((*(T14*)v2).data);
void* v9 = *(void**)v8;
void* v10 = (void*)&(((T15*)v9)[v6]);
T15 v11 = *(T15*)v10;
intptr_t v12 = v11.k;
intptr_t v13 = v11.v;
f19(v3,v12,v13);
int v14 = v6 + 1;
v6 = v14;
int v15 = v6 < v5;
v7 = v15;
}
void* v16 = (void*)&((*(T14*)v2).data);
void* v17 = *(void**)v16;
free(v17);
free(v2);
return v3;
}

void del_hash(void* v0) {
void* v1 = (void*)&((*(T16*)v0).N);
intptr_t v2 = *(intptr_t*)v1;
void* v3 = (void*)&((*(T16*)v0).tabl);
void* v4 = *(void**)v3;
intptr_t v5;
v5 = 0;
bool v6 = (bool)((uintptr_t)v5 < (uintptr_t)v2);
while (v6) {
void* v7 = (void*)&(((void**)v4)[v5]);
void* v8 = *(void**)v7;
void* v9 = (void*)&((*(T14*)v8).data);
void* v10 = *(void**)v9;
free(v10);
free(v8);
intptr_t v11 = (intptr_t)((intptr_t)v5 + (intptr_t)1);
v5 = v11;
bool v12 = (bool)((uintptr_t)v5 < (uintptr_t)v2);
v6 = v12;
}
free(v4);
free(v0);
}

void* new_hash(intptr_t v0) {
void* v1 = calloc(v0, sizeof(void*));
intptr_t v2;
v2 = 0;
bool v3 = (bool)((uintptr_t)v2 < (uintptr_t)v0);
while (v3) {
void* v4 = calloc(1, sizeof(T14));
void* v5 = calloc(0, sizeof(T15));
void* v6 = (void*)&((*(T14*)v4).data);
*(void**)v6=v5;
void* v7 = (void*)&(((void**)v1)[v2]);
*(void**)v7=v4;
intptr_t v8 = (intptr_t)((intptr_t)v2 + (intptr_t)1);
v2 = v8;
bool v9 = (bool)((uintptr_t)v2 < (uintptr_t)v0);
v3 = v9;
}
void* v10 = calloc(1, sizeof(T16));
void* v11 = (void*)&((*(T16*)v10).N);
*(intptr_t*)v11=v0;
void* v12 = (void*)&((*(T16*)v10).tabl);
*(void**)v12=v1;
return v10;
}

intptr_t calc_hash(intptr_t v0, intptr_t v1) {
intptr_t v2 = (intptr_t)((uintptr_t)v0 % (uintptr_t)v1);
return v2;
}

intptr_t f22(void* v0, intptr_t v1) {
intptr_t v2;
void* v3 = (void*)&((*(T14*)v0).len);
int v4 = *(int*)v3;
int v5;
v5 = 0;
int v6 = v5 < v4;
while (v6) {
void* v7 = (void*)&((*(T14*)v0).data);
void* v8 = *(void**)v7;
void* v9 = (void*)&(((T15*)v8)[v5]);
T15 v10 = *(T15*)v9;
intptr_t v11 = v10.k;
bool v12 = v11 == v1;
if (v12) {
intptr_t v13 = v10.v;
v2 = v13;
} else {
}
int v14 = v5 + 1;
v5 = v14;
int v15 = v5 < v4;
v6 = v15;
}
return v2;
}

intptr_t hash_lookup(void* v0, intptr_t v1) {
void* v2 = (void*)&((*(T16*)v0).tabl);
void* v3 = *(void**)v2;
void* v4 = (void*)&((*(T16*)v0).N);
intptr_t v5 = *(intptr_t*)v4;
intptr_t v6 = (intptr_t)((uintptr_t)v1 % (uintptr_t)v5);
void* v7 = (void*)&(((void**)v3)[v6]);
void* v8 = *(void**)v7;
intptr_t v9 = f22(v8,v1);
return v9;
}

intptr_t f23(intptr_t v0, intptr_t v1) {
intptr_t v2 = (intptr_t)((uintptr_t)v0 % (uintptr_t)v1);
return v2;
}

void f24(void* v0, intptr_t v1, intptr_t v2) {
bool v3;
v3 = false;
void* v4 = (void*)&((*(T14*)v0).len);
int v5 = *(int*)v4;
int v6;
v6 = 0;
int v7 = v6 < v5;
while (v7) {
void* v8 = (void*)&((*(T14*)v0).data);
void* v9 = *(void**)v8;
void* v10 = (void*)&(((T15*)v9)[v6]);
T15 v11 = *(T15*)v10;
intptr_t v12 = v11.k;
bool v13 = v12 == v1;
if (v13) {
T15 v14 = {v1,v2};
void* v15 = (void*)&((*(T14*)v0).data);
void* v16 = *(void**)v15;
void* v17 = (void*)&(((T15*)v16)[v6]);
*(T15*)v17=v14;
v3 = true;
} else {
}
int v18 = v6 + 1;
v6 = v18;
int v19 = v6 < v5;
v7 = v19;
}
bool v20 = !v3;
if (v20) {
T15 v21 = {v1,v2};
void* v22 = (void*)&((*(T14*)v0).len);
int v23 = *(int*)v22;
void* v24 = (void*)&((*(T14*)v0).cap);
int v25 = *(int*)v24;
bool v26 = v25 == v23;
if (v26) {
int v27 = v25 * 2;
int v28 = v27 < 1;
int v29;
if (v28) {
v29 = 1;
} else {
v29 = v27;
}
void* v30 = calloc(v29, sizeof(T15));
void* v31 = (void*)&((*(T14*)v0).data);
void* v32 = *(void**)v31;
memcpy(v30, v32, v23 * sizeof(T15));
void* v33 = (void*)&((*(T14*)v0).data);
void* v34 = *(void**)v33;
free(v34);
void* v35 = (void*)&((*(T14*)v0).data);
*(void**)v35=v30;
void* v36 = (void*)&((*(T14*)v0).len);
int v37 = *(int*)v36;
int v38 = v37 + 1;
void* v39 = (void*)&((*(T14*)v0).len);
*(int*)v39=v38;
void* v40 = (void*)&((*(T14*)v0).cap);
*(int*)v40=v29;
void* v41 = (void*)&(((T15*)v30)[v23]);
*(T15*)v41=v21;
} else {
void* v42 = (void*)&((*(T14*)v0).data);
void* v43 = *(void**)v42;
void* v44 = (void*)&(((T15*)v43)[v23]);
*(T15*)v44=v21;
int v45 = v23 + 1;
void* v46 = (void*)&((*(T14*)v0).len);
*(int*)v46=v45;
}
} else {
}
}

void update_hash(void* v0, intptr_t v1, intptr_t v2) {
void* v3 = (void*)&((*(T16*)v0).tabl);
void* v4 = *(void**)v3;
void* v5 = (void*)&((*(T16*)v0).N);
intptr_t v6 = *(intptr_t*)v5;
intptr_t v7 = f23(v1,v6);
void* v8 = (void*)&(((void**)v4)[v7]);
void* v9 = *(void**)v8;
f24(v9,v1,v2);
}

bool f25(void* v0, intptr_t v1) {
bool v2;
v2 = false;
void* v3 = (void*)&((*(T14*)v0).len);
int v4 = *(int*)v3;
int v5;
v5 = 0;
int v6 = v5 < v4;
while (v6) {
void* v7 = (void*)&((*(T14*)v0).data);
void* v8 = *(void**)v7;
void* v9 = (void*)&(((T15*)v8)[v5]);
T15 v10 = *(T15*)v9;
intptr_t v11 = v10.k;
bool v12 = v11 == v1;
bool v13 = v2 || v12;
v2 = v13;
int v14 = v5 + 1;
v5 = v14;
int v15 = v5 < v4;
v6 = v15;
}
return v2;
}

bool hash_has_key(void* v0, intptr_t v1) {
void* v2 = (void*)&((*(T16*)v0).tabl);
void* v3 = *(void**)v2;
void* v4 = (void*)&((*(T16*)v0).N);
intptr_t v5 = *(intptr_t*)v4;
intptr_t v6 = (intptr_t)((uintptr_t)v1 % (uintptr_t)v5);
void* v7 = (void*)&(((void**)v3)[v6]);
void* v8 = *(void**)v7;
bool v9 = f25(v8,v1);
return v9;
}

void insert_bucket(void* v0, intptr_t v1, intptr_t v2) {
bool v3;
v3 = false;
void* v4 = (void*)&((*(T14*)v0).len);
int v5 = *(int*)v4;
int v6;
v6 = 0;
int v7 = v6 < v5;
while (v7) {
void* v8 = (void*)&((*(T14*)v0).data);
void* v9 = *(void**)v8;
void* v10 = (void*)&(((T15*)v9)[v6]);
T15 v11 = *(T15*)v10;
intptr_t v12 = v11.k;
bool v13 = v12 == v1;
if (v13) {
T15 v14 = {v1,v2};
void* v15 = (void*)&((*(T14*)v0).data);
void* v16 = *(void**)v15;
void* v17 = (void*)&(((T15*)v16)[v6]);
*(T15*)v17=v14;
v3 = true;
} else {
}
int v18 = v6 + 1;
v6 = v18;
int v19 = v6 < v5;
v7 = v19;
}
bool v20 = !v3;
if (v20) {
T15 v21 = {v1,v2};
void* v22 = (void*)&((*(T14*)v0).len);
int v23 = *(int*)v22;
void* v24 = (void*)&((*(T14*)v0).cap);
int v25 = *(int*)v24;
bool v26 = v25 == v23;
if (v26) {
int v27 = v25 * 2;
int v28 = v27 < 1;
int v29;
if (v28) {
v29 = 1;
} else {
v29 = v27;
}
void* v30 = calloc(v29, sizeof(T15));
void* v31 = (void*)&((*(T14*)v0).data);
void* v32 = *(void**)v31;
memcpy(v30, v32, v23 * sizeof(T15));
void* v33 = (void*)&((*(T14*)v0).data);
void* v34 = *(void**)v33;
free(v34);
void* v35 = (void*)&((*(T14*)v0).data);
*(void**)v35=v30;
void* v36 = (void*)&((*(T14*)v0).len);
int v37 = *(int*)v36;
int v38 = v37 + 1;
void* v39 = (void*)&((*(T14*)v0).len);
*(int*)v39=v38;
void* v40 = (void*)&((*(T14*)v0).cap);
*(int*)v40=v29;
void* v41 = (void*)&(((T15*)v30)[v23]);
*(T15*)v41=v21;
} else {
void* v42 = (void*)&((*(T14*)v0).data);
void* v43 = *(void**)v42;
void* v44 = (void*)&(((T15*)v43)[v23]);
*(T15*)v44=v21;
int v45 = v23 + 1;
void* v46 = (void*)&((*(T14*)v0).len);
*(int*)v46=v45;
}
} else {
}
}

intptr_t lookup_bucket(void* v0, intptr_t v1) {
intptr_t v2;
void* v3 = (void*)&((*(T14*)v0).len);
int v4 = *(int*)v3;
int v5;
v5 = 0;
int v6 = v5 < v4;
while (v6) {
void* v7 = (void*)&((*(T14*)v0).data);
void* v8 = *(void**)v7;
void* v9 = (void*)&(((T15*)v8)[v5]);
T15 v10 = *(T15*)v9;
intptr_t v11 = v10.k;
bool v12 = v11 == v1;
if (v12) {
intptr_t v13 = v10.v;
v2 = v13;
} else {
}
int v14 = v5 + 1;
v5 = v14;
int v15 = v5 < v4;
v6 = v15;
}
return v2;
}

bool bucket_has_key(void* v0, intptr_t v1) {
bool v2;
v2 = false;
void* v3 = (void*)&((*(T14*)v0).len);
int v4 = *(int*)v3;
int v5;
v5 = 0;
int v6 = v5 < v4;
while (v6) {
void* v7 = (void*)&((*(T14*)v0).data);
void* v8 = *(void**)v7;
void* v9 = (void*)&(((T15*)v8)[v5]);
T15 v10 = *(T15*)v9;
intptr_t v11 = v10.k;
bool v12 = v11 == v1;
bool v13 = v2 || v12;
v2 = v13;
int v14 = v5 + 1;
v5 = v14;
int v15 = v5 < v4;
v6 = v15;
}
return v2;
}

void* entries_of_hash(void* v0) {
void* v1 = calloc(1, sizeof(T14));
void* v2 = calloc(0, sizeof(T15));
void* v3 = (void*)&((*(T14*)v1).data);
*(void**)v3=v2;
void* v4 = (void*)&((*(T16*)v0).N);
intptr_t v5 = *(intptr_t*)v4;
void* v6 = (void*)&((*(T16*)v0).tabl);
void* v7 = *(void**)v6;
intptr_t v8;
v8 = 0;
bool v9 = (bool)((uintptr_t)v8 < (uintptr_t)v5);
while (v9) {
void* v10 = (void*)&(((void**)v7)[v8]);
void* v11 = *(void**)v10;
void* v12 = (void*)&((*(T14*)v11).len);
int v13 = *(int*)v12;
int v14;
v14 = 0;
int v15 = v14 < v13;
while (v15) {
void* v16 = (void*)&((*(T14*)v11).data);
void* v17 = *(void**)v16;
void* v18 = (void*)&(((T15*)v17)[v14]);
T15 v19 = *(T15*)v18;
void* v20 = (void*)&((*(T14*)v1).len);
int v21 = *(int*)v20;
void* v22 = (void*)&((*(T14*)v1).cap);
int v23 = *(int*)v22;
bool v24 = v23 == v21;
if (v24) {
int v25 = v23 * 2;
int v26 = v25 < 1;
int v27;
if (v26) {
v27 = 1;
} else {
v27 = v25;
}
void* v28 = calloc(v27, sizeof(T15));
void* v29 = (void*)&((*(T14*)v1).data);
void* v30 = *(void**)v29;
memcpy(v28, v30, v21 * sizeof(T15));
void* v31 = (void*)&((*(T14*)v1).data);
void* v32 = *(void**)v31;
free(v32);
void* v33 = (void*)&((*(T14*)v1).data);
*(void**)v33=v28;
void* v34 = (void*)&((*(T14*)v1).len);
int v35 = *(int*)v34;
int v36 = v35 + 1;
void* v37 = (void*)&((*(T14*)v1).len);
*(int*)v37=v36;
void* v38 = (void*)&((*(T14*)v1).cap);
*(int*)v38=v27;
void* v39 = (void*)&(((T15*)v28)[v21]);
*(T15*)v39=v19;
} else {
void* v40 = (void*)&((*(T14*)v1).data);
void* v41 = *(void**)v40;
void* v42 = (void*)&(((T15*)v41)[v21]);
*(T15*)v42=v19;
int v43 = v21 + 1;
void* v44 = (void*)&((*(T14*)v1).len);
*(int*)v44=v43;
}
int v45 = v14 + 1;
v14 = v45;
int v46 = v14 < v13;
v15 = v46;
}
intptr_t v47 = (intptr_t)((intptr_t)v8 + (intptr_t)1);
v8 = v47;
bool v48 = (bool)((uintptr_t)v8 < (uintptr_t)v5);
v9 = v48;
}
return v1;
}

