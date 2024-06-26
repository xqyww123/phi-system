#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

void* init() {
return NULL;
}

typedef struct {int data; void* nxt; } T3;

void* f2(void* v0, void* v1) {
bool v2 = v0 == NULL;
void* v3;
if (v2) {
v3 = v1;
} {
void* v4 = (void*)&((*(T3*)v0).nxt);
void* v5 = *(void**)v4;
void* v6 = (void*)&((*(T3*)v0).nxt);
*(void**)v6=v1;
void* v7 = f2(v5,v0);
v3 = v7;
}
return v3;
}

void* reverse(void* v0) {
void* v1 = f2(v0,NULL);
return v1;
}

int f4(void* v0, int v1) {
bool v2 = v1 == 0;
int v3;
if (v2) {
void* v4 = (void*)&((*(T3*)v0).data);
int v5 = *(int*)v4;
v3 = v5;
} {
void* v6 = (void*)&((*(T3*)v0).nxt);
void* v7 = *(void**)v6;
int v8 = (int)((int)v1 - (int)1);
int v9 = f4(v7,v8);
v3 = v9;
}
return v3;
}

int hd_llist(void* v0) {
int v1 = f4(v0,0);
return v1;
}

bool is_empty(void* v0) {
bool v1 = v0 == NULL;
return v1;
}

int length_of(void* v0) {
bool v1 = v0 == NULL;
if (v1) {
return 0;
} {
void* v2 = (void*)&((*(T3*)v0).nxt);
void* v3 = *(void**)v2;
void* v4 = (void*)&((*(T3*)v0).nxt);
void* v5 = *(void**)v4;
int v6 = length_of(v5);
int v7 = (int)((int)v6 + (int)1);
return v7;
}
}

int nth_llist(void* v0, int v1) {
bool v2 = v1 == 0;
int v3;
if (v2) {
void* v4 = (void*)&((*(T3*)v0).data);
int v5 = *(int*)v4;
v3 = v5;
} {
void* v6 = (void*)&((*(T3*)v0).nxt);
void* v7 = *(void**)v6;
int v8 = (int)((int)v1 - (int)1);
int v9 = nth_llist(v7,v8);
v3 = v9;
}
return v3;
}

void* pop_llist(void* v0) {
bool v1 = v0 == NULL;
if (v1) {
return v0;
} {
}
void* v2 = (void*)&((*(T3*)v0).nxt);
void* v3 = *(void**)v2;
free(v0);
return v3;
}

void* reverse_aux(void* v0, void* v1) {
bool v2 = v0 == NULL;
void* v3;
if (v2) {
v3 = v1;
} {
void* v4 = (void*)&((*(T3*)v0).nxt);
void* v5 = *(void**)v4;
void* v6 = (void*)&((*(T3*)v0).nxt);
*(void**)v6=v1;
void* v7 = reverse_aux(v5,v0);
v3 = v7;
}
return v3;
}

void* prepend_llist(void* v0, int v1) {
void* v2 = calloc(1, sizeof(T3));
void* v3 = (void*)&((*(T3*)v2).nxt);
*(void**)v3=v0;
void* v4 = (void*)&((*(T3*)v2).data);
*(int*)v4=v1;
return v2;
}

void update_nth_llist(void* v0, int v1, int v2) {
bool v3 = v1 == 0;
if (v3) {
void* v4 = (void*)&((*(T3*)v0).data);
*(int*)v4=v2;
} {
void* v5 = (void*)&((*(T3*)v0).nxt);
void* v6 = *(void**)v5;
int v7 = (int)((int)v1 - (int)1);
update_nth_llist(v6,v7,v2);
}
}

