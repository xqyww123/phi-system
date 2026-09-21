#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void* init() {
return NULL;
}

bool is_empty(void* _v0) {
bool _v1 = _v0 == NULL;
return _v1;
}

typedef struct {unsigned data; void* nxt; } T__2;

void* prepend_llist(void* _v0, unsigned _v1) {
void* _v2 = calloc(1, sizeof(T__2));
void* _v3 = (void*)&((*(T__2*)_v2).nxt);
*(void**)_v3=_v0;
void* _v4 = (void*)&((*(T__2*)_v2).data);
*(unsigned*)_v4=_v1;
return _v2;
}

void* pop_llist(void* _v0) {
bool _v1 = _v0 == NULL;
if (_v1) {
return _v0;
} else {
}
void* _v2 = (void*)&((*(T__2*)_v0).nxt);
void* _v3 = *(void**)_v2;
free(_v0);
return _v3;
}

unsigned nth_llist(void* _v0, unsigned _v1) {
bool _v2 = _v1 == 0;
unsigned _v3;
if (_v2) {
void* _v4 = (void*)&((*(T__2*)_v0).data);
unsigned _v5 = *(unsigned*)_v4;
_v3 = _v5;
} else {
void* _v6 = (void*)&((*(T__2*)_v0).nxt);
void* _v7 = *(void**)_v6;
unsigned _v8 = (unsigned)((unsigned)_v1 - (unsigned)1);
unsigned _v9 = nth_llist(_v7,_v8);
_v3 = _v9;
}
return _v3;
}

unsigned hd_llist(void* _v0) {
unsigned _v1 = nth_llist(_v0,0);
return _v1;
}

void update_nth_llist(void* _v0, unsigned _v1, unsigned _v2) {
bool _v3 = _v1 == 0;
if (_v3) {
void* _v4 = (void*)&((*(T__2*)_v0).data);
*(unsigned*)_v4=_v2;
} else {
void* _v5 = (void*)&((*(T__2*)_v0).nxt);
void* _v6 = *(void**)_v5;
unsigned _v7 = (unsigned)((unsigned)_v1 - (unsigned)1);
update_nth_llist(_v6,_v7,_v2);
}
}

unsigned length_of(void* _v0) {
bool _v1 = _v0 == NULL;
if (_v1) {
return 0;
} else {
void* _v2 = (void*)&((*(T__2*)_v0).nxt);
void* _v3 = *(void**)_v2;
void* _v4 = (void*)&((*(T__2*)_v0).nxt);
void* _v5 = *(void**)_v4;
unsigned _v6 = length_of(_v5);
unsigned _v7 = (unsigned)((unsigned)_v6 + (unsigned)1);
return _v7;
}
}

void* reverse_aux(void* _v0, void* _v1) {
bool _v2 = _v0 == NULL;
void* _v3;
if (_v2) {
_v3 = _v1;
} else {
void* _v4 = (void*)&((*(T__2*)_v0).nxt);
void* _v5 = *(void**)_v4;
void* _v6 = (void*)&((*(T__2*)_v0).nxt);
*(void**)_v6=_v1;
void* _v7 = reverse_aux(_v5,_v0);
_v3 = _v7;
}
return _v3;
}

void* reverse(void* _v0) {
void* _v1 = reverse_aux(_v0,NULL);
return _v1;
}

