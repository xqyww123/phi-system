#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct {int data; void* nxt; } T2;

void* prepend_llist(void* v0, int v1) {
void* v2 = calloc(1, sizeof(T2));
void* v3 = (void*)&((*(T2*)v2).nxt);
*(void**)v3=v0;
void* v4 = (void*)&((*(T2*)v2).data);
*(int*)v4=v1;
return v2;
}

