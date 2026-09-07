#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

int binary_search_array(void* v0, int v1, int v2, int v3) {
void* v4 = (void*)&(((int*)v0)[v1]);
int v5 = *(int*)v4;
bool v6 = (bool)((uint)v5 <= (uint)v3);
if (v6) {
return v1;
} else {
int v7;
v7 = v2;
int v8;
v8 = v1;
int v9 = (int)((int)v8 + (int)1);
bool v10 = (bool)((uint)v9 < (uint)v7);
while (v10) {
int v11 = (int)((int)v7 - (int)v8);
int v12 = (int)((uint)v11 / (uint)2);
int v13 = (int)((int)v8 + (int)v12);
void* v14 = (void*)&(((int*)v0)[v13]);
int v15 = *(int*)v14;
bool v16 = (bool)((uint)v15 <= (uint)v3);
if (v16) {
v7 = v13;
} else {
v8 = v13;
}
int v17 = (int)((int)v8 + (int)1);
bool v18 = (bool)((uint)v17 < (uint)v7);
v10 = v18;
}
return v7;
}
}

