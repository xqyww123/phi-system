#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

void qsort(void* v0, int v1) {
bool v2 = (bool)((uint)v1 <= (uint)1);
if (v2) {
return ;
} {
int v3 = (int)((int)v1 - (int)1);
int* v4 = (int*)v0 + (uint)v3;
int v5 = *(int*)v4;
int v6;
v6 = 0;
int v7;
v7 = 0;
bool v8 = (bool)((uint)v7 < (uint)v1);
while (v8) {
int* v9 = (int*)v0 + (uint)v7;
int v10 = *(int*)v9;
bool v11 = (bool)((uint)v10 <= (uint)v5);
if (v11) {
int* v12 = (int*)v0 + (uint)v7;
int* v13 = (int*)v0 + (uint)v6;
int v14 = *(int*)v13;
*(int*)v12=v14;
int* v15 = (int*)v0 + (uint)v6;
*(int*)v15=v10;
int v16 = (int)((int)v6 + (int)1);
v6 = v16;
} {
}
int v17 = (int)((int)v7 + (int)1);
v7 = v17;
bool v18 = (bool)((uint)v7 < (uint)v1);
v8 = v18;
}
int v19 = (int)((int)v6 - (int)1);
qsort(v0,v19);
int* v20 = (int*)v0 + (uint)v6;
int v21 = (int)((int)v1 - (int)v6);
qsort(v20,v21);
return ;
}
}

