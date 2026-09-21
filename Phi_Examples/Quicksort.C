#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void quicksort(void* _v0, unsigned _v1) {
bool _v2 = (bool)((unsigned)_v1 <= (unsigned)1);
if (_v2) {
return ;
} else {
unsigned _v3 = (unsigned)((unsigned)_v1 - (unsigned)1);
unsigned* _v4 = (unsigned*)_v0 + (unsigned)_v3;
unsigned _v5 = *(unsigned*)_v4;
unsigned _v6;
_v6 = 0;
unsigned _v7;
_v7 = 0;
bool _v8 = (bool)((unsigned)_v7 < (unsigned)_v1);
while (_v8) {
unsigned* _v9 = (unsigned*)_v0 + (unsigned)_v7;
unsigned _v10 = *(unsigned*)_v9;
bool _v11 = (bool)((unsigned)_v10 <= (unsigned)_v5);
if (_v11) {
unsigned* _v12 = (unsigned*)_v0 + (unsigned)_v7;
unsigned* _v13 = (unsigned*)_v0 + (unsigned)_v6;
unsigned _v14 = *(unsigned*)_v13;
*(unsigned*)_v12=_v14;
unsigned* _v15 = (unsigned*)_v0 + (unsigned)_v6;
*(unsigned*)_v15=_v10;
unsigned _v16 = (unsigned)((unsigned)_v6 + (unsigned)1);
_v6 = _v16;
} else {
}
unsigned _v17 = (unsigned)((unsigned)_v7 + (unsigned)1);
_v7 = _v17;
bool _v18 = (bool)((unsigned)_v7 < (unsigned)_v1);
_v8 = _v18;
}
unsigned _v19 = (unsigned)((unsigned)_v6 - (unsigned)1);
quicksort(_v0,_v19);
unsigned* _v20 = (unsigned*)_v0 + (unsigned)_v6;
unsigned _v21 = (unsigned)((unsigned)_v1 - (unsigned)_v6);
quicksort(_v20,_v21);
return ;
}
}

