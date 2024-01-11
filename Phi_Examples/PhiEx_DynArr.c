#include <stdlib.h>
#include <string.h>

typedef int T;

struct DynArr {
  T *data;
  size_t len;
  size_t cap;
};

T get_dynarr (struct DynArr *addr, size_t i) {
  return addr -> data[i];
}

void set_dynarr (struct DynArr *addr, size_t i, T v) {
  addr -> data[i] = v;
}

size_t max (size_t x, size_t y) {
  if (x < y) return y; else return x;
}

void push_dynarr (struct DynArr *addr, T v) {
  size_t len = addr -> len;
  size_t cap = addr -> cap;
  if (cap == len) {
    size_t cap2 = max (cap * 2, 1);
    T* data2 = calloc(sizeof(T), cap2);
    memcpy (data2, addr -> data, len);
    free (addr -> data);
    addr -> data = data2;
    (addr -> len) ++;
    data2[len] = v;
  } else {
    addr -> data[len] = v;
    (addr -> len) ++;
  }
}

T pop_dynarr (struct DynArr *addr) {
  size_t len = addr -> len - 1;
  size_t half_cap = addr -> cap / 2;
  T ret = addr -> data[len];
  addr -> len = len;
  if (len <= half_cap) {
      T* data2 = calloc(sizeof(T), half_cap);
      memcpy (data2, addr -> data, len);
      free (addr -> data);
      addr -> data = data2;
      addr -> cap = half_cap;
  }
  return ret;
}

