#include <stdlib.h>
#include <string.h>

typedef int T;

struct DynArr {
  T *data;
  size_t len;
  size_t cap;
};

size_t len_dynarr(struct DynArr *addr) {
  return addr -> len;
}

T get_dynarr (struct DynArr *addr, size_t i) {
  return addr -> data[i];
}

void set_dynarr (struct DynArr *addr, size_t i, T v) {
  addr -> data[i] = v;
}

size_t max (size_t x, size_t y) {
  if (x < y) return y; else return x;
}

void push_dynarr (struct DynArr *addr, T v)
{
  size_t len = addr -> len;
  size_t cap = addr -> cap;
  if (cap == len) {
    size_t cap2 = max (cap * 2, 1);
    T* data2 = (T*) calloc(sizeof(T), cap2);
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

T pop_dynarr (struct DynArr *addr)
{
  size_t len = addr -> len - 1;
  size_t half_cap = addr -> cap / 2;
  T ret = addr -> data[len];
  addr -> len = len;
  if (len <= half_cap) {
      T* data2 = (T*) calloc(sizeof(T), half_cap);
      memcpy (data2, addr -> data, len);
      free (addr -> data);
      addr -> data = data2;
      addr -> cap = half_cap;
  }
  return ret;
}

struct DynArr* new_dynarr ()
{
  struct DynArr* ret = (struct DynArr*) calloc(sizeof(DynArr), 1);
  ret -> data = (T*) calloc(sizeof(T), 0);
  return ret;
}

void del_dynarr(struct DynArr* addr) {
  free (addr -> data);
  free (addr);
}

void concat_dynarr (struct DynArr* addr1, struct DynArr* addr2)
{
  int len = len_dynarr (addr2);
  for (int i = 0; i < len; ++i) {
    push_dynarr (addr1, get_dynarr (addr2, i));
  }
}

