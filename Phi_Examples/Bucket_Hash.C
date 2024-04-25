#include <stdbool.h>

typedef int TY;

struct KV_Entry {
  int k;
  TY v;
};

#include "DynArr_for_Hash.c"

struct Hash {
  struct DynArr** tabl;
  int N;
};

int calc_hash (int k, int N) {
  return k % N;
}

void insert_bucket (struct DynArr* addr, int k, TY v)
{
  bool met = false;
  for (int i=0; i < len_dynarr(addr); ++i) {
    struct KV_Entry kv = get_dynarr(addr, i);
    if (kv.k = k) {
      set_dynarr (addr, i, {k: k, v: v});
      met = true;
    }
    if (!met) {
      push_dynarr (addr, {k: k, v: v});
    }
  }
}

void update_hash(struct Hash* addr, int k, TY v)
{
  struct DynArr** tabl = addr -> tabl;
  int N = addr -> N;
  int hash = calc_hash (k, N);
  insert_bucket (tabl[hash], k, v);
}

bool bucket_has_key (struct DynArr* addr, int k)
{
  bool met = false;
  for (int i = 0; i < len_dynarr(addr); ++i) {
    met = met || (get_dynarr(addr, i).k == k);
  }
  return met;
}

bool hash_has_key (struct Hash* addr, int k)
{
  struct DynArr** tabl = addr -> tabl;
  int N = addr -> N;
  int hash = calc_hash (k, N);
  return bucket_has_key (tabl[hash], k);
}

TY lookup_bucket (struct DynArr* addr, int k)
{
  TY ret;
  for (int i = 0; i < len_dynarr(addr); ++i) {
    struct KV_Entry entry = get_dynarr(addr, i);
    if (entry.k == k) {
      ret = entry.v;
    }
  }
  return ret;
}

TY hash_lookup (struct Hash* addr, int k)
{
  struct DynArr** tabl = addr -> tabl;
  int N = addr -> N;
  int hash = calc_hash (k, N);
  TY ret = lookup_bucket (tabl[hash], k);
  return ret;
}

struct Hash* new_hash (int N)
{
  struct DynArr** tabl_addr = (struct DynArr**) calloc(sizeof(struct DynArr*), N);
  for (int i = 0; i < N; ++i) {
    struct DynArr* dynarr = new_dynarr();
    tabl_addr[i] = dynarr;
  }

  struct Hash* ret = (struct Hash*) calloc(sizeof(struct Hash), 1);
  ret -> N = N;
  ret -> tabl = tabl_addr;
  return ret;
}

void del_hash (struct Hash* addr)
{
  int N = addr -> N;
  struct DynArr** tabl = addr -> tabl;
  for (int i = 0; i < N; ++i) {
    del_dynarr (tabl[i]);
  }
  free (tabl);
  free (addr);
}

struct DynArr* entries_of_hash (struct Hash* addr)
{
  struct DynArr* dynarr = new_dynarr ();
  int N = addr -> N;
  struct DynArr** tabl = addr -> tabl;
  for (int i=0; i < N; ++i) {
    concat_dynarr (dynarr, tabl[i]);
  }
  return dynarr;
}

struct Hash* rehash (struct Hash* addr, int N)
{
  struct DynArr* dynarr = entries_of_hash (addr);
  del_hash(addr);
  struct Hash* ret = new_hash(N);
  for (int i = 0; i < len_dynarr(dynarr); ++i) {
    struct KV_Entry entry = get_dynarr (dynarr, i);
    update_hash (ret, entry.k, entry.v);
  }
  del_dynarr (dynarr);
  return ret;
}

