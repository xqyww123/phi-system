
typedef int T;

struct DynArr {
  T *data;
  int len;
  int cap;
};

T get_dynarr (struct DynArr *addr, int i) {
  return addr -> data[i];
}

void set_dynarr (struct DynArr *addr, int i, T v) {
  addr -> data[i] = v;
}



